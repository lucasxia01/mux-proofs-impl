use ark_poly::{univariate::DensePolynomial, Evaluations, GeneralEvaluationDomain};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use blake2::Blake2s;

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::{fields::batch_inversion, One, Zero};
use ark_poly::UVPolynomial;
use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
use rand_chacha::ChaChaRng;
use std::ops::Add;
use std::ops::Mul;
use std::ops::Sub;

pub fn consecutive_sum(vec: &[Fr]) -> Vec<Fr> {
    let mut xs = vec.iter();
    let vs = std::iter::successors(Some(Fr::zero()), |acc| xs.next().map(|n| *n + *acc)).skip(1);
    vs.collect::<Vec<Fr>>()
}

pub fn compute_denoms(denominator: &[Fr], alpha: Fr) -> Vec<Fr> {
    let mut invs = denominator.iter().map(|x| *x + alpha).collect::<Vec<Fr>>();
    batch_inversion(&mut invs);
    invs
}

pub fn compute_terms(numerator: Option<&[Fr]>, denominator: &[Fr], alpha: Fr) -> Vec<Fr> {
    let denoms = compute_denoms(denominator, alpha);
    match numerator {
        Some(nums) => denoms
            .iter()
            .zip(nums.iter())
            .map(|(denom, num)| *denom * num)
            .collect::<Vec<Fr>>(),
        None => denoms,
    }
}

pub fn compute_starter_polys(
    f_vec: &[Fr],
    t_vec: &[Fr],
    c_vec: &[Fr],
) -> (
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
) {
    let n = f_vec.len();
    let d = t_vec.len();
    let V = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let H = Radix2EvaluationDomain::<Fr>::new(d).unwrap();

    let f = Evaluations::from_vec_and_domain(f_vec.to_vec(), V).interpolate();
    let t = Evaluations::from_vec_and_domain(t_vec.to_vec(), H).interpolate();
    let c = Evaluations::from_vec_and_domain(c_vec.to_vec(), H).interpolate();
    (f, t, c)
}

pub fn compute_helper_polys(
    f_vec: &[Fr],
    t_vec: &[Fr],
    c_vec: &[Fr],
    alpha: Fr,
) -> (
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    DensePolynomial<Fr>,
    Fr,
) {
    let n = f_vec.len();
    let d = t_vec.len();
    let V = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let H = Radix2EvaluationDomain::<Fr>::new(d).unwrap();

    let f_terms = compute_terms(None, &f_vec, alpha);
    let t_terms = compute_terms(Some(&c_vec), &t_vec, alpha);

    let sum: Fr = f_terms.iter().sum();

    let f_shift = sum / Fr::from(n as u64);
    let t_shift = sum / Fr::from(d as u64);
    let shifted_f_terms = f_terms.iter().map(|x| *x - f_shift).collect::<Vec<Fr>>();
    let shifted_t_terms = t_terms.iter().map(|x| *x - t_shift).collect::<Vec<Fr>>();
    let mut s_f_vec = consecutive_sum(&shifted_f_terms);
    let mut s_t_vec = consecutive_sum(&shifted_t_terms);

    let f_hab = Evaluations::from_vec_and_domain(f_terms, V).interpolate();
    let t_hab = Evaluations::from_vec_and_domain(t_terms, H).interpolate();
    let s_f = Evaluations::from_vec_and_domain(s_f_vec.clone(), V).interpolate();
    let s_t = Evaluations::from_vec_and_domain(s_t_vec.clone(), H).interpolate();
    s_f_vec.rotate_right(1);
    s_t_vec.rotate_right(1);
    let s_f_rot = Evaluations::from_vec_and_domain(s_f_vec, V).interpolate();
    let s_t_rot = Evaluations::from_vec_and_domain(s_t_vec, H).interpolate();
    (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum)
}

pub fn blah() {
    let f_vec = vec![
        Fr::from(1),
        Fr::from(1),
        Fr::from(1),
        Fr::from(1),
        Fr::from(1),
        Fr::from(2),
        Fr::from(2),
        Fr::from(2),
    ];
    let t_vec = vec![Fr::from(1), Fr::from(2)];
    let c_vec = vec![Fr::from(5), Fr::from(3)];

    let n = f_vec.len();
    let d = t_vec.len();
    let V = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let H = Radix2EvaluationDomain::<Fr>::new(d).unwrap();

    let alpha = Fr::from(3);
    let zeta = Fr::from(5);
    let one_poly = DensePolynomial::from_coefficients_vec(vec![Fr::one()]);
    let alpha_poly = DensePolynomial::from_coefficients_vec(vec![alpha]);
    let (f, t, c) = compute_starter_polys(&f_vec, &t_vec, &c_vec);
    let (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum) =
        compute_helper_polys(&f_vec, &t_vec, &c_vec, alpha);

    let s_n_poly = DensePolynomial::from_coefficients_vec(vec![sum / Fr::from(n as u64)]);
    let s_d_poly = DensePolynomial::from_coefficients_vec(vec![sum / Fr::from(d as u64)]);
    let zt_V_1 = &(&(&f + &alpha_poly) * &f_hab) - &one_poly;
    let zt_V_2 = &(&s_f + &f_hab) - &(&s_f_rot - &s_n_poly);
    let zt_V = &zt_V_1 * (&zt_V_2.mul(zeta));
    let zt_H_1 = &(&(&t + &alpha_poly) * &t_hab) - &c;
    let zt_H_2 = &(&s_t + &t_hab) - &(&s_t_rot - &s_d_poly);
    let zt_H = &zt_H_1 * (&zt_H_2.mul(zeta));

    let q_V = zt_V.divide_by_vanishing_poly(V).unwrap();
    let q_H = zt_V.divide_by_vanishing_poly(H).unwrap();
}
