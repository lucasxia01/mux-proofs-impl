#![allow(non_snake_case)]
use ark_poly::{univariate::DensePolynomial, Evaluations};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

use ark_bls12_381::Fr;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{fields::batch_inversion, FftField, One, Zero};
use ark_poly::UVPolynomial;
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PCCommitment, PolynomialCommitment};
use itertools::Itertools;
use std::ops::Mul;

pub fn lc_comms<
    F: FftField,
    E: PairingEngine<Fr = F>,
    PC: PolynomialCommitment<
        F,
        DensePolynomial<F>,
        Commitment = ark_poly_commit::marlin_pc::Commitment<E>,
    >,
>(
    coms: &[LabeledCommitment<PC::Commitment>],
    coeffs: &[F],
) -> LabeledCommitment<PC::Commitment> {
    let mut com = coms[0].commitment().comm.clone();
    for i in 1..coms.len() {
        com += (coeffs[i], &coms[i].commitment().comm);
    }
    let mut temp = ark_poly_commit::marlin_pc::Commitment::<E>::empty();
    temp.comm = com;
    LabeledCommitment::new("combination".to_string(), temp, None)
}

pub fn consecutive_sum<F: FftField>(vec: &[F]) -> Vec<F> {
    let mut xs = vec.iter();
    let vs = std::iter::successors(Some(F::zero()), |acc| xs.next().map(|n| *n + *acc)).skip(1);
    vs.collect::<Vec<F>>()
}

pub fn compute_denoms<F: FftField>(denominator: &[F], alpha: F) -> Vec<F> {
    let mut invs = denominator.iter().map(|x| *x + alpha).collect::<Vec<F>>();
    batch_inversion(&mut invs);
    invs
}

pub fn compute_terms<F: FftField>(numerator: Option<&[F]>, denominator: &[F], alpha: F) -> Vec<F> {
    let denoms = compute_denoms(denominator, alpha);
    match numerator {
        Some(nums) => denoms
            .iter()
            .zip(nums.iter())
            .map(|(denom, num)| *denom * num)
            .collect::<Vec<F>>(),
        None => denoms,
    }
}
pub fn compute_statement_polys<F: FftField>(
    fs: &[F],
    ts: &[F],
    m: usize,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (Vec<DensePolynomial<F>>, Vec<DensePolynomial<F>>) {
    let mods = (0..m).cycle();
    let fs = mods.clone().zip(fs.iter().map(|e| *e)).into_group_map();
    let ts = mods.zip(ts.iter().map(|e| *e)).into_group_map();
    let mut f_polys = vec![];
    let mut t_polys = vec![];
    for i in 0..m {
        let fi = Evaluations::from_vec_and_domain(fs[&i].clone(), V).interpolate();
        let ti = Evaluations::from_vec_and_domain(ts[&i].clone(), H).interpolate();
        f_polys.push(fi);
        t_polys.push(ti);
    }
    (f_polys, t_polys)
}

pub fn compute_round_1<F: FftField>(
    fs: &[F],
    ts: &[F],
    beta: F,
    m: usize,
) -> (Vec<F>, Vec<F>, Vec<F>) {
    let n = fs.len() / m;
    let d = ts.len() / m;
    let beta_pows = std::iter::successors(Some(F::one()), |n| Some(*n * beta))
        .take(m)
        .collect::<Vec<F>>();
    let mut f_vec = vec![F::zero(); n];
    let mut t_vec = vec![F::zero(); d];

    for i in 0..n {
        for j in 0..m {
            f_vec[i] += beta_pows[j] * fs[i * m + j];
        }
    }
    for i in 0..d {
        for j in 0..m {
            t_vec[i] += beta_pows[j] * ts[i * m + j];
        }
    }
    let counts = f_vec.iter().counts();
    let c_vec = t_vec
        .iter()
        .map(|t| F::from(counts[t] as u64))
        .collect::<Vec<F>>();
    (f_vec, t_vec, c_vec)
}

pub fn compute_round_2_polys<F: FftField>(
    f_vec: &[F],
    t_vec: &[F],
    c_vec: &[F],
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (DensePolynomial<F>, DensePolynomial<F>, DensePolynomial<F>) {
    let f = Evaluations::from_vec_and_domain(f_vec.to_vec(), V).interpolate();
    let t = Evaluations::from_vec_and_domain(t_vec.to_vec(), H).interpolate();
    let c = Evaluations::from_vec_and_domain(c_vec.to_vec(), H).interpolate();
    (f, t, c)
}

pub fn compute_round_3_polys<F: FftField>(
    f_vec: &[F],
    t_vec: &[F],
    c_vec: &[F],
    alpha: F,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    F,
) {
    let f_terms = compute_terms(None, &f_vec, alpha);
    let t_terms = compute_terms(Some(&c_vec), &t_vec, alpha);

    let sum: F = f_terms.iter().sum();

    let f_shift = sum / F::from(V.size() as u64);
    let t_shift = sum / F::from(H.size() as u64);
    let shifted_f_terms = f_terms.iter().map(|x| *x - f_shift).collect::<Vec<F>>();
    let shifted_t_terms = t_terms.iter().map(|x| *x - t_shift).collect::<Vec<F>>();
    let mut s_f_vec = consecutive_sum(&shifted_f_terms);
    let mut s_t_vec = consecutive_sum(&shifted_t_terms);

    let f_hab = Evaluations::from_vec_and_domain(f_terms, V).interpolate();
    let t_hab = Evaluations::from_vec_and_domain(t_terms, H).interpolate();
    let s_f = Evaluations::from_vec_and_domain(s_f_vec.clone(), V).interpolate();
    let s_t = Evaluations::from_vec_and_domain(s_t_vec.clone(), H).interpolate();
    s_f_vec.rotate_left(1);
    s_t_vec.rotate_left(1);
    let s_f_rot = Evaluations::from_vec_and_domain(s_f_vec, V).interpolate();
    let s_t_rot = Evaluations::from_vec_and_domain(s_t_vec, H).interpolate();
    (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum)
}

pub fn compute_round_4_polys<F: FftField>(
    f: &DensePolynomial<F>,
    t: &DensePolynomial<F>,
    c: &DensePolynomial<F>,
    f_hab: &DensePolynomial<F>,
    t_hab: &DensePolynomial<F>,
    s_f: &DensePolynomial<F>,
    s_t: &DensePolynomial<F>,
    s_f_rot: &DensePolynomial<F>,
    s_t_rot: &DensePolynomial<F>,
    sum: F,
    alpha: F,
    zeta: F,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (DensePolynomial<F>, DensePolynomial<F>) {
    let one_poly = DensePolynomial::from_coefficients_vec(vec![F::one()]);
    let alpha_poly = DensePolynomial::from_coefficients_vec(vec![alpha]);
    let s_n_poly = DensePolynomial::from_coefficients_vec(vec![sum / F::from(V.size() as u64)]);
    let s_d_poly = DensePolynomial::from_coefficients_vec(vec![sum / F::from(H.size() as u64)]);
    let zt_V_1 = &(&(f + &alpha_poly) * f_hab) - &one_poly;
    let zt_V_2 = &(s_f + f_hab) - &(s_f_rot - &s_n_poly);
    let zt_V = &zt_V_1 * (&zt_V_2.mul(zeta));
    let zt_H_1 = &(&(t + &alpha_poly) * t_hab) - c;
    let zt_H_2 = &(s_t + t_hab) - &(s_t_rot - &s_d_poly);
    let zt_H = &zt_H_1 * (&zt_H_2.mul(zeta));

    let q_V = zt_V.divide_by_vanishing_poly(V).unwrap().0;
    let q_H = zt_V.divide_by_vanishing_poly(H).unwrap().0;
    (q_V, q_H)
}

pub fn prover<F: FftField>(f_vec: &[F], t_vec: &[F], c_vec: &[F]) {
    let n = f_vec.len();
    let d = t_vec.len();
    let V = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let H = Radix2EvaluationDomain::<F>::new(d).unwrap();

    // Round 2
    let (f, t, c) = compute_round_2_polys(&f_vec, &t_vec, &c_vec, V.clone(), H.clone());
    let alpha = F::from(3 as u64);

    // Round 3
    let (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum) =
        compute_round_3_polys(&f_vec, &t_vec, &c_vec, alpha, V.clone(), H.clone());
    let zeta = F::from(5 as u64);

    // Round 4
    let (q_V, q_H) = compute_round_4_polys(
        &f,
        &t,
        &c,
        &f_hab,
        &t_hab,
        &s_f,
        &s_t,
        &s_f_rot,
        &s_t_rot,
        sum,
        alpha,
        zeta,
        V.clone(),
        H.clone(),
    );
    let z = F::from(2 as u64);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn statement_poly() {
        let fs = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
        ];
        let ts = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
        let V = Radix2EvaluationDomain::<Fr>::new(8).unwrap();
        let H = Radix2EvaluationDomain::<Fr>::new(4).unwrap();
        let (f_polys, t_polys) = compute_statement_polys(&fs, &ts, 2, V, H);
    }

    #[test]
    fn round_1() {
        let fs = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
        ];
        let ts = vec![Fr::from(1), Fr::from(2), Fr::from(3), Fr::from(4)];
        let beta = Fr::from(7 as u64);
        let (f_vec, t_vec, c_vec) = compute_round_1(&fs, &ts, beta, 2);
        assert_eq!(
            f_vec,
            vec![
                Fr::from(1 + 2 * 7),
                Fr::from(1 + 2 * 7),
                Fr::from(1 + 2 * 7),
                Fr::from(3 + 4 * 7)
            ]
        );
        assert_eq!(t_vec, vec![Fr::from(1 + 2 * 7), Fr::from(3 + 4 * 7)]);
        assert_eq!(c_vec, vec![Fr::from(3), Fr::from(1)]);
    }
}
