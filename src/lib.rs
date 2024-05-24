// This file contains the prover, round by round

use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use ark_ff::{to_bytes, FftField, Field, UniformRand};
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial, Radix2EvaluationDomain,
    UVPolynomial,
};
use ark_poly_commit::{
    BatchLCProof, LabeledCommitment, LabeledPolynomial, LinearCombination, PCUniversalParams,
    PolynomialCommitment, QuerySet,
};
use ark_std::rand::RngCore;
use ark_std::{end_timer, ops::*, start_timer};

pub mod rng;
use rng::FiatShamirRng;
pub use rng::SimpleHashFiatShamirRng;

mod error;
pub use error::*;

// we need pick parameters
// field, group, FS, evlauation domain

// Copied from sublonk
pub fn is_pow_2(x: usize) -> bool {
    (x & (x - 1)) == 0
}

// Copied from sublonk
pub fn poly_from_evals<F: FftField>(evals: &Vec<F>) -> DensePolynomial<F> {
    let n = evals.len();
    assert!(is_pow_2(n));

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals.to_owned(), domain);
    eval_form.interpolate()
}

// Copied from sublonk
pub fn get_mult_subgroup_vanishing_poly<F: FftField>(n: usize) -> SparsePolynomial<F> {
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    domain.vanishing_polynomial()
}

pub fn compute_ith_lagrange_poly<F: FftField>(
    i: usize,
    domain: Radix2EvaluationDomain<F>,
) -> SparsePolynomial<F> {
    let omega_to_i = domain.group_gen.pow(&[i as u64]);
    let coeff_i = omega_to_i / F::from(domain.size);
    // denom is the polynomial X - omega_to_i
    let denom: DensePolynomial<F> =
        SparsePolynomial::from_coefficients_vec(vec![(0, -omega_to_i), (1, F::one())]).into();
    let numerator: DensePolynomial<F> = domain.vanishing_polynomial().into();
    return SparsePolynomial::from(numerator.div(&denom).mul(coeff_i));
}

pub fn compute_ith_lagrange_poly_eval<F: FftField>(
    i: usize,
    domain: Radix2EvaluationDomain<F>,
    evaluation_point: F,
) -> F {
    let omega_to_i = domain.group_gen.pow(&[i as u64]);
    return omega_to_i / F::from(domain.size)
        * domain.vanishing_polynomial().evaluate(&evaluation_point)
        / (evaluation_point - omega_to_i);
}

// Commits to single polynomial represented by vector of evaluations
pub fn commit_to_evals<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>>(
    committer_key: &PC::CommitterKey,
    evals: Vec<F>,
    name: &str,
) -> LabeledCommitment<PC::Commitment> {
    // call poly_from_evals on each of the list of evals
    let poly = poly_from_evals(&evals);
    // create the labeled polynomials with the corresponding names
    let labeled_polys = LabeledPolynomial::new(name.to_string(), poly, None, None);

    // let labeled_poly = LabeledPolynomial::new(name.to_string(), poly.clone(), None, None);
    let comms = PC::commit(committer_key, vec![&labeled_polys], None).unwrap();
    comms.0[0].clone() // TODO: figure out what the second tuple element, the randomness is
}

// Commits to multiple polynomials represented by vector of evaluations
pub fn multi_commit_to_evals<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>>(
    committer_key: &PC::CommitterKey,
    evals: Vec<Vec<F>>,
    names: Vec<&str>,
) -> Vec<LabeledCommitment<PC::Commitment>> {
    // call poly_from_evals on each of the list of evals
    let polys = evals.iter().map(|x| poly_from_evals(x)).collect::<Vec<_>>();
    // create the labeled polynomials with the corresponding names
    let labeled_polys = polys
        .iter()
        .enumerate()
        .map(|(i, x)| LabeledPolynomial::new(names[i].to_string(), x.clone(), None, None))
        .collect::<Vec<_>>();

    // let labeled_poly = LabeledPolynomial::new(name.to_string(), poly.clone(), None, None);
    let comms = PC::commit(committer_key, &labeled_polys, None).unwrap();
    comms.0 // TODO: figure out what the second tuple element, the randomness is
}

pub fn construct_zero_tests<F: FftField>(
    opening_challenge: F,
    t_vanishing: SparsePolynomial<F>,
    f_vanishing: SparsePolynomial<F>,
) -> Vec<LinearCombination<F>> {
    // Step 1.b Zero test
    let zero_test_c = LinearCombination::new(
        "zero_test_c".to_string(),
        vec![
            (F::one(), "c_rotated_gamma".to_string()),
            (F::one(), "c".to_string()),
            (
                t_vanishing.evaluate(&opening_challenge),
                "c_quotient".to_string(),
            ),
        ],
    );

    // Step 3.b Zero tests

    // Step 3.c Zero tests

    // Step 3.d Zero tests

    // Step 4.b Zero tests

    // Step 5.b Zero tests

    // Step 6.b Zero tests

    // Step 7.b Zero tests

    // Step 7.c Zero tests

    // Step 7.d Zero test

    return vec![zero_test_c];
}

pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

pub struct Proof<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>> {
    pc_proof: BatchLCProof<F, DensePolynomial<F>, PC>,
}

pub struct VectorLookup<
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
> {
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng>
    VectorLookup<F, PC, FS>
{
    pub const PROTOCOL_NAME: &'static [u8] = b"Vector_Lookup";

    /// Generate the one time universal SRS for the PC
    pub fn universal_setup<R: RngCore>(
        num_constraints: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let max_degree = num_constraints;
        let setup_time = start_timer!(|| {
            format!(
            "Vlookup::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup(max_degree, None, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys, which are just the PC commitment and verificaiton keys.
    pub fn index(
        srs: &UniversalSRS<F, PC>,
        size: usize,
    ) -> Result<(PC::CommitterKey, PC::VerifierKey), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        // TODO: Add check that c is in the correct mode.
        if srs.max_degree() < size {
            Err(Error::IndexTooLarge)?;
        }

        let coeff_support = []; // TODO: figure this out
                                // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1; // TODO: figure this
        let (committer_key, verifier_key) =
            PC::trim(&srs, size, supported_hiding_bound, Some(&coeff_support))
                .map_err(Error::from_pc_err)?;

        Ok((committer_key, verifier_key))
    }

    // Prove function
    // Inputs: Prover key, (vector commitment, table commitment), (vector elements, table elements)
    pub fn prove(
        committer_key: &PC::CommitterKey,
        f_comm: LabeledCommitment<PC::Commitment>,
        t_comm: LabeledCommitment<PC::Commitment>,
        f_evals: Vec<F>,
        t_evals: Vec<F>,
        coset_domain_size: usize,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        // TODO: fix this initialization to include all public inputs
        let mut fs_rng = FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
        let f_domain_size = f_evals.len();
        let t_domain_size = t_evals.len();
        let f_domain = Radix2EvaluationDomain::<F>::new(f_domain_size).unwrap();
        let t_domain = Radix2EvaluationDomain::<F>::new(t_domain_size).unwrap();
        let coset_domain = Radix2EvaluationDomain::<F>::new(coset_domain_size).unwrap();
        let one_domain = Radix2EvaluationDomain::<F>::new(1).unwrap();
        let f_generator = f_domain.group_gen;
        let t_generator = t_domain.group_gen;
        let coset_generator = coset_domain.group_gen;
        assert_eq!(f_domain_size % coset_domain_size, 0);
        assert_eq!(t_domain_size % coset_domain_size, 0);
        let f_domain_num_cosets = f_domain_size / coset_domain_size;
        let t_domain_num_cosets = t_domain_size / coset_domain_size;
        // Set up the vanishing polynomials for the two domains
        let t_vanishing: SparsePolynomial<F> =
            get_mult_subgroup_vanishing_poly(t_domain_size).into();
        let f_vanishing: SparsePolynomial<F> =
            get_mult_subgroup_vanishing_poly(f_domain_size).into();

        // Step 1: compute count polynomial c(X) that encodes the counts the frequency of each table vector in f
        let f_vecs: Vec<Vec<F>> = (0..f_domain_num_cosets)
            .map(|coset_idx| {
                (0..coset_domain_size)
                    .map(|i| f_evals[i * coset_domain_size + coset_idx])
                    .collect()
            })
            .collect();
        let t_vecs: Vec<Vec<F>> = (0..t_domain_num_cosets)
            .map(|coset_idx| {
                (0..coset_domain_size)
                    .map(|i| t_evals[i * coset_domain_size + coset_idx])
                    .collect()
            })
            .collect();
        // Count how many each vector appears in t_vecs.
        let mut f_vec_counts: HashMap<Vec<F>, u32> = HashMap::new();
        for f_vec in &f_vecs {
            *f_vec_counts.entry(f_vec.clone()).or_insert(0) += 1;
        }
        let mut t_vec_counts: HashMap<Vec<F>, u32> = HashMap::new();
        for t_vec in &t_vecs {
            *t_vec_counts.entry(t_vec.clone()).or_insert(0) += 1;
        }
        // Loop through f_vec_counts and check that each vector appears in t_vec_counts.
        for (k, v) in &f_vec_counts {
            if !t_vec_counts.contains_key(k) {
                panic!("f contains vec that is not in {:?}", k);
            }
        }
        // Step 1.a: Define c(X) over t_domain
        let mut c_evals: Vec<F> = vec![F::zero(); t_domain_size];
        for i in 0..t_domain_size {
            c_evals[i] = F::from(f_vec_counts[&t_vecs[i % t_domain_num_cosets].clone()]);
        }
        println!("Count poly in eval form: {:?}", c_evals);

        // Step 1.b: ZeroTest to should that c(\gammaX) = c(X)
        // Commit to c(X) and c(\gammaX) and the quotient polynomial c_quotient(X) = (c(X) - c(\gammaX))/t_vanishing(X)
        // rotate c_evals by gamma, which is t_domain_num_cosets
        c_evals.rotate_right(t_domain_num_cosets); // TODO: double check this, and investigate the complexity of rotate_right
        println!("Rotated c_evals: {:?}", c_evals);
        // This poly represents c(\gamma X)
        // Want to prove that c(X) - c(\gammaX) = 0
        let c = LabeledPolynomial::new("c".to_string(), poly_from_evals(&c_evals), None, None);
        let c_rotated_gamma = LabeledPolynomial::new(
            "c_rotated_gamma".to_string(),
            poly_from_evals(&c_evals),
            None,
            None,
        );
        // Get a quotient poly q(X) = (c(X) - c(\gammaX))/t_vanishing
        let c_quotient = (c.sub(c_rotated_gamma.polynomial()))
            .divide_by_vanishing_poly(t_domain)
            .unwrap()
            .0; // TODO: add an error for this
        let c_quotient = LabeledPolynomial::new("c_quotient".to_string(), c_quotient, None, None);

        let (c_comms, c_comm_rands) =
            PC::commit(committer_key, vec![&c, &c_rotated_gamma, &c_quotient], None)
                .map_err(Error::from_pc_err)?;
        let c_comm = c_comms[0].clone();
        let c_comm_rand = c_comm_rands[0].clone();
        let c_rotated_comm = c_comms[1].clone();
        let c_rotated_comm_rand = c_comm_rands[1].clone();
        let c_quotient_comm = c_comms[2].clone();
        let c_quotient_comm_rand = c_comm_rands[2].clone();

        // Step 2: Compute challenges alpha and beta
        let alpha = F::rand(&mut fs_rng);
        let beta = F::rand(&mut fs_rng);

        // Step 3: Compute position-indexing powers-of-beta polynomial I_b(X)
        // Precompute powers of beta up to coset_domain_size iteratively using the previous power of beta
        let mut beta_powers: Vec<F> = vec![F::one()];
        for i in 1..coset_domain_size {
            beta_powers.push(beta * beta_powers[i - 1]);
        }
        // Step 3.a: Compute I_b(X) for b = {f, t}.
        let mut idx_f_evals: Vec<_> = f_evals
            .iter()
            .zip(beta_powers.iter().cycle())
            .map(|(f, b)| *f * *b)
            .take(f_domain_size)
            .collect();

        let idx_f = LabeledPolynomial::new(
            "idx_f".to_string(),
            poly_from_evals(&idx_f_evals),
            None,
            None,
        );
        idx_f_evals.rotate_right(1);
        let idx_f_rotated_omega = LabeledPolynomial::new(
            "idx_f_rotated_omega".to_string(),
            poly_from_evals(&idx_f_evals),
            None,
            None,
        );
        idx_f_evals.rotate_right(f_domain_num_cosets - 1); // a total rotation of f_domain_num_cosets, which is gamma in the f_domain
        let idx_f_rotated_gamma = LabeledPolynomial::new(
            "idx_f_rotated_gamma".to_string(),
            poly_from_evals(&idx_f_evals),
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 3.b for f polynomial
        // Q(X) = (I_f(X) - 1) / (X - 1)
        let idx_f_quotient_1_dense = idx_f
            .sub(&DensePolynomial::from_coefficients_vec(vec![F::from(1u32)]))
            .divide_by_vanishing_poly(one_domain)
            .unwrap()
            .0;
        let idx_f_quotient_1 = LabeledPolynomial::new(
            "idx_f_quotient_1".to_string(),
            idx_f_quotient_1_dense,
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 3.c for f polynomial
        // Q(X) = (I_f(\gamma X) - \beta * I_f(X)) * (X - \gamma^{m-1}) / (X^m - 1), where m is coset_domain_size
        // quotient_2_binomial is (X - \gamma^{m-1})
        let quotient_2_binomial = DensePolynomial::from_coefficients_vec(vec![
            F::from(coset_domain.group_gen_inv),
            F::from(1u32),
        ]);
        let idx_f_quotient_2_dense = idx_f_rotated_gamma
            .sub(&idx_f.mul(beta))
            .mul(&quotient_2_binomial)
            .divide_by_vanishing_poly(coset_domain)
            .unwrap()
            .0;
        let idx_f_quotient_2 = LabeledPolynomial::new(
            "idx_f_quotient_2".to_string(),
            idx_f_quotient_2_dense,
            None,
            None,
        );

        // Quotient polynomial for zero test in Step 3.d for f polynomial
        // Q(X) = (I_f(X) - I_f(\omega_b X)) * (X^m - \omega_b^((d_f-1)*m)) / (X^(d_f*m) - 1)
        // quotient_3_binomial is (X^m - \omega_b^((d_f-1)*m))
        let quotient_3_binomial: DensePolynomial<F> =
            SparsePolynomial::from_coefficients_vec(vec![
                (
                    0,
                    F::from(
                        f_domain
                            .group_gen
                            .pow(&[(f_domain_size - coset_domain_size) as u64]),
                    ),
                ),
                (coset_domain_size, F::from(1u32)),
            ])
            .into();
        let idx_f_quotient_3_dense = idx_f
            .sub(idx_f_rotated_omega.polynomial())
            .mul(&quotient_3_binomial)
            .divide_by_vanishing_poly(f_domain)
            .unwrap()
            .0;
        let idx_f_quotient_3 = LabeledPolynomial::new(
            "idx_f_quotient_3".to_string(),
            idx_f_quotient_3_dense,
            None,
            None,
        );

        // Now compute all the polynomials for t
        let mut idx_t_evals: Vec<_> = t_evals
            .iter()
            .zip(beta_powers.iter().cycle())
            .map(|(t, b)| *t * *b)
            .take(t_domain_size)
            .collect();

        let idx_t = LabeledPolynomial::new(
            "idx_t".to_string(),
            poly_from_evals(&idx_t_evals),
            None,
            None,
        );
        idx_t_evals.rotate_right(1);
        let idx_t_rotated_omega = LabeledPolynomial::new(
            "idx_t_rotated_omega".to_string(),
            poly_from_evals(&idx_t_evals),
            None,
            None,
        );
        idx_t_evals.rotate_right(t_domain_num_cosets - 1); // a total rotation of t_domain_num_cosets, which is gamma in the t_domain
        let idx_t_rotated_gamma = LabeledPolynomial::new(
            "idx_t_rotated_gamma".to_string(),
            poly_from_evals(&idx_t_evals),
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 3.b for f polynomial
        // Q(X) = (I_t(X) - 1) / (X - 1)
        let idx_t_quotient_1_dense = idx_t
            .sub(&DensePolynomial::from_coefficients_vec(vec![F::from(1u32)]))
            .divide_by_vanishing_poly(one_domain)
            .unwrap()
            .0;
        let idx_t_quotient_1 = LabeledPolynomial::new(
            "idx_t_quotient_1".to_string(),
            idx_t_quotient_1_dense,
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 3.c for f polynomial
        // Q(X) = (I_t(\gamma X) - \beta * I_t(X)) * (X - \gamma^{m-1}) / (X^m - 1), where m is coset_domain_size
        // quotient_2_binomial is (X - \gamma^{m-1})
        let quotient_2_binomial = DensePolynomial::from_coefficients_vec(vec![
            F::from(coset_domain.group_gen_inv),
            F::from(1u32),
        ]);
        let idx_t_quotient_2_dense = idx_t_rotated_gamma
            .sub(&idx_t.mul(beta))
            .mul(&quotient_2_binomial)
            .divide_by_vanishing_poly(coset_domain)
            .unwrap()
            .0;
        let idx_t_quotient_2 = LabeledPolynomial::new(
            "idx_t_quotient_2".to_string(),
            idx_t_quotient_2_dense,
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 3.d for f polynomial
        // Q(X) = (I_t(X) - I_t(\omega_b X)) * (X^m - \omega_b^((d_t-1)*m)) / (X^(d_t*m) - 1)
        // quotient_3_binomial is (X^m - \omega_b^((d_t-1)*m))
        let quotient_3_binomial: DensePolynomial<F> =
            SparsePolynomial::from_coefficients_vec(vec![
                (
                    0,
                    F::from(
                        t_domain
                            .group_gen
                            .pow(&[(t_domain_size - coset_domain_size) as u64]),
                    ),
                ),
                (coset_domain_size, F::from(1u32)),
            ])
            .into();
        let idx_t_quotient_3_dense = idx_t
            .sub(idx_t_rotated_omega.polynomial())
            .mul(&quotient_3_binomial)
            .divide_by_vanishing_poly(t_domain)
            .unwrap()
            .0;
        let idx_t_quotient_3 = LabeledPolynomial::new(
            "idx_t_quotient_3".to_string(),
            idx_t_quotient_3_dense,
            None,
            None,
        );

        // Commit to the f and t indexing polynomials and the quotient polynomials
        let (idx_comms, _) = PC::commit(
            committer_key,
            vec![
                &idx_f,
                &idx_f_rotated_omega,
                &idx_f_rotated_gamma,
                &idx_f_quotient_1,
                &idx_f_quotient_2,
                &idx_f_quotient_3,
                &idx_t,
                &idx_t_rotated_omega,
                &idx_t_rotated_gamma,
                &idx_t_quotient_1,
                &idx_t_quotient_2,
                &idx_t_quotient_3,
            ],
            None,
        )
        .unwrap();

        // Step 4: Compute summation polynomial S_b(X).
        // Step 4.a: Compute S_b(X) for b = {f, t}.
        let mut s_f_evals = vec![F::zero(); f_domain_size];
        let mut s_t_evals = vec![F::zero(); f_domain_size];
        for i in 0..f_domain_num_cosets {
            let mut s_f_sum = F::zero();
            for j in 0..coset_domain_size {
                s_f_sum += f_evals[j * f_domain_num_cosets + i] * beta_powers[j];
            }
            let mut s_t_sum = F::zero();
            for j in 0..coset_domain_size {
                s_t_sum += f_evals[j * t_domain_num_cosets + i] * beta_powers[j];
            }
            for j in 0..coset_domain_size {
                s_f_evals[j * f_domain_num_cosets + i] = s_f_sum;
                s_t_evals[j * t_domain_num_cosets + i] = s_t_sum;
            }
        }
        let s_f =
            LabeledPolynomial::new("s_f".to_string(), poly_from_evals(&s_f_evals), None, None);
        s_f_evals.rotate_right(f_domain_num_cosets);
        let s_f_rotated_gamma = LabeledPolynomial::new(
            "s_f_rotated_gamma".to_string(),
            poly_from_evals(&s_f_evals),
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 4.b for f polynomial
        // Q(X) = (S_f(X) - S_f(\gamma X)) / (X^(d_f*m) - 1)
        let s_f_quotient_dense = s_f
            .sub(s_f_rotated_gamma.polynomial())
            .divide_by_vanishing_poly(f_domain)
            .unwrap()
            .0;
        let s_f_quotient =
            LabeledPolynomial::new("s_f_quotient".to_string(), s_f_quotient_dense, None, None);

        let s_t =
            LabeledPolynomial::new("s_t".to_string(), poly_from_evals(&s_t_evals), None, None);
        s_t_evals.rotate_right(t_domain_num_cosets);
        let s_t_rotated_gamma = LabeledPolynomial::new(
            "s_t_rotated_gamma".to_string(),
            poly_from_evals(&s_t_evals),
            None,
            None,
        );
        // Quotient polynomial for zero test in Step 4.b for f polynomial
        // Q(X) = (S_t(X) - S_t(\gamma X)) / (X^(d_t*m) - 1)
        let s_t_quotient_dense = s_t
            .sub(s_t_rotated_gamma.polynomial())
            .divide_by_vanishing_poly(t_domain)
            .unwrap()
            .0;
        let s_t_quotient =
            LabeledPolynomial::new("s_t_quotient".to_string(), s_t_quotient_dense, None, None);

        let (s_comms, s_comm_rands) = PC::commit(
            committer_key,
            vec![
                &s_f,
                &s_f_rotated_gamma,
                &s_f_quotient,
                &s_t,
                &s_t_rotated_gamma,
                &s_t_quotient,
            ],
            None,
        )
        .unwrap();

        // Step 5: Compute induction polynomial B_b(X), which contains partial sums

        // Step 6: Compute inverse polynomial U_b(X)

        // Step 7: Prove summations of U_0 and c * U_1

        // Construct all the zero tests
        let opening_challenge = F::rand(&mut fs_rng); // TODO: do this or u128::rand?
        let lc_s = construct_zero_tests(opening_challenge, t_vanishing, f_vanishing);
        let query_set = QuerySet::new();
        let pc_proof = PC::open_combinations(
            &committer_key,
            &lc_s,
            vec![&c, &c_rotated_gamma, &c_quotient],
            vec![&c_comm, &c_rotated_comm, &c_quotient_comm],
            &query_set,
            opening_challenge,
            vec![&c_comm_rand, &c_rotated_comm_rand, &c_quotient_comm_rand],
            None, // TODO: replace this with zk_rng
        )
        .map_err(Error::from_pc_err)?;

        return Ok(Proof { pc_proof: pc_proof });
    }
}
