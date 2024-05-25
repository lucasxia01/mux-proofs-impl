// This file contains the prover, round by round

use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use ark_ff::{batch_inversion, to_bytes, FftField, Field};
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial, Radix2EvaluationDomain,
    UVPolynomial,
};
use ark_poly_commit::{
    LabeledCommitment, LabeledPolynomial, LinearCombination, PCUniversalParams,
    PolynomialCommitment, QuerySet,
};
use ark_std::rand::RngCore;
use ark_std::{end_timer, ops::*, start_timer};

use crate::rng::FiatShamirRng;
pub use crate::rng::SimpleHashFiatShamirRng;

pub use crate::error::*;

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
    let coeff_i = omega_to_i * domain.size_inv;
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
    return omega_to_i
        * domain.size_inv
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
        vec![(F::one(), "c".to_string()), (-F::one(), "c".to_string())],
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
    c_comm: LabeledCommitment<PC::Commitment>,
    idx_f_comm: LabeledCommitment<PC::Commitment>,
    idx_t_comm: LabeledCommitment<PC::Commitment>,
    s_f_comm: LabeledCommitment<PC::Commitment>,
    s_t_comm: LabeledCommitment<PC::Commitment>,
    b_f_comm: LabeledCommitment<PC::Commitment>,
    b_t_comm: LabeledCommitment<PC::Commitment>,
    u_f_comm: LabeledCommitment<PC::Commitment>,
    u_t_comm: LabeledCommitment<PC::Commitment>,
    T_f_comm: LabeledCommitment<PC::Commitment>,
    T_t_comm: LabeledCommitment<PC::Commitment>,
    pc_proof: <PC as PolynomialCommitment<F, DensePolynomial<F>>>::BatchProof,
}

pub struct CosetLookup<
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
> {
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

impl<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng>
    CosetLookup<F, PC, FS>
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
        f_comm: &LabeledCommitment<PC::Commitment>,
        t_comm: &LabeledCommitment<PC::Commitment>,
        f_evals: Vec<F>,
        t_evals: Vec<F>,
        f: LabeledPolynomial<F, DensePolynomial<F>>,
        t: LabeledPolynomial<F, DensePolynomial<F>>,
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
        let t_vanishing: SparsePolynomial<F> = t_domain.vanishing_polynomial();
        let f_vanishing: SparsePolynomial<F> = f_domain.vanishing_polynomial();

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
        // Commit to c(X) and the quotient polynomial c_quotient(X) = (c(X) - c(\gammaX))/t_vanishing(X)
        // Want to prove that c(X) - c(\gammaX) = 0
        let c = LabeledPolynomial::new("c".to_string(), poly_from_evals(&c_evals), None, None);
        // rotate c_evals by gamma, which is t_domain_num_cosets
        c_evals.rotate_right(t_domain_num_cosets); // TODO: double check this, and investigate the complexity of rotate_right
        println!("Rotated c_evals: {:?}", c_evals);
        let c_rotated_gamma = LabeledPolynomial::new(
            "c_rotated_gamma".to_string(),
            poly_from_evals(&c_evals),
            None,
            None,
        );
        // Get a quotient poly q(X) = (c(X) - c(\gammaX))/t_vanishing

        let (c_comms, c_comm_rands) =
            PC::commit(committer_key, vec![&c], None).map_err(Error::from_pc_err)?;
        let c_comm = c_comms[0].clone();
        let c_comm_rand = c_comm_rands[0].clone();

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
        let mut idx_f_evals = vec![F::zero(); f_domain_size];
        for i in 0..f_domain_num_cosets {
            for j in 0..coset_domain_size {
                idx_f_evals[j * f_domain_num_cosets + i] = beta_powers[j];
            }
        }
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

        // Now compute all the polynomials for t
        let mut idx_t_evals = vec![F::zero(); t_domain_size];
        for i in 0..t_domain_num_cosets {
            for j in 0..coset_domain_size {
                idx_t_evals[j * t_domain_num_cosets + i] = beta_powers[j];
            }
        }

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

        // Commit to the f and t indexing polynomials and the quotient polynomials
        let (idx_comms, idx_comm_rands) =
            PC::commit(committer_key, vec![&idx_f, &idx_t], None).unwrap();
        let idx_f_comm = idx_comms[0].clone();
        let idx_f_comm_rand = idx_comm_rands[0].clone();
        let idx_t_comm = idx_comms[1].clone();
        let idx_t_comm_rand = idx_comm_rands[1].clone();

        // Step 4: Compute summation polynomial S_b(X).
        // Step 4.a: Compute S_b(X) for b = {f, t}.
        let mut s_f_evals = vec![F::zero(); f_domain_size];
        for i in 0..f_domain_num_cosets {
            let mut s_f_sum = F::zero();
            for j in 0..coset_domain_size {
                s_f_sum += f_evals[j * f_domain_num_cosets + i] * beta_powers[j];
            }
            for j in 0..coset_domain_size {
                s_f_evals[j * f_domain_num_cosets + i] = s_f_sum;
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

        let mut s_t_evals = vec![F::zero(); t_domain_size];
        for i in 0..t_domain_num_cosets {
            let mut s_t_sum = F::zero();
            for j in 0..coset_domain_size {
                s_t_sum += t_evals[j * t_domain_num_cosets + i] * beta_powers[j];
            }
            for j in 0..coset_domain_size {
                s_t_evals[j * t_domain_num_cosets + i] = s_t_sum;
            }
        }
        let s_t =
            LabeledPolynomial::new("s_t".to_string(), poly_from_evals(&s_t_evals), None, None);
        s_t_evals.rotate_right(t_domain_num_cosets);
        let s_t_rotated_gamma = LabeledPolynomial::new(
            "s_t_rotated_gamma".to_string(),
            poly_from_evals(&s_t_evals),
            None,
            None,
        );

        let (s_comms, s_comm_rands) = PC::commit(committer_key, vec![&s_f, &s_t], None).unwrap();
        let s_f_comm = s_comms[0].clone();
        let s_f_comm_rand = s_comm_rands[0].clone();
        let s_t_comm = s_comms[1].clone();
        let s_t_comm_rand = s_comm_rands[1].clone();

        // Step 5: Compute induction polynomial B_b(X), which contains partial sums
        // Step 5.a: Compute B_b(X) for b = {f, t}.
        let mut b_f_evals = vec![F::zero(); f_domain_size];
        for i in 0..f_domain_num_cosets {
            let mut b_f_sum = F::zero();
            let coset_sum_piece = s_f_evals[i] * coset_domain.size_inv; // the sum over this coset divided by the coset size, TODO: don't do this from
            for j in 0..coset_domain_size {
                b_f_sum += f_evals[j * f_domain_num_cosets + i] * beta_powers[j] - coset_sum_piece;
                b_f_evals[j * f_domain_num_cosets + i] = b_f_sum;
            }
        }
        let b_f =
            LabeledPolynomial::new("b_f".to_string(), poly_from_evals(&b_f_evals), None, None);
        b_f_evals.rotate_right(f_domain_num_cosets);
        let b_f_rotated_gamma = LabeledPolynomial::new(
            "b_f_rotated_gamma".to_string(),
            poly_from_evals(&b_f_evals),
            None,
            None,
        );
        let mut f_evals_rotated_gamma = f_evals.clone();
        f_evals_rotated_gamma.rotate_right(f_domain_num_cosets);
        let f_rotated_gamma = LabeledPolynomial::new(
            "f_rotated_gamma".to_string(),
            poly_from_evals(&f_evals_rotated_gamma),
            None,
            None,
        );

        let mut b_t_evals = vec![F::zero(); t_domain_size];
        for i in 0..t_domain_num_cosets {
            let mut b_t_sum = F::zero();
            let coset_sum_piece = s_t_evals[i] * coset_domain.size_inv; // the sum over this coset divided by the coset size
            for j in 0..coset_domain_size {
                b_t_sum += t_evals[j * t_domain_num_cosets + i] * beta_powers[j] - coset_sum_piece;
                b_t_evals[j * t_domain_num_cosets + i] = b_t_sum;
            }
        }
        let b_t =
            LabeledPolynomial::new("b_t".to_string(), poly_from_evals(&b_t_evals), None, None);
        b_t_evals.rotate_right(t_domain_num_cosets);
        let b_t_rotated_gamma = LabeledPolynomial::new(
            "b_t_rotated_gamma".to_string(),
            poly_from_evals(&b_t_evals),
            None,
            None,
        );
        let mut t_evals_rotated_gamma = t_evals.clone();
        t_evals_rotated_gamma.rotate_right(t_domain_num_cosets);
        let t_rotated_gamma = LabeledPolynomial::new(
            "t_rotated_gamma".to_string(),
            poly_from_evals(&t_evals_rotated_gamma),
            None,
            None,
        );

        let (b_comms, b_comm_rands) = PC::commit(committer_key, vec![&b_f, &b_t], None).unwrap();
        let b_f_comm = b_comms[0].clone();
        let b_f_comm_rand = b_comm_rands[0].clone();
        let b_t_comm = b_comms[1].clone();
        let b_t_comm_rand = b_comm_rands[1].clone();

        // Step 6: Compute inverse polynomial U_b(X)
        // Step 6.a: Compute U_b(X) for b = {f, t}.
        let mut u_f_denoms: Vec<F> = s_f_evals.iter().map(|&x| alpha - x).collect();
        batch_inversion(&mut u_f_denoms);
        let mut u_f_evals = vec![F::zero(); f_domain_size];
        for i in 0..f_domain_num_cosets {
            for j in 0..coset_domain_size {
                u_f_evals[j * f_domain_num_cosets + i] = u_f_denoms[i];
            }
        }
        let u_f =
            LabeledPolynomial::new("u_f".to_string(), poly_from_evals(&u_f_evals), None, None);

        let mut u_t_denoms: Vec<F> = s_t_evals.iter().map(|&x| alpha - x).collect();
        batch_inversion(&mut u_t_denoms);
        let mut u_t_evals = vec![F::zero(); t_domain_size];
        for i in 0..t_domain_num_cosets {
            for j in 0..coset_domain_size {
                u_t_evals[j * t_domain_num_cosets + i] = u_t_denoms[i];
            }
        }
        let u_t =
            LabeledPolynomial::new("u_t".to_string(), poly_from_evals(&u_t_evals), None, None);

        let (u_comms, u_comm_rands) = PC::commit(committer_key, vec![&u_f, &u_t], None).unwrap();
        let u_f_comm = u_comms[0].clone();
        let u_f_comm_rand = u_comm_rands[0].clone();
        let u_t_comm = u_comms[1].clone();
        let u_t_comm_rand = u_comm_rands[1].clone();

        // Step 7: Prove summations of U_0 and c * U_1
        // Step 7.a: Compute inverse summation polynomials T_b(X) for b = {f, t}.
        let mut T_f_evals = vec![F::zero(); f_domain_size];
        T_f_evals[f_domain_size - 1] = u_f_evals[f_domain_size - 1];
        for i in (0..f_domain_size - 1).rev() {
            T_f_evals[i] = T_f_evals[i + 1] + u_f_evals[i];
        }
        let T_f =
            LabeledPolynomial::new("T_f".to_string(), poly_from_evals(&T_f_evals), None, None);
        let mut T_t_evals = vec![F::zero(); t_domain_size];
        T_t_evals[t_domain_size - 1] = c_evals[t_domain_size - 1] * u_t_evals[t_domain_size - 1];
        for i in (0..t_domain_size - 1).rev() {
            T_t_evals[i] = T_t_evals[i + 1] + c_evals[i] * u_t_evals[i];
        }
        let T_t =
            LabeledPolynomial::new("T_t".to_string(), poly_from_evals(&T_t_evals), None, None);
        let (T_comms, T_comm_rands) = PC::commit(committer_key, vec![&T_f, &T_t], None).unwrap();
        let T_f_comm = T_comms[0].clone();
        let T_f_comm_rand = T_comm_rands[0].clone();
        let T_t_comm = T_comms[1].clone();
        let T_t_comm_rand = T_comm_rands[1].clone();

        // Construct all the zero tests
        let opening_challenge = F::rand(&mut fs_rng); // TODO: do this or u128::rand?
        let query_set = QuerySet::new();
        let comms = vec![
            &c_comm,
            &idx_f_comm,
            &idx_t_comm,
            &s_f_comm,
            &s_t_comm,
            &b_f_comm,
            &b_t_comm,
            &u_f_comm,
            &u_t_comm,
            &T_f_comm,
            &T_t_comm,
        ];
        let comm_rands = vec![
            &c_comm_rand,
            &idx_f_comm_rand,
            &idx_t_comm_rand,
            &s_f_comm_rand,
            &s_t_comm_rand,
            &b_f_comm_rand,
            &b_t_comm_rand,
            &u_f_comm_rand,
            &u_t_comm_rand,
            &T_f_comm_rand,
            &T_t_comm_rand,
        ];
        let polys = [
            &c, &idx_f, &idx_t, &s_f, &s_t, &b_f, &b_t, &u_f, &u_t, &T_f, &T_t,
        ];
        let pc_proof = PC::batch_open(
            committer_key,
            polys,             // all the polys, including the quotient polynomials (no rotated)
            comms,             // same as polys but commitments
            &query_set,        // all query points and polynomials
            opening_challenge, // from f-s
            comm_rands,        // same as polys but comm rands
            None,
        )
        .map_err(Error::from_pc_err)?;

        // lets say the zero test is A(X) = B(gamma X) over G, C(X) = 0 over G
        // have to send commitments to A, B, and Q_G(X) = LC/V_G(X)
        // we need B(gamma X) to compute Q_G(X)
        // send batch eval proof for A(z), B(gamma z), Q_G(z)
        // also send evaluations of A(z), B(gamma z), Q_G(z)

        return Ok(Proof {
            c_comm,
            idx_f_comm,
            idx_t_comm,
            s_f_comm,
            s_t_comm,
            b_f_comm,
            b_t_comm,
            u_f_comm,
            u_t_comm,
            T_f_comm,
            T_t_comm,
            pc_proof,
        });
    }

    pub fn verify(
        verifier_key: &PC::VerifierKey,
        proof: &Proof<F, PC>,
        f_comm: &LabeledCommitment<PC::Commitment>,
        t_comm: &LabeledCommitment<PC::Commitment>,
    ) -> Result<bool, Error<PC::Error>> {
        // Derive some lagranges and vanishing polynomials
        // Do a bunch of zero checks
        // Batch verify everything with 2 pairings
        // PC::batch_check(
        //     vk,
        //     commitments,
        //     query_set,
        //     evaluations,
        //     proof,
        //     opening_challenge,
        //     rng,
        // );
        return Ok(true);
    }
}
