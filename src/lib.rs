// This file contains the prover, round by round

use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use ark_ff::{to_bytes, FftField, Field, UniformRand};
use ark_poly::{
    univariate::{DensePolynomial, SparsePolynomial},
    EvaluationDomain, Evaluations, GeneralEvaluationDomain, Polynomial, Radix2EvaluationDomain,
};
use ark_poly_commit::{
    LabeledCommitment, LabeledPolynomial, LinearCombination, PCUniversalParams,
    PolynomialCommitment,
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
    t_vanishing: DensePolynomial<F>,
    f_vanishing: DensePolynomial<F>,
) -> Vec<LinearCombination<F>> {
    let zero_test_c = LinearCombination::new(
        "zero_test_c".to_string(),
        vec![
            (F::one(), "c_rotated".to_string()),
            (F::one(), "c".to_string()),
            (
                t_vanishing.evaluate(&opening_challenge),
                "t_vanishing".to_string(),
            ),
        ],
    );
    return vec![zero_test_c];
}

// Copied from sublonk
pub fn get_mult_subgroup_vanishing_poly<F: FftField>(n: usize) -> SparsePolynomial<F> {
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    domain.vanishing_polynomial()
}

pub type UniversalSRS<F, PC> = <PC as PolynomialCommitment<F, DensePolynomial<F>>>::UniversalParams;

pub struct Proof<F: FftField> {
    dummy: F,
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
    ) -> Result<Proof<F>, Error<PC::Error>> {
        // TODO: fix this initialization to include all public inputs
        let mut fs_rng = FS::initialize(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
        let f_domain_size = f_evals.len();
        let t_domain_size = t_evals.len();
        assert_eq!(f_domain_size % coset_domain_size, 0);
        assert_eq!(t_domain_size % coset_domain_size, 0);
        let f_domain_num_cosets = f_domain_size / coset_domain_size;
        let t_domain_num_cosets = t_domain_size / coset_domain_size;
        // Set up the vanishing polynomials for the two domains
        let t_vanishing: DensePolynomial<F> =
            get_mult_subgroup_vanishing_poly(t_domain_size).into();
        let f_vanishing: DensePolynomial<F> =
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
        // count how many each vector appears in t_vecs
        let mut f_vec_counts: HashMap<Vec<F>, u32> = HashMap::new();
        for f_vec in &f_vecs {
            *f_vec_counts.entry(f_vec.clone()).or_insert(0) += 1;
        }
        let mut t_vec_counts: HashMap<Vec<F>, u32> = HashMap::new();
        for t_vec in &t_vecs {
            *t_vec_counts.entry(t_vec.clone()).or_insert(0) += 1;
        }
        // loop through f_vec_counts and check that each vector appears in t_vec_counts
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
        // commit to c(X) and c(\gammaX)
        let c_coeffs = poly_from_evals(&c_evals);
        // rotate c_evals by 1
        c_evals.rotate_right(1);
        println!("Rotated c_evals: {:?}", c_evals);
        let c_coeffs_rotated = poly_from_evals(&c_evals);
        // Want to prove that c(X) - c(\gammaX) = 0
        let c = LabeledPolynomial::new("c".to_string(), c_coeffs.clone(), None, None);
        let c_rotated = LabeledPolynomial::new(
            "c_rotated".to_string(),
            c_coeffs_rotated.clone(),
            None,
            None,
        );
        let (c_comms, _) = PC::commit(committer_key, vec![&c, &c_rotated], None).unwrap();
        // Now that we've committed, do a zero test over t_domain.
        // Get a quotient poly q(X) = (c(X) - c(\gammaX))/t_vanishing
        let c_quotient = (c_coeffs.sub(&c_coeffs_rotated)).div(&t_vanishing);

        // Step 2: Compute challenges alpha and beta
        let alpha = F::rand(&mut fs_rng);
        let beta = F::rand(&mut fs_rng);

        // Step 3: Compute position-indexing powers-of-beta polynomial I_b(X)
        // Precompute powers of beta up to coset_domain_size iteratively using the previous power of beta
        let mut beta_powers: Vec<F> = vec![F::one()];
        for i in 1..coset_domain_size {
            beta_powers.push(beta * beta_powers[i - 1]);
        }
        // Step 3.a: Compute I_b(X) for b = {f, t}
        let idx_f: Vec<_> = f_evals
            .iter()
            .zip(beta_powers.iter().cycle())
            .map(|(f, b)| *f * *b)
            .take(f_domain_size)
            .collect();
        let idx_t: Vec<_> = t_evals
            .iter()
            .zip(beta_powers.iter().cycle())
            .map(|(t, b)| *t * *b)
            .take(t_domain_size)
            .collect();
        let idx_f_coeffs = poly_from_evals(&idx_f);
        let idx_t_coeffs = poly_from_evals(&idx_t);
        let idx_f = LabeledPolynomial::new("idx_f".to_string(), idx_f_coeffs, None, None);
        let idx_t = LabeledPolynomial::new("idx_t".to_string(), idx_t_coeffs, None, None);
        let (idx_comms, _) = PC::commit(committer_key, vec![&idx_f, &idx_t], None).unwrap();

        // Step 4: Compute summation polynomial S_b(X)

        // Step 5: Compute induction polynomial B_b(X), which contains partial sums

        // Step 6: Compute inverse polynomial U_b(X)

        // Step 7: Prove summations of U_0 and c * U_1

        // Construct all the zero tests
        let opening_challenge = F::rand(&mut fs_rng); // TODO: do this or u128::rand?
        let lc_s = construct_zero_tests(opening_challenge, t_vanishing, f_vanishing);

        let dummy: F = F::rand(&mut fs_rng);
        return Ok(Proof { dummy });
    }
}
