// This file contains the prover, round by round

use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use ark_ff::{to_bytes, Field, FftField, UniformRand};
use ark_poly::{univariate::SparsePolynomial, univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain, Radix2EvaluationDomain};
use ark_std::ops::*;
use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};

use std::fmt::Error;

use crate::rng::FiatShamirRng;
// we need pick parameters
// field, group, FS, evlauation domain

pub fn is_pow_2(x: usize) -> bool {
    (x & (x - 1)) == 0
}

pub fn poly_from_evals<F: FftField>(evals: &Vec<F>) -> DensePolynomial<F> {
    let n = evals.len();
    assert!(is_pow_2(n));

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals.to_owned(), domain);
    eval_form.interpolate()
}

pub fn get_mult_subgroup_vanishing_poly<F: FftField>(n: usize) -> SparsePolynomial<F> {
    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    domain.vanishing_polynomial()
}

// pub struct Proof<F: FftField> {

// }

pub struct Prover<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng> {
    // f_domain: GeneralEvaluationDomain<F>,
    // t_domain: GeneralEvaluationDomain<F>,
    // coset_domain: GeneralEvaluationDomain<F>,
    commitment_key : PC::CommitterKey,
    f_evals : Vec<F>,
    t_evals : Vec<F>,
    f : DensePolynomial<F>,
    t : DensePolynomial<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
    coset_domain_size : usize
}

impl<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng>
    Prover<F, PC, FS>
{

    pub const PROTOCOL_NAME: &'static [u8] = b"MUX_Proofs";

    pub fn new(commitment_key : PC::CommitterKey, f_evals : Vec<F>, t_evals : Vec<F>, coset_domain_size : usize) -> Self {
        // assert_eq!(f_domain.size(), f_evals.len());
        // assert_eq!(t_domain.size(), t_evals.len());
        // self.f_domain = f_domain;
        // self.t_domain = t_domain;
        // self.coset_domain = coset_domain;
        return Self {
            commitment_key,
            f_evals : f_evals.clone(),
            t_evals : t_evals.clone(),
            f : poly_from_evals(&f_evals),
            t : poly_from_evals(&t_evals),
            _pc: PhantomData,
            _fs: PhantomData,
            coset_domain_size,
        }
        // self.f_evals = f_evals.clone();
        // self.t_evals = t_evals.clone();
        // // FFT to compute the Dense polynomials from the evals
        // self.f = poly_from_evals(&f_evals);
        // self.t = poly_from_evals(&t_evals);
    }

    pub fn prove(self) -> Result<Vec<u8>, Error> {
        
        // TODO: fix this initialization to include all public inputs
        let mut fs_rng = FS::initialize(
            &to_bytes![&Self::PROTOCOL_NAME].unwrap(),
        );
        let f_domain_size = self.f_evals.len();
        let t_domain_size = self.t_evals.len();
        assert_eq!(f_domain_size % self.coset_domain_size, 0);
        assert_eq!(t_domain_size % self.coset_domain_size, 0);
        let f_domain_num_cosets = f_domain_size / self.coset_domain_size;
        let t_domain_num_cosets = t_domain_size / self.coset_domain_size;
        // Set up the vanishing polynomials for the two domains
        let t_vanishing: DensePolynomial<F> = get_mult_subgroup_vanishing_poly(t_domain_size).into();
        let f_vanishing: DensePolynomial<F> = get_mult_subgroup_vanishing_poly(f_domain_size).into();
        // Step 1: compute count polynomial c(X) that encodes the counts the frequency of each table vector in f
        let f_vecs: Vec<Vec<F>> = (0..f_domain_num_cosets)
            .map(|coset_idx| {
                (0..self.coset_domain_size)
                    .map(|i| self.f_evals[i * self.coset_domain_size + coset_idx])
                    .collect()
            })
            .collect();
        let t_vecs: Vec<Vec<F>> = (0..t_domain_num_cosets)
            .map(|coset_idx| {
                (0..self.coset_domain_size)
                    .map(|i| self.t_evals[i * self.coset_domain_size + coset_idx])
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
        for i  in 0..t_domain_size {
            c_evals[i] = F::from(f_vec_counts[&t_vecs[i%t_domain_num_cosets].clone()]);
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
        let c_rotated = LabeledPolynomial::new("c_rotated".to_string(), c_coeffs_rotated.clone(), None, None);
        let (c_comms, _) = PC::commit(&self.commitment_key, vec![&c, &c_rotated], None).unwrap();
        // Now that we've committed, do a zero test over t_domain.
        // Get a quotient poly q(X) = (c(X) - c(\gammaX))/t_vanishing over t_domain
        let c_quotient = (c_coeffs.sub(&c_coeffs_rotated)).div(&t_vanishing);

        // Step 2: Compute challenges alpha and beta
        let alpha: F = u128::rand(&mut fs_rng).into();
        let beta: F = u128::rand(&mut fs_rng).into();

        // Step 3: Compute position-indexing powers-of-beta polynomial I_b(X)

        // Step 4: Compute summation polynomial S_b(X)

        // Step 5: Compute induction polynomial B_b(X), which contains partial sums

        // Step 6: Compute inverse polynomial U_b(X)

        // Step 7: Prove summations of U_0 and c * U_1 

        return Ok(vec![]);
    }
}