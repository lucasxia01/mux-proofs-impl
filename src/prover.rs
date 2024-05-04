// This file contains the prover, round by round

use std::{collections::HashMap, hash::Hash, marker::PhantomData};

use ark_ff::{to_bytes, FftField, PrimeField, UniformRand};
use ark_poly::{Evaluations, 
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Radix2EvaluationDomain
};
use ark_poly_commit::{PolynomialCommitment};

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

// pub struct Proof<F: PrimeField> {

// }

pub struct Prover<F: FftField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng> {
    // f_domain: GeneralEvaluationDomain<F>,
    // t_domain: GeneralEvaluationDomain<F>,
    // coset_domain: GeneralEvaluationDomain<F>,
    f_evals : Vec<F>,
    t_evals : Vec<F>,
    f : DensePolynomial<F>,
    t : DensePolynomial<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
    coset_domain_size : usize
}

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng>
    Prover<F, PC, FS>
{

    pub const PROTOCOL_NAME: &'static [u8] = b"MUX_Proofs";

    pub fn new(f_evals : Vec<F>, t_evals : Vec<F>, coset_domain_size : usize) -> Self {
        // assert_eq!(f_domain.size(), f_evals.len());
        // assert_eq!(t_domain.size(), t_evals.len());
        // self.f_domain = f_domain;
        // self.t_domain = t_domain;
        // self.coset_domain = coset_domain;
        return Self {
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
        let mut f_vec_counts: HashMap<Vec<F>, i32> = HashMap::new();
        for f_vec in &f_vecs {
            *f_vec_counts.entry(f_vec.clone()).or_insert(0) += 1;
        }
        let mut t_vec_counts: HashMap<Vec<F>, i32> = HashMap::new();
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
        let mut c_evals: Vec<i32> = vec![0; t_domain_size];
        for i  in 0..t_domain_size {
            c_evals[i] = f_vec_counts[&t_vecs[i%t_domain_num_cosets].clone()];
        }
        // Step 1.b: ZeroTest to should that c(\gammaX) = c(X)
        
        
        println!("{:?}", c_evals);
        


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