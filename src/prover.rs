// This file contains the prover, round by round

use std::marker::PhantomData;

use ark_ff::{to_bytes, FftField, PrimeField, UniformRand};
use ark_poly::{Evaluations, 
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain, Radix2EvaluationDomain
};
use ark_poly_commit::{PolynomialCommitment};

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

    pub fn prove() {
        let mut fs_rng = FS::initialize(
            &to_bytes![&Self::PROTOCOL_NAME].unwrap(),
        );
        // Step 1: compute count polynomial c(X) that encodes the counts the frequency of each table vector in f

        // Step 2: Compute challenges alpha and beta
        let alpha: F = u128::rand(&mut fs_rng).into();
        let beta: F = u128::rand(&mut fs_rng).into();

        // Step 3: Compute position-indexing powers-of-beta polynomial I_b(X)

        // Step 4: Compute summation polynomial S_b(X)

        // Step 5: Compute induction polynomial B_b(X), which contains partial sums

        // Step 6: Compute inverse polynomial U_b(X)

        // Step 7: Prove summations of U_0 and c * U_1 
    }
}