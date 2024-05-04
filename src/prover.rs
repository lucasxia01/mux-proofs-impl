// This file contains the prover, round by round

use std::marker::PhantomData;

use ark_ff::PrimeField;
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain
};
use ark_poly_commit::PolynomialCommitment;

use crate::rng::FiatShamirRng;
// we need pick parameters
// field, group, FS, evlauation domain

pub struct Prover<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng> (
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<FS>
);

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, FS: FiatShamirRng>
    Prover<F, PC, FS>
{

    pub fn new(f : DensePolynomial<F>, t : DensePolynomial<F>) {
        let f_domain = GeneralEvaluationDomain::<F>::new(f.len()).unwrap();
        let t_domain = GeneralEvaluationDomain::<F>::new(t.len()).unwrap();
    }
}