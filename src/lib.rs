use blake2::Blake2s;
use ark_poly::{
    univariate::DensePolynomial, GeneralEvaluationDomain
};

use ark_bls12_381::{Bls12_381, Fr};
use prover::Prover;
use rand_chacha::ChaChaRng;
pub mod rng;
use rng::FiatShamirRng;
pub use rng::SimpleHashFiatShamirRng;
mod prover;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn prove_and_verify() {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        // just assume the coset domain is 1 for now
        let f_evals = vec![Fr::from(1), Fr::from(2), Fr::from(1), Fr::from(2)];
        let t_evals = vec![Fr::from(1), Fr::from(2)];
        let prover = Prover::<Fr, MarlinKZG10<Bls12_381, DensePolynomial<Fr>>, FS> ::new(f_evals, t_evals, 1);
    }
}
