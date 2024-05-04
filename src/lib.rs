use blake2::{Blake2s};
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

#[test]
fn test() {
    // create a prover from prover.rs
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
    // let prover = Prover::<Fr, MarlinKZG10<Bls12_381, DensePolynomial<Fr>>, FS> ::new();
}
