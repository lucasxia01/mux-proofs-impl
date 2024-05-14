use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use blake2::Blake2s;

use ark_bls12_381::{Bls12_381, Fr};
use rand_chacha::ChaChaRng;
pub mod rng;
pub use mux_proofs_impl::rng::FiatShamirRng;
pub use mux_proofs_impl::rng::SimpleHashFiatShamirRng;

#[cfg(test)]
mod tests {
    use ark_poly_commit::PolynomialCommitment;
    use mux_proofs_impl::VectorLookup;

    use super::*;
    #[test]
    fn prove_and_verify() {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type VectorLookupInst = VectorLookup<Fr, PC, FS>;
        let max_degree = 1024;
        let rng = &mut ark_std::test_rng();
        let srs = PC::setup(max_degree, None, rng).unwrap();
        let (committer_key, verifier_key) = PC::trim(&srs, max_degree, 0, None).unwrap();

        // just assume the coset domain is 1 for now
        let f_evals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
        ];
        let t_evals = vec![Fr::from(1), Fr::from(2)];

        let universal_srs = VectorLookupInst::universal_setup(16, rng).unwrap();
    }
}
