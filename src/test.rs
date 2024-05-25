use ark_poly::{univariate::DensePolynomial, GeneralEvaluationDomain};
use blake2::Blake2s;

use ark_bls12_381::{Bls12_381, Fr};
use rand_chacha::ChaChaRng;
pub mod rng;
pub use mux_proofs_impl::rng::FiatShamirRng;
pub use mux_proofs_impl::rng::SimpleHashFiatShamirRng;

#[cfg(test)]
mod tests {
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use mux_proofs_impl::{commit_to_evals, poly_from_evals, CosetLookup};

    use super::*;
    #[test]
    fn prove_and_verify() {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type CosetLookupInst = CosetLookup<Fr, PC, FS>;
        let max_degree = 1024;
        let rng = &mut ark_std::test_rng();

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

        // Universal setup
        let universal_srs = CosetLookupInst::universal_setup(16, rng).unwrap();

        // Index to generate the prover and verifier keys
        let (committer_key, verifier_key) = CosetLookupInst::index(&universal_srs, 16).unwrap();

        let f = LabeledPolynomial::new("f".to_string(), poly_from_evals(&f_evals), None, None);
        let t = LabeledPolynomial::new("t".to_string(), poly_from_evals(&t_evals), None, None);
        // Get the public statement: the commitments to f and t
        let f_comm = PC::commit(&committer_key, vec![&f], None).unwrap().0[0].clone();
        let t_comm = PC::commit(&committer_key, vec![&t], None).unwrap().0[0].clone();

        // Prove
        let proof =
            CosetLookupInst::prove(&committer_key, &f_comm, &t_comm, f_evals, t_evals, f, t, 1)
                .unwrap();
        let result = CosetLookupInst::verify(&verifier_key, &proof, &f_comm, &t_comm).unwrap();

        assert!(result);
    }
}
