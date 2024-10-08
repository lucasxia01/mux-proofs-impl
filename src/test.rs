#![allow(unused_variables)]
#![allow(non_snake_case)]
#![allow(unused_imports)]

// Tests for the Succinct Vector Lookup protocol
mod tests {
    use std::mem::size_of_val;

    use super::*;
    use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Radix2EvaluationDomain};
    use blake2::Blake2s;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use rand_chacha::ChaChaRng;

    use crate::{
        succinct_lookup::{poly_from_evals, SuccinctLookup},
        rng::{FiatShamirRng, SimpleHashFiatShamirRng},
        VectorLookup,
    };

    // Proves and verifies using the Succinct Vector Lookup protocol
    fn prove_and_verify(f_vals: Vec<Fr>, t_vals: Vec<Fr>, vector_size: usize) -> bool {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type SuccinctLookupInst = SuccinctLookup<Fr, PC, FS>;
        let rng = &mut ark_std::test_rng();
        let lookup_size = f_vals.len() / vector_size;
        let table_size = t_vals.len() / vector_size;
        assert!(f_vals.len() % vector_size == 0);
        assert!(t_vals.len() % vector_size == 0);

        // Universal setup
        let universal_srs = SuccinctLookupInst::universal_setup(1024, rng).unwrap();

        // Index to generate the prover and verifier keys
        let (pk, vk) =
            SuccinctLookupInst::index(&universal_srs, vector_size, lookup_size, table_size).unwrap();

        let (f_comm_pair, f) = SuccinctLookupInst::commit_lookup(&pk, f_vals.clone(), rng).unwrap();
        let (t_comm_pair, t) = SuccinctLookupInst::commit_table(&pk, t_vals.clone(), rng).unwrap();

        // Prove
        let proof =
            SuccinctLookupInst::prove(&pk, &f_comm_pair, &t_comm_pair, f_vals, t_vals, f, t, rng).unwrap();
        println!("c comm size: {:?}", size_of_val(proof.c_comm.commitment()));
        println!("pc proof length: {:?}", proof.pc_proof.len());
        println!(
            "pc proof element size: {:?}",
            size_of_val(&proof.pc_proof[0].w)
        );
        let result = SuccinctLookupInst::verify(&vk, &proof, &f_comm_pair.0, &t_comm_pair.0).unwrap();
        return result;
    }

    // Test with vector size of 1
    #[test]
    fn prove_and_verify_simple() {
        let f_vals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
        ];
        let t_vals = vec![Fr::from(1), Fr::from(2)];
        let vector_size = 1;
        assert!(prove_and_verify(f_vals, t_vals, vector_size));
    }

    // Test with vector size of 2
    #[test]
    fn prove_and_verify_simple_2() {
        let f_vals = vec![Fr::from(1), Fr::from(2)];
        let t_vals = vec![Fr::from(1), Fr::from(2)];
        let vector_size = 2;
        assert!(prove_and_verify(f_vals, t_vals, vector_size));
    }

    // Test with vector size of 4, f size of 8, t size of 4
    #[test]
    fn prove_and_verify_medium() {
        // vector size of 4
        let f_vals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(2),
            Fr::from(3),
        ];

        let t_vals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(1),
            Fr::from(1),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(2),
            Fr::from(3),
        ]; // (1, 2, 1, 2), (1, 1, 1, 1), (2, 1, 2, 1), (2, 3, 2, 3)
        let vector_size = 4;
        assert!(prove_and_verify(f_vals, t_vals, vector_size));
    }
}
