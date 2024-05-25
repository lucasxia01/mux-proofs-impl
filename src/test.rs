mod tests {
    use super::*;
    use ark_poly::{
        univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
        Radix2EvaluationDomain,
    };
    use blake2::Blake2s;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_poly_commit::{LabeledPolynomial, PolynomialCommitment};
    use rand_chacha::ChaChaRng;

    use crate::{
        coset_lookup::{commit_to_evals, poly_from_evals, CosetLookup},
        rng::{FiatShamirRng, SimpleHashFiatShamirRng},
    };

    // Test with subvector size of 1
    #[test]
    fn prove_and_verify_simple() {
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
        let subvector_size = 1;
        // Universal setup
        let universal_srs = CosetLookupInst::universal_setup(16, rng).unwrap();

        // Index to generate the prover and verifier keys
        let (committer_key, verifier_key) = CosetLookupInst::index(&universal_srs, 16).unwrap();

        let f = LabeledPolynomial::new("f".to_string(), poly_from_evals(&f_evals), None, None);
        let t = LabeledPolynomial::new("t".to_string(), poly_from_evals(&t_evals), None, None);
        // Get the public statement: the commitments to f and t
        let f_comm = PC::commit(&committer_key, vec![&f], None).unwrap().0[0].clone();
        let t_comm = PC::commit(&committer_key, vec![&t], None).unwrap().0[0].clone();

        let f_domain = Radix2EvaluationDomain::<Fr>::new(f_evals.len()).unwrap();
        let t_domain = Radix2EvaluationDomain::<Fr>::new(t_evals.len()).unwrap();
        let coset_domain = Radix2EvaluationDomain::<Fr>::new(subvector_size).unwrap();
        // Prove
        let proof = CosetLookupInst::prove(
            &committer_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &f_comm,
            &t_comm,
            f_evals,
            t_evals,
            f,
            t,
        )
        .unwrap();
        let result = CosetLookupInst::verify(
            &verifier_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &proof,
            &f_comm,
            &t_comm,
        )
        .unwrap();

        assert!(result);
    }

    // Test with subvector size of 2
    #[test]
    fn prove_and_verify_simple_2() {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type CosetLookupInst = CosetLookup<Fr, PC, FS>;
        let max_degree = 1024;
        let rng = &mut ark_std::test_rng();

        // just assume the coset domain is 1 for now
        let f_evals = vec![Fr::from(1), Fr::from(2)];
        let t_evals = vec![Fr::from(1), Fr::from(2)];
        let subvector_size = 2;
        // Universal setup
        let universal_srs = CosetLookupInst::universal_setup(16, rng).unwrap();

        // Index to generate the prover and verifier keys
        let (committer_key, verifier_key) = CosetLookupInst::index(&universal_srs, 16).unwrap();

        let f = LabeledPolynomial::new("f".to_string(), poly_from_evals(&f_evals), None, None);
        let t = LabeledPolynomial::new("t".to_string(), poly_from_evals(&t_evals), None, None);
        // Get the public statement: the commitments to f and t
        let f_comm = PC::commit(&committer_key, vec![&f], None).unwrap().0[0].clone();
        let t_comm = PC::commit(&committer_key, vec![&t], None).unwrap().0[0].clone();

        let f_domain = Radix2EvaluationDomain::<Fr>::new(f_evals.len()).unwrap();
        let t_domain = Radix2EvaluationDomain::<Fr>::new(t_evals.len()).unwrap();
        let coset_domain = Radix2EvaluationDomain::<Fr>::new(subvector_size).unwrap();
        // Prove
        let proof = CosetLookupInst::prove(
            &committer_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &f_comm,
            &t_comm,
            f_evals,
            t_evals,
            f,
            t,
        )
        .unwrap();
        let result = CosetLookupInst::verify(
            &verifier_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &proof,
            &f_comm,
            &t_comm,
        )
        .unwrap();

        assert!(result);
    }

    // Test with subvector size of 4, f size of 8, t size of 4
    #[test]
    fn prove_and_verify_medium() {
        // create a prover from prover.rs
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type CosetLookupInst = CosetLookup<Fr, PC, FS>;
        let max_degree = 1024;
        let rng = &mut ark_std::test_rng();

        // just assume the coset domain is 1 for now
        let f_evals = vec![
            Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(2),
            Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(3),
            Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(2),
            Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(2), Fr::from(1), Fr::from(1), Fr::from(1), Fr::from(3)
        ];
        
        let t_evals = vec![
            Fr::from(1), Fr::from(1), Fr::from(2), Fr::from(1),
            Fr::from(2), Fr::from(1), Fr::from(1), Fr::from(3),
            Fr::from(1), Fr::from(1), Fr::from(2), Fr::from(1),
            Fr::from(2), Fr::from(1), Fr::from(1), Fr::from(3),
        ]; // (1, 2, 1, 2), (1, 1, 1, 1), (2, 1, 2, 1), (2, 3, 2, 3)
        let subvector_size = 2;
        // Universal setup
        let universal_srs = CosetLookupInst::universal_setup(64, rng).unwrap();

        // Index to generate the prover and verifier keys
        let (committer_key, verifier_key) = CosetLookupInst::index(&universal_srs, 64).unwrap();

        let f = LabeledPolynomial::new("f".to_string(), poly_from_evals(&f_evals), None, None);
        let t = LabeledPolynomial::new("t".to_string(), poly_from_evals(&t_evals), None, None);
        // Get the public statement: the commitments to f and t
        let f_comm = PC::commit(&committer_key, vec![&f], None).unwrap().0[0].clone();
        let t_comm = PC::commit(&committer_key, vec![&t], None).unwrap().0[0].clone();

        let f_domain = Radix2EvaluationDomain::<Fr>::new(f_evals.len()).unwrap();
        let t_domain = Radix2EvaluationDomain::<Fr>::new(t_evals.len()).unwrap();
        let coset_domain = Radix2EvaluationDomain::<Fr>::new(subvector_size).unwrap();
        // Prove
        let proof = CosetLookupInst::prove(
            &committer_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &f_comm,
            &t_comm,
            f_evals,
            t_evals,
            f,
            t,
        )
        .unwrap();
        let result = CosetLookupInst::verify(
            &verifier_key,
            &f_domain,
            &t_domain,
            &coset_domain,
            &proof,
            &f_comm,
            &t_comm,
        )
        .unwrap();

        assert!(result);
    }
}
