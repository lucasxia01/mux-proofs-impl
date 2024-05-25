#![allow(non_snake_case)]
use ark_poly::{univariate::DensePolynomial, Evaluations};
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain};

use ark_ec::PairingEngine;
use ark_ff::{fields::batch_inversion, FftField, Zero};
use ark_poly::UVPolynomial;
use ark_poly_commit::{
    LabeledCommitment, LabeledPolynomial, PCCommitment, PolynomialCommitment, QuerySet,
};
use ark_std::rand::RngCore;
use itertools::Itertools;
use std::ops::Mul;

use crate::rng::FiatShamirRng;
pub use crate::rng::SimpleHashFiatShamirRng;

pub use crate::error::*;
use crate::VectorLookup;
use std::marker::PhantomData;

pub fn lc_comms<
    F: FftField,
    E: PairingEngine<Fr = F>,
    PC: PolynomialCommitment<
        F,
        DensePolynomial<F>,
        Commitment = ark_poly_commit::marlin_pc::Commitment<E>,
    >,
>(
    coms: &[LabeledCommitment<PC::Commitment>],
    coeffs: &[F],
) -> LabeledCommitment<PC::Commitment> {
    let mut com = coms[0].commitment().comm.clone();
    for i in 1..coms.len() {
        com += (coeffs[i], &coms[i].commitment().comm);
    }
    let mut temp = ark_poly_commit::marlin_pc::Commitment::<E>::empty();
    temp.comm = com;
    temp.shifted_comm = None; // TODO: do we need a degree bound?
    LabeledCommitment::new("combination".to_string(), temp, None)
}

pub fn consecutive_sum<F: FftField>(vec: &[F]) -> Vec<F> {
    let mut xs = vec.iter();
    let vs =
        std::iter::successors(Some(F::zero()), |acc| xs.next().map(|n| *n + *acc)).take(vec.len());
    vs.collect::<Vec<F>>()
}

pub fn compute_denoms<F: FftField>(denominator: &[F], alpha: F) -> Vec<F> {
    let mut invs = denominator.iter().map(|x| *x + alpha).collect::<Vec<F>>();
    batch_inversion(&mut invs);
    invs
}

pub fn compute_terms<F: FftField>(numerator: Option<&[F]>, denominator: &[F], alpha: F) -> Vec<F> {
    let denoms = compute_denoms(denominator, alpha);
    match numerator {
        Some(nums) => {
            assert!(nums.len() == denoms.len());
            denoms
                .iter()
                .zip(nums.iter())
                .map(|(denom, num)| *denom * num)
                .collect::<Vec<F>>()
        }
        None => denoms,
    }
}

pub fn compute_statement_polys<F: FftField>(
    fs: &[F],
    m: usize,
    V: Radix2EvaluationDomain<F>,
) -> Vec<DensePolynomial<F>> {
    let mods = (0..m).cycle();
    let fs = mods.clone().zip(fs.iter().map(|e| *e)).into_group_map();
    let mut f_polys = vec![];
    for i in 0..m {
        let fi = Evaluations::from_vec_and_domain(fs[&i].clone(), V).interpolate();
        f_polys.push(fi);
    }
    f_polys
}

pub fn compute_round_1<F: FftField>(
    fs: &[F],
    ts: &[F],
    beta: F,
    m: usize,
) -> (Vec<F>, Vec<F>, Vec<F>) {
    let n = fs.len() / m;
    let d = ts.len() / m;
    let beta_pows = std::iter::successors(Some(F::one()), |n| Some(*n * beta))
        .take(m)
        .collect::<Vec<F>>();
    let mut f_vec = vec![F::zero(); n];
    let mut t_vec = vec![F::zero(); d];

    for i in 0..n {
        for j in 0..m {
            f_vec[i] += beta_pows[j] * fs[i * m + j];
        }
    }
    for i in 0..d {
        for j in 0..m {
            t_vec[i] += beta_pows[j] * ts[i * m + j];
        }
    }
    let counts = f_vec.iter().counts();
    let c_vec = t_vec
        .iter()
        .map(|t| F::from(*counts.get(t).unwrap_or(&0) as u64))
        .collect::<Vec<F>>();
    (f_vec, t_vec, c_vec)
}

pub fn compute_round_2_polys<F: FftField>(
    f_vec: &[F],
    t_vec: &[F],
    c_vec: &[F],
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (DensePolynomial<F>, DensePolynomial<F>, DensePolynomial<F>) {
    let f = Evaluations::from_vec_and_domain(f_vec.to_vec(), V).interpolate();
    let t = Evaluations::from_vec_and_domain(t_vec.to_vec(), H).interpolate();
    let c = Evaluations::from_vec_and_domain(c_vec.to_vec(), H).interpolate();
    (f, t, c)
}

pub fn compute_round_3_polys<F: FftField>(
    f_vec: &[F],
    t_vec: &[F],
    c_vec: &[F],
    alpha: F,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
    F,
) {
    let f_terms = compute_terms(None, &f_vec, alpha);
    let t_terms = compute_terms(Some(&c_vec), &t_vec, alpha);

    let sum: F = f_terms.iter().sum();

    let f_shift = sum / F::from(V.size() as u64);
    let t_shift = sum / F::from(H.size() as u64);
    let shifted_f_terms = f_terms.iter().map(|x| *x - f_shift).collect::<Vec<F>>();
    let shifted_t_terms = t_terms.iter().map(|x| *x - t_shift).collect::<Vec<F>>();
    let mut s_f_vec = consecutive_sum(&shifted_f_terms);
    let mut s_t_vec = consecutive_sum(&shifted_t_terms);

    let f_hab = Evaluations::from_vec_and_domain(f_terms, V).interpolate();
    let t_hab = Evaluations::from_vec_and_domain(t_terms, H).interpolate();
    let s_f = Evaluations::from_vec_and_domain(s_f_vec.clone(), V).interpolate();
    let s_t = Evaluations::from_vec_and_domain(s_t_vec.clone(), H).interpolate();
    s_f_vec.rotate_left(1);
    s_t_vec.rotate_left(1);
    let s_f_rot = Evaluations::from_vec_and_domain(s_f_vec, V).interpolate();
    let s_t_rot = Evaluations::from_vec_and_domain(s_t_vec, H).interpolate();
    (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum)
}

pub fn compute_round_4_polys<F: FftField>(
    f: &DensePolynomial<F>,
    t: &DensePolynomial<F>,
    c: &DensePolynomial<F>,
    f_hab: &DensePolynomial<F>,
    t_hab: &DensePolynomial<F>,
    s_f: &DensePolynomial<F>,
    s_t: &DensePolynomial<F>,
    s_f_rot: &DensePolynomial<F>,
    s_t_rot: &DensePolynomial<F>,
    sum: F,
    alpha: F,
    zeta: F,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
) -> (DensePolynomial<F>, DensePolynomial<F>) {
    let one_poly = DensePolynomial::from_coefficients_vec(vec![F::one()]);
    let alpha_poly = DensePolynomial::from_coefficients_vec(vec![alpha]);
    let s_n_poly = DensePolynomial::from_coefficients_vec(vec![sum / F::from(V.size() as u64)]);
    let s_d_poly = DensePolynomial::from_coefficients_vec(vec![sum / F::from(H.size() as u64)]);
    let zt_V_1 = &(&(f + &alpha_poly) * f_hab) - &one_poly;
    let zt_V_2 = &(s_f + f_hab) - &(s_f_rot + &s_n_poly);
    let zt_V = &zt_V_1 + (&zt_V_2.mul(zeta));
    let zt_H_1 = &(&(t + &alpha_poly) * t_hab) - c;
    let zt_H_2 = &(s_t + t_hab) - &(s_t_rot + &s_d_poly);
    let zt_H = &zt_H_1 + (&zt_H_2.mul(zeta));

    let (q_V, r_V) = zt_V.divide_by_vanishing_poly(V).unwrap();
    let (q_H, r_H) = zt_H.divide_by_vanishing_poly(H).unwrap();

    assert!(zt_V_1.divide_by_vanishing_poly(V).unwrap().1.is_zero());
    assert!(zt_H_1.divide_by_vanishing_poly(H).unwrap().1.is_zero());
    assert!(zt_V_2.divide_by_vanishing_poly(V).unwrap().1.is_zero());
    assert!(zt_H_2.divide_by_vanishing_poly(H).unwrap().1.is_zero());
    assert!(r_V.is_zero());
    assert!(r_H.is_zero());
    (q_V, q_H)
}

pub struct NaiveLookup<F: FftField, PC, FS: FiatShamirRng, E: PairingEngine<Fr = F>>
where
    PC: PolynomialCommitment<
        F,
        DensePolynomial<F>,
        Commitment = ark_poly_commit::marlin_pc::Commitment<E>,
    >,
{
    _f: PhantomData<F>,
    _pc: PhantomData<PC>,
    _fs: PhantomData<FS>,
}

#[derive(Clone)]
pub struct NaivePK<F: FftField, P: Clone> {
    vector_size: usize,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
    pc_pk: P,
}

#[derive(Clone)]
pub struct NaiveVK<F: FftField, V: Clone> {
    vector_size: usize,
    V: Radix2EvaluationDomain<F>,
    H: Radix2EvaluationDomain<F>,
    pc_vk: V,
}

#[derive(Clone)]
pub struct NaivePF<F: FftField, C, P>
where
    C: Clone,
    P: Clone,
{
    comms: C,
    evals: ark_poly_commit::Evaluations<F, F>,
    proof: P,
    sum: F,
}

impl<F: FftField, PC, FS: FiatShamirRng, E: PairingEngine<Fr = F>> VectorLookup<F>
    for NaiveLookup<F, PC, FS, E>
where
    PC: PolynomialCommitment<
        F,
        DensePolynomial<F>,
        Commitment = ark_poly_commit::marlin_pc::Commitment<E>,
    >,
    PC::CommitterKey: Clone,
    PC::VerifierKey: Clone,
{
    type Error = PC::Error;
    type VectorCommitment = (
        Vec<LabeledCommitment<PC::Commitment>>,
        Vec<<PC as PolynomialCommitment<F, DensePolynomial<F>>>::Randomness>,
    );
    type VectorRepr = ();
    type UniversalSRS = PC::UniversalParams;
    type ProverKey = NaivePK<F, PC::CommitterKey>;
    type VerifierKey = NaiveVK<F, PC::VerifierKey>;
    type Proof = NaivePF<F, Self::VectorCommitment, PC::BatchProof>;

    fn universal_setup<R: RngCore>(
        size: usize,
        rng: &mut R,
    ) -> Result<Self::UniversalSRS, Self::Error> {
        let srs = PC::setup(size, None, rng)?;
        Ok(srs)
    }

    fn index(
        srs: &Self::UniversalSRS,
        vector_size: usize,
        lookup_size: usize,
        table_size: usize,
    ) -> Result<(Self::ProverKey, Self::VerifierKey), Self::Error> {
        let trim_size = std::cmp::max(lookup_size, table_size) * vector_size;
        let (pk, vk) = PC::trim(srs, trim_size, 1, None)?;
        Ok((
            NaivePK {
                vector_size,
                V: Radix2EvaluationDomain::<F>::new(lookup_size).unwrap(),
                H: Radix2EvaluationDomain::<F>::new(table_size).unwrap(),
                pc_pk: pk,
            },
            NaiveVK {
                vector_size,
                V: Radix2EvaluationDomain::<F>::new(lookup_size).unwrap(),
                H: Radix2EvaluationDomain::<F>::new(table_size).unwrap(),
                pc_vk: vk,
            },
        ))
    }

    fn commit_lookup(
        pk: &Self::ProverKey,
        f_vals: Vec<F>,
    ) -> Result<(Self::VectorCommitment, Self::VectorRepr), Self::Error> {
        let fs_polys = compute_statement_polys(&f_vals, pk.vector_size, pk.V.clone());
        let labeledpolys = fs_polys
            .iter()
            .enumerate()
            .map(|(i, f)| LabeledPolynomial::new(format!("f{}", i), f.clone(), None, None))
            .collect::<Vec<_>>();
        let comms = PC::commit(&pk.pc_pk, &labeledpolys, None)?;
        Ok((comms, ()))
    }

    fn commit_table(
        pk: &Self::ProverKey,
        t_vals: Vec<F>,
    ) -> Result<(Self::VectorCommitment, Self::VectorRepr), Self::Error> {
        let ts_polys = compute_statement_polys(&t_vals, pk.vector_size, pk.H.clone());
        let labeledpolys = ts_polys
            .iter()
            .enumerate()
            .map(|(i, t)| LabeledPolynomial::new(format!("t{}", i), t.clone(), None, None))
            .collect::<Vec<_>>();
        let comms = PC::commit(&pk.pc_pk, &labeledpolys, None)?;
        Ok((comms, ()))
    }

    fn prove(
        pk: &Self::ProverKey,
        _f_comm: &Self::VectorCommitment,
        _t_comm: &Self::VectorCommitment,
        f_vals: Vec<F>,
        t_vals: Vec<F>,
        _f: Self::VectorRepr,
        _t: Self::VectorRepr,
    ) -> Result<Self::Proof, Self::Error> {
        let mut fs_rng = FS::initialize(b"naiveLC");
        let beta = F::rand(&mut fs_rng);
        let (f_vec, t_vec, c_vec) = compute_round_1(&f_vals[..], &t_vals[..], beta, pk.vector_size);

        let (f, t, c) = compute_round_2_polys(&f_vec, &t_vec, &c_vec, pk.V.clone(), pk.H.clone());
        let f_labeled = LabeledPolynomial::new("f".to_string(), f.clone(), None, None);
        let t_labeled = LabeledPolynomial::new("t".to_string(), t.clone(), None, None);
        let c_labeled = LabeledPolynomial::new("c".to_string(), c.clone(), None, None);

        let alpha = F::rand(&mut fs_rng);

        let (f_hab, t_hab, s_f, s_t, s_f_rot, s_t_rot, sum) =
            compute_round_3_polys(&f_vec, &t_vec, &c_vec, alpha, pk.V.clone(), pk.H.clone());
        let f_hab_labeled = LabeledPolynomial::new("f_hab".to_string(), f_hab.clone(), None, None);
        let t_hab_labeled = LabeledPolynomial::new("t_hab".to_string(), t_hab.clone(), None, None);
        let s_f_labeled = LabeledPolynomial::new("s_f".to_string(), s_f.clone(), None, None);
        let s_t_labeled = LabeledPolynomial::new("s_t".to_string(), s_t.clone(), None, None);

        let zeta = F::rand(&mut fs_rng);
        let (q_V, q_H) = compute_round_4_polys(
            &f,
            &t,
            &c,
            &f_hab,
            &t_hab,
            &s_f,
            &s_t,
            &s_f_rot,
            &s_t_rot,
            sum,
            alpha,
            zeta,
            pk.V.clone(),
            pk.H.clone(),
        );
        let q_V_labeled = LabeledPolynomial::new("q_V".to_string(), q_V.clone(), None, None);
        let q_H_labeled = LabeledPolynomial::new("q_H".to_string(), q_H.clone(), None, None);

        let labeled_polys = vec![
            f_labeled,
            t_labeled,
            c_labeled,
            f_hab_labeled,
            t_hab_labeled,
            s_f_labeled,
            s_t_labeled,
            q_V_labeled,
            q_H_labeled,
        ];

        let z = F::rand(&mut fs_rng);
        let omega_z = z * pk.V.group_gen;
        let gamma_z = z * pk.H.group_gen;

        let batch_chall = F::rand(&mut fs_rng);

        let comms = PC::commit(&pk.pc_pk, &labeled_polys, None)?;

        let query_set = Self::get_query_set(z, omega_z, gamma_z);
        let mut evaluations = ark_poly_commit::Evaluations::new();
        evaluations.insert(("c".to_string(), z), c.evaluate(&z));
        evaluations.insert(("f".to_string(), z), f.evaluate(&z));
        evaluations.insert(("t".to_string(), z), t.evaluate(&z));
        evaluations.insert(("f_hab".to_string(), z), f_hab.evaluate(&z));
        evaluations.insert(("t_hab".to_string(), z), t_hab.evaluate(&z));
        evaluations.insert(("s_f".to_string(), z), s_f.evaluate(&z));
        evaluations.insert(("s_t".to_string(), z), s_t.evaluate(&z));
        evaluations.insert(("s_f".to_string(), omega_z), s_f.evaluate(&omega_z));
        evaluations.insert(("s_t".to_string(), gamma_z), s_t.evaluate(&gamma_z));
        evaluations.insert(("q_V".to_string(), z), q_V.evaluate(&z));
        evaluations.insert(("q_H".to_string(), z), q_H.evaluate(&z));

        let batch_proof = PC::batch_open(
            &pk.pc_pk,
            &labeled_polys, // all the polys, including the quotient polynomials (no rotated)
            &comms.0,       // same as polys but commitments
            &query_set,     // all query points and polynomials
            batch_chall,    // from f-s
            &comms.1,       // same as polys but comm rands
            Some(&mut fs_rng),
        )?;

        let proof = Self::Proof {
            comms,
            evals: evaluations,
            proof: batch_proof,
            sum,
        };
        Ok(proof)
    }

    fn verify(
        vk: &Self::VerifierKey,
        proof: &Self::Proof,
        f_comm: &Self::VectorCommitment,
        t_comm: &Self::VectorCommitment,
    ) -> Result<bool, Self::Error> {
        let mut fs_rng = FS::initialize(b"naiveLC");
        let beta = F::rand(&mut fs_rng);

        let m = vk.vector_size;
        let beta_pows = std::iter::successors(Some(F::one()), |n| Some(*n * beta))
            .take(m)
            .collect::<Vec<F>>();

        let _ = lc_comms::<F, E, PC>(&f_comm.0, &beta_pows);
        let _ = lc_comms::<F, E, PC>(&t_comm.0, &beta_pows);

        let alpha = F::rand(&mut fs_rng);
        let zeta = F::rand(&mut fs_rng);
        let z = F::rand(&mut fs_rng);
        let batch_chall = F::rand(&mut fs_rng);

        let query_set = Self::get_query_set(z, z * vk.V.group_gen, z * vk.H.group_gen);
        let mut result = PC::batch_check(
            &vk.pc_vk,
            &proof.comms.0,
            &query_set,
            &proof.evals,
            &proof.proof,
            batch_chall,
            &mut fs_rng,
        )?;

        let c_z = proof.evals.get(&("c".to_string(), z)).unwrap();
        let f_z = proof.evals.get(&("f".to_string(), z)).unwrap();
        let t_z = proof.evals.get(&("t".to_string(), z)).unwrap();
        let f_hab_z = proof.evals.get(&("f_hab".to_string(), z)).unwrap();
        let t_hab_z = proof.evals.get(&("t_hab".to_string(), z)).unwrap();
        let s_f_z = proof.evals.get(&("s_f".to_string(), z)).unwrap();
        let s_t_z = proof.evals.get(&("s_t".to_string(), z)).unwrap();
        let s_f_omega_z = proof
            .evals
            .get(&("s_f".to_string(), z * vk.V.group_gen))
            .unwrap();
        let s_t_gamma_z = proof
            .evals
            .get(&("s_t".to_string(), z * vk.H.group_gen))
            .unwrap();
        let q_V_z = proof.evals.get(&("q_V".to_string(), z)).unwrap();
        let q_H_z = proof.evals.get(&("q_H".to_string(), z)).unwrap();
        let V_z = vk.V.evaluate_vanishing_polynomial(z);
        let H_z = vk.H.evaluate_vanishing_polynomial(z);
        let s_n = proof.sum / F::from(vk.V.size() as u64);
        let s_d = proof.sum / F::from(vk.H.size() as u64);

        result &= *q_V_z
            == ((*f_hab_z * (alpha + f_z) - F::one())
                + zeta * (*s_f_z + f_hab_z - s_f_omega_z - s_n))
                / V_z;
        result &= *q_H_z
            == ((*t_hab_z * (alpha + t_z) - c_z) + zeta * (*s_t_z + t_hab_z - s_t_gamma_z - s_d))
                / H_z;

        Ok(result)
    }
}

impl<F: FftField, PC, FS: FiatShamirRng, E: PairingEngine<Fr = F>> NaiveLookup<F, PC, FS, E>
where
    PC: PolynomialCommitment<
        F,
        DensePolynomial<F>,
        Commitment = ark_poly_commit::marlin_pc::Commitment<E>,
    >,
{
    pub fn get_query_set(z: F, omega_z: F, gamma_z: F) -> QuerySet<F> {
        let mut query_set = QuerySet::new();
        query_set.insert(("c".to_string(), ("z".to_string(), z)));
        query_set.insert(("f".to_string(), ("z".to_string(), z)));
        query_set.insert(("t".to_string(), ("z".to_string(), z)));
        query_set.insert(("f_hab".to_string(), ("z".to_string(), z)));
        query_set.insert(("t_hab".to_string(), ("z".to_string(), z)));
        query_set.insert(("s_f".to_string(), ("z".to_string(), z)));
        query_set.insert(("s_t".to_string(), ("z".to_string(), z)));
        query_set.insert(("s_f".to_string(), ("omega_z".to_string(), omega_z)));
        query_set.insert(("s_t".to_string(), ("gamma_z".to_string(), gamma_z)));
        query_set.insert(("q_V".to_string(), ("z".to_string(), z)));
        query_set.insert(("q_H".to_string(), ("z".to_string(), z)));
        query_set
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;

    #[test]
    fn round_1() {
        let fs = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
        ];
        let ts = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
            Fr::from(5),
            Fr::from(6),
            Fr::from(7),
            Fr::from(8),
        ];
        let beta = Fr::from(7 as u64);
        let (f_vec, t_vec, c_vec) = compute_round_1(&fs, &ts, beta, 2);
        assert_eq!(
            f_vec,
            vec![
                Fr::from(1 + 2 * 7),
                Fr::from(1 + 2 * 7),
                Fr::from(1 + 2 * 7),
                Fr::from(3 + 4 * 7)
            ]
        );
        assert_eq!(t_vec, vec![Fr::from(1 + 2 * 7), Fr::from(3 + 4 * 7)]);
        assert_eq!(c_vec, vec![Fr::from(3), Fr::from(1)]);
    }

    #[test]
    fn test_lookup() {
        use ark_bls12_381::{Bls12_381, Fr};
        use ark_poly_commit::marlin_pc::MarlinKZG10;
        use blake2::Blake2s;
        use rand_chacha::ChaChaRng;
        type PC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;
        type FS = SimpleHashFiatShamirRng<Blake2s, ChaChaRng>;
        type NaiveInst = NaiveLookup<Fr, PC, FS, Bls12_381>;

        let f_evals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
        ];
        let t_evals = vec![
            Fr::from(1),
            Fr::from(2),
            Fr::from(3),
            Fr::from(4),
            Fr::from(5),
            Fr::from(6),
            Fr::from(7),
            Fr::from(8),
        ];
        let vector_size = 4;
        let lookup_size = f_evals.len() / vector_size;
        let table_size = t_evals.len() / vector_size;
        let srs = NaiveInst::universal_setup(16, &mut ark_std::test_rng()).unwrap();
        let (pk, vk) = NaiveInst::index(&srs, vector_size, lookup_size, table_size).unwrap();
        let (f_comm, _) = NaiveInst::commit_lookup(&pk, f_evals.clone()).unwrap();
        let (t_comm, _) = NaiveInst::commit_table(&pk, t_evals.clone()).unwrap();
        let proof = NaiveInst::prove(&pk, &f_comm, &t_comm, f_evals, t_evals, (), ()).unwrap();
        let result = NaiveInst::verify(&vk, &proof, &f_comm, &t_comm).unwrap();
        assert!(result);
    }
}
