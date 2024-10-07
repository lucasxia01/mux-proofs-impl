use ark_ff::Field;
use ark_std::rand::RngCore;

use std::fmt::Debug;

pub mod error;
pub mod rng;

// Implementation of CosetLookup vector lookup
pub mod coset_lookup;

// Implementation of naive linear combination vector lookup
pub mod naive;

#[cfg(test)]
pub mod test;

pub trait VectorLookup<F: Field> {
    type Error: Debug;
    type VectorCommitment: Clone;
    type VectorCommitmentRandomness: Clone;
    type VectorRepr: Clone;
    type UniversalSRS: Clone;
    type ProverKey;
    type VerifierKey;
    type Proof;

    /// Generate the one time universal SRS
    fn universal_setup<R: RngCore>(
        size: usize,
        rng: &mut R,
    ) -> Result<Self::UniversalSRS, Self::Error>;

    /// Generate the prover and verifier keys specific to vector-size, lookup-size, table-size
    /// Prover key and verifier key should contain information about size parameters
    fn index(
        srs: &Self::UniversalSRS,
        vector_size: usize,
        lookup_size: usize,
        table_size: usize,
    ) -> Result<(Self::ProverKey, Self::VerifierKey), Self::Error>;

    /// Given fields values and prover key, generate vector commitment and representation for lookup
    fn commit_lookup<R: RngCore>(
        pk: &Self::ProverKey,
        f_vals: Vec<F>,
        rng: &mut R,
    ) -> Result<((Self::VectorCommitment, Self::VectorCommitmentRandomness), Self::VectorRepr), Self::Error>;

    /// Given fields values and prover key, generate vector commitment and representation for table
    fn commit_table<R: RngCore>(
        pk: &Self::ProverKey,
        t_vals: Vec<F>,
        rng:  &mut R,
    ) -> Result<((Self::VectorCommitment, Self::VectorCommitmentRandomness), Self::VectorRepr), Self::Error>;

    /// Perform vector lookup and produce proof
    fn prove<R: RngCore>(
        pk: &Self::ProverKey,
        f_comm_pair: &(Self::VectorCommitment, Self::VectorCommitmentRandomness),
        t_comm_pair: &(Self::VectorCommitment, Self::VectorCommitmentRandomness),
        f_vals: Vec<F>,
        t_vals: Vec<F>,
        f: Self::VectorRepr,
        t: Self::VectorRepr,
        rng:  &mut R,
    ) -> Result<Self::Proof, Self::Error>;

    /// Perform verification of vector lookup proof
    fn verify(
        vk: &Self::VerifierKey,
        proof: &Self::Proof,
        f_comm: &Self::VectorCommitment,
        t_comm: &Self::VectorCommitment,
    ) -> Result<bool, Self::Error>;
}
