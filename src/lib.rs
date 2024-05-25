use ark_std::rand::RngCore;
use ark_ff::{Field};

pub mod error;
pub mod rng;

// Implementation of CosetLookup vector lookup
pub mod coset_lookup;

// Implementation of naive linear combination vector lookup
//pub mod naive_lc

pub trait VectorLookup<F: Field> {
    type Error;
    type VectorCommitment: Clone;
    type VectorRepr: Clone;
    type UniversalSRS: Clone;
    type ProverKey: Clone;
    type VerifierKey: Clone;
    type Proof: Clone;

    /// Generate the one time universal SRS
    fn universal_setup<R: RngCore>(
        size: usize,
        rng: &mut R,
    ) -> Result<Self::UniversalSRS, Self::Error>;

    /// Generate the prover and verifier keys specific to vector-size, lookup-size, table-size
    fn index(
        srs: &Self::UniversalSRS,
        vector_size: usize,
        lookup_size: usize,
        table_size: usize,
    ) -> Result<(Self::ProverKey, Self::VerifierKey), Self::Error>; 

    /// Perform vector lookup and produce proof
    fn prove(
        pk: &Self::ProverKey,
        f_comm: &Self::VectorCommitment,
        t_comm: &Self::VectorCommitment,
        f_vals: Vec<F>,
        t_vals: Vec<F>,
        f: Self::VectorRepr,
        t: Self::VectorRepr,
        vector_size: usize,
        lookup_size: usize,
        table_size: usize,
    ) -> Result<Self::Proof, Self::Error>;

    /// Perform verification of vector lookup proof
    fn verify(
        vk: &Self::VerifierKey,
        proof: &Self::Proof,
        f_comm: &Self::VectorCommitment,
        t_comm: &Self::VectorCommitment,
        vector_size: usize,
        lookup_size: usize,
        table_size: usize,
    ) -> Result<bool, Self::Error>;
}
