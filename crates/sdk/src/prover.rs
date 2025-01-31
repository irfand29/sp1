//! # SP1 Prover Trait
//!
//! A trait that each prover variant must implement.

use std::borrow::Borrow;

use anyhow::Result;
use itertools::Itertools;
use p3_field::PrimeField32;
use sp1_core_executor::{ExecutionReport, SP1Context};
use sp1_core_machine::io::SP1Stdin;
use sp1_primitives::io::SP1PublicValues;
use sp1_prover::{
    components::SP1ProverComponents, CoreSC, InnerSC, SP1CoreProofData, SP1Prover, SP1ProvingKey,
    SP1VerifyingKey, SP1_CIRCUIT_VERSION,
};
use sp1_stark::{air::PublicValues, MachineVerificationError, Word};
use thiserror::Error;

use crate::install::try_install_circuit_artifacts;
use crate::{SP1Proof, SP1ProofMode, SP1ProofWithPublicValues};

/// A basic set of primitives that each prover variant must implement.
pub trait Prover<C: SP1ProverComponents>: Send + Sync {
    /// The inner [`SP1Prover`] struct used by the prover.
    fn inner(&self) -> &SP1Prover<C>;

    /// The version of the current SP1 circuit.
    fn version(&self) -> &str {
        SP1_CIRCUIT_VERSION
    }

    /// Generate the proving and verifying keys for the given program.
    fn setup(&self, elf: &[u8]) -> (SP1ProvingKey, SP1VerifyingKey);

    /// Executes the program on the given input.
    fn execute(&self, elf: &[u8], stdin: &SP1Stdin) -> Result<(SP1PublicValues, ExecutionReport)> {
        Ok(self.inner().execute(elf, stdin, SP1Context::default())?)
    }

    /// Proves the given program on the given input in the given proof mode.
    fn prove(
        &self,
        pk: &SP1ProvingKey,
        stdin: &SP1Stdin,
        mode: SP1ProofMode,
    ) -> Result<SP1ProofWithPublicValues>;

    /// Verify that an SP1 proof is valid given its vkey and metadata.
    fn verify(
        &self,
        bundle: &SP1ProofWithPublicValues,
        vkey: &SP1VerifyingKey,
    ) -> Result<(), SP1VerificationError> {
        verify_proof(self.inner(), self.version(), bundle, vkey)
    }
}

/// In-memory prover implementation
#[cfg(feature = "in_memory")]
pub struct InMemoryProver<C: SP1ProverComponents> {
    inner: SP1Prover<C>,
}

#[cfg(feature = "in_memory")]
impl<C: SP1ProverComponents> Prover<C> for InMemoryProver<C> {
    fn inner(&self) -> &SP1Prover<C> {
        &self.inner
    }

    fn setup(&self, elf: &[u8]) -> (SP1ProvingKey, SP1VerifyingKey) {
        SP1Prover::core_setup(elf)
    }

    fn prove(
        &self,
        pk: &SP1ProvingKey,
        stdin: &SP1Stdin,
        mode: SP1ProofMode,
    ) -> Result<SP1ProofWithPublicValues> {
        match mode {
            SP1ProofMode::Compressed => {
                let proof = self.inner.prove_compressed(pk, stdin)?;
                Ok(SP1ProofWithPublicValues {
                    proof: SP1Proof::Compressed(proof),
                    public_values: self.inner.get_public_values(),
                    sp1_version: SP1_CIRCUIT_VERSION.to_string(),
                })
            }
            _ => anyhow::bail!("In-memory prover only supports compressed proofs"),
        }
    }
}

/// Docker-based prover implementation (existing)
#[cfg(feature = "docker")]
pub struct DockerProver<C: SP1ProverComponents> {
    inner: SP1Prover<C>,
}

#[cfg(feature = "docker")]
impl<C: SP1ProverComponents> Prover<C> for DockerProver<C> {
    fn inner(&self) -> &SP1Prover<C> {
        &self.inner
    }

    fn setup(&self, elf: &[u8]) -> (SP1ProvingKey, SP1VerifyingKey) {
        SP1Prover::docker_setup(elf)
    }

    fn prove(
        &self,
        pk: &SP1ProvingKey,
        stdin: &SP1Stdin,
        mode: SP1ProofMode,
    ) -> Result<SP1ProofWithPublicValues> {
        self.inner.prove(pk, stdin, mode)
    }
}

/// Error and verification implementations remain unchanged below...

#[derive(Error, Debug)]
pub enum SP1VerificationError {
    #[error("Invalid public values")]
    InvalidPublicValues,
    #[error("Version mismatch")]
    VersionMismatch(String),
    #[error("Core machine verification error: {0}")]
    Core(MachineVerificationError<CoreSC>),
    #[error("Recursion verification error: {0}")]
    Recursion(MachineVerificationError<InnerSC>),
    #[error("Plonk verification error: {0}")]
    Plonk(anyhow::Error),
    #[error("Groth16 verification error: {0}")]
    Groth16(anyhow::Error),
}

pub(crate) fn verify_proof<C: SP1ProverComponents>(
    prover: &SP1Prover<C>,
    version: &str,
    bundle: &SP1ProofWithPublicValues,
    vkey: &SP1VerifyingKey,
) -> Result<(), SP1VerificationError> {
    if bundle.sp1_version != version {
        return Err(SP1VerificationError::VersionMismatch(bundle.sp1_version.clone()));
    }

    match &bundle.proof {
        SP1Proof::Core(proof) => {
            let public_values: &PublicValues<Word<_>, _> =
                proof.last().unwrap().public_values.as_slice().borrow();

            let committed_value_digest_bytes = public_values
                .committed_value_digest
                .iter()
                .flat_map(|w| w.0.iter().map(|x| x.as_canonical_u32() as u8))
                .collect_vec();

            for (a, b) in committed_value_digest_bytes.iter().zip_eq(bundle.public_values.hash()) {
                if *a != b {
                    return Err(SP1VerificationError::InvalidPublicValues);
                }
            }

            prover
                .verify(&SP1CoreProofData(proof.clone()), vkey)
                .map_err(SP1VerificationError::Core)
        }
        SP1Proof::Compressed(proof) => {
            let public_values: &PublicValues<Word<_>, _> =
                proof.proof.public_values.as_slice().borrow();

            let committed_value_digest_bytes = public_values
                .committed_value_digest
                .iter()
                .flat_map(|w| w.0.iter().map(|x| x.as_canonical_u32() as u8))
                .collect_vec();

            for (a, b) in committed_value_digest_bytes.iter().zip_eq(bundle.public_values.hash()) {
                if *a != b {
                    return Err(SP1VerificationError::InvalidPublicValues);
                }
            }

            prover.verify_compressed(proof, vkey).map_err(SP1VerificationError::Recursion)
        }
        SP1Proof::Plonk(proof) => prover
            .verify_plonk_bn254(
                proof,
                vkey,
                &bundle.public_values,
                &if sp1_prover::build::sp1_dev_mode() {
                    sp1_prover::build::plonk_bn254_artifacts_dev_dir()
                } else {
                    try_install_circuit_artifacts("plonk")
                },
            )
            .map_err(SP1VerificationError::Plonk),
        SP1Proof::Groth16(proof) => prover
            .verify_groth16_bn254(
                proof,
                vkey,
                &bundle.public_values,
                &if sp1_prover::build::sp1_dev_mode() {
                    sp1_prover::build::groth16_bn254_artifacts_dev_dir()
                } else {
                    try_install_circuit_artifacts("groth16")
                },
            )
            .map_err(SP1VerificationError::Groth16),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sp1_prover::components::CpuProverComponents;

    #[cfg(feature = "in_memory")]
    #[test]
    fn test_in_memory_prover() {
        let prover = InMemoryProver::<CpuProverComponents> {
            inner: SP1Prover::new()
        };
        let elf = include_bytes!("../../examples/fibonacci/program/elf/riscv32im-succinct-zkvm-elf");
        let (pk, vk) = prover.setup(elf);
        let mut stdin = SP1Stdin::new();
        stdin.write(&10u32);
        let proof = prover.prove(&pk, &stdin, SP1ProofMode::Compressed).unwrap();
        prover.verify(&proof, &vk).unwrap();
    }

    #[cfg(feature = "in_memory")]
    #[test]
    fn test_in_memory_unsupported_mode() {
        let prover = InMemoryProver::<CpuProverComponents> {
            inner: SP1Prover::new()
        };
        let elf = include_bytes!("../../examples/fibonacci/program/elf/riscv32im-succinct-zkvm-elf");
        let (pk, _) = prover.setup(elf);
        let stdin = SP1Stdin::new();
        let result = prover.prove(&pk, &stdin, SP1ProofMode::Plonk);
        assert!(result.is_err());
    }

    #[cfg(feature = "docker")]
    #[test]
    fn test_docker_prover() {
        let prover = DockerProver::<CpuProverComponents> {
            inner: SP1Prover::new()
        };
        // ... existing docker tests ...
    }
}
