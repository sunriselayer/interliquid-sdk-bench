use sp1_sdk::{include_elf, HashableKey, Prover, ProverClient};

/// The ELF (executable and linkable format) file for the Succinct RISC-V zkVM.
pub const COMMIT_STATE_ELF: &[u8] = include_elf!("commit-state-program");

fn main() {
    let prover = ProverClient::builder().cpu().build();
    let (_, vk) = prover.setup(COMMIT_STATE_ELF);
    println!("{}", vk.bytes32());
}
