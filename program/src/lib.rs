//! Hash instruction bytes and return 32 output bytes. No accounts.

use solana_account_info::AccountInfo;
use solana_cpi::set_return_data;
use solana_program_entrypoint::entrypoint;
use solana_program_error::{ProgramError, ProgramResult};
use solana_pubkey::Pubkey;
use solana_shake::{Shake128, Shake256, TurboShake128, TurboShake256};

entrypoint!(process_instruction);

// [tag: 1][message]. Tags 0..3 use hash; 4..7 use hashv over two halves.
fn process_instruction(_: &Pubkey, _: &[AccountInfo], data: &[u8]) -> ProgramResult {
    let (&tag, data) = data
        .split_first()
        .ok_or(ProgramError::InvalidInstructionData)?;
    let (left, right) = data.split_at(data.len() / 2);
    let output = match tag {
        0 => Shake128::hash::<32>(data),
        1 => Shake256::hash::<32>(data),
        2 => TurboShake128::hash::<32, 0x1f>(data),
        3 => TurboShake256::hash::<32, 0x1f>(data),
        4 => Shake128::hashv::<32>(&[left, right]),
        5 => Shake256::hashv::<32>(&[left, right]),
        6 => TurboShake128::hashv::<32, 0x1f>(&[left, right]),
        7 => TurboShake256::hashv::<32, 0x1f>(&[left, right]),
        _ => return Err(ProgramError::InvalidInstructionData),
    };
    set_return_data(&output);
    Ok(())
}
