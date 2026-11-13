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
    match tag {
        0 => shake128_hash(data),
        1 => shake256_hash(data),
        2 => turboshake128_hash(data),
        3 => turboshake256_hash(data),
        4 => shake128_hashv(data),
        5 => shake256_hashv(data),
        6 => turboshake128_hashv(data),
        7 => turboshake256_hashv(data),
        _ => Err(ProgramError::InvalidInstructionData),
    }
}

fn shake128_hash(data: &[u8]) -> ProgramResult {
    set_return_data(&Shake128::hash::<32>(data));
    Ok(())
}

fn shake256_hash(data: &[u8]) -> ProgramResult {
    set_return_data(&Shake256::hash::<32>(data));
    Ok(())
}

fn turboshake128_hash(data: &[u8]) -> ProgramResult {
    set_return_data(&TurboShake128::hash::<32, 0x1f>(data));
    Ok(())
}

fn turboshake256_hash(data: &[u8]) -> ProgramResult {
    set_return_data(&TurboShake256::hash::<32, 0x1f>(data));
    Ok(())
}

fn shake128_hashv(data: &[u8]) -> ProgramResult {
    let (left, right) = data.split_at(data.len() / 2);
    set_return_data(&Shake128::hashv::<32>(&[left, right]));
    Ok(())
}

fn shake256_hashv(data: &[u8]) -> ProgramResult {
    let (left, right) = data.split_at(data.len() / 2);
    set_return_data(&Shake256::hashv::<32>(&[left, right]));
    Ok(())
}

fn turboshake128_hashv(data: &[u8]) -> ProgramResult {
    let (left, right) = data.split_at(data.len() / 2);
    set_return_data(&TurboShake128::hashv::<32, 0x1f>(&[left, right]));
    Ok(())
}

fn turboshake256_hashv(data: &[u8]) -> ProgramResult {
    let (left, right) = data.split_at(data.len() / 2);
    set_return_data(&TurboShake256::hashv::<32, 0x1f>(&[left, right]));
    Ok(())
}
