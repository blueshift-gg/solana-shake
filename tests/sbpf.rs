use mollusk_svm::Mollusk;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use solana_address::Address;
use solana_instruction::Instruction;

fn hash<H: Update + ExtendableOutput>(mut hasher: H, input: &[u8]) -> [u8; 32] {
    hasher.update(input);
    let mut output = [0; 32];
    hasher.finalize_xof().read(&mut output);
    output
}

#[test]
fn example_program() {
    let program = Address::new_from_array([1; 32]);
    let elf =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("target/deploy/solana_shake_example");
    let svm = Mollusk::new(&program, elf.to_str().unwrap());
    for length in [0, 3, 135, 136, 137, 167, 168, 169, 1312] {
        let input = vec![0x5a; length];
        let expected = [
            hash(sha3::Shake128::default(), &input),
            hash(sha3::Shake256::default(), &input),
            hash(
                sha3::TurboShake128::from_core(sha3::TurboShake128Core::new(0x1f)),
                &input,
            ),
            hash(
                sha3::TurboShake256::from_core(sha3::TurboShake256Core::new(0x1f)),
                &input,
            ),
        ];
        for tag in 0..8 {
            let data = [&[tag][..], &input].concat();
            let instruction = Instruction::new_with_bytes(program, &data, vec![]);
            let result = svm.process_instruction(&instruction, &[]);
            assert!(result.program_result.is_ok(), "{:?}", result.program_result);
            assert_eq!(result.return_data, expected[usize::from(tag % 4)]);
            assert!(result.compute_units_consumed < 120_000);
            if length == 0 || length == 1312 {
                eprintln!(
                    "tag {tag}, {length} bytes: {} CU",
                    result.compute_units_consumed
                );
            }
        }
    }
    for data in [&[][..], &[8]] {
        let instruction = Instruction::new_with_bytes(program, data, vec![]);
        assert!(
            svm.process_instruction(&instruction, &[])
                .program_result
                .is_err()
        );
    }
}
