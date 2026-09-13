# Solana SHAKE

[![CI](https://github.com/blueshift-gg/solana-shake/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/solana-shake/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

SHAKE128, SHAKE256, TurboSHAKE128 and TurboSHAKE256 for Solana programs.
`no_std`, allocation-free, with no dependencies. All four use one Keccak
implementation and support constant evaluation.

SHAKE follows FIPS 202. TurboSHAKE follows RFC 9861, uses twelve rounds and
requires a protocol domain byte in `0x01..=0x7f`. It cannot replace SHAKE in
protocols whose specification fixes SHAKE.

## Usage

```toml
[dependencies]
solana-shake = { git = "https://github.com/blueshift-gg/solana-shake", branch = "turboshake" }
```

```rust
use solana_shake::{Shake256, TurboShake128};

let digest = Shake256::hash::<64>(b"message");
assert_eq!(digest, Shake256::hashv::<64>(&[b"mes", b"sage"]));
let turbo = TurboShake128::hash::<32, 0x07>(b"message");
```

`hashv` hashes concatenated byte slices without allocating. Slice boundaries
add no padding or domain separation. Output length is a const parameter.

For streaming input or output, use `new → absorb → finalize → squeeze`:

```rust
use solana_shake::Shake128;

let mut sponge = Shake128::new();
sponge.absorb(b"message");
let mut output = sponge.finalize();
let mut first = [0u8; 32];
let mut next = [0u8; 64];
output.squeeze(&mut first);
output.squeeze(&mut next);
```

`finalize` borrows the sponge and returns an `Xof`. TurboSHAKE uses
`finalize::<DOMAIN>()`. For rejection samplers, `rate_lanes()` exposes the
current rate as little-endian `u64` lanes; `permute()` advances to the next
block. Use either this path or `squeeze` for a given `Xof`.

`Shake128::RATE` is 168 bytes; `Shake256::RATE` is 136. The TurboSHAKE types
have the same respective rates. These aliases select the security level and
round count of `Shake<BITS, TURBO>`; other security levels fail to compile.
Generic callers can use `finalize_with_domain::<0x1f>()` for either variant.

## Example program

The [program](program/src/lib.rs) takes `[tag: 1][message]` and returns 32 bytes.
Tags `0..3` select SHAKE128, SHAKE256, TurboSHAKE128 and TurboSHAKE256.
Tags `4..7` use the same functions through `hashv`, splitting the message in half.
TurboSHAKE uses domain `0x1f`. No accounts are needed.

The [SBPF test](tests/sbpf.rs) checks all eight instructions against RustCrypto.

## Compute units

Measured on SBPF v3 with the example program; 32-byte output.

| Function | Empty input | 1,312-byte input |
|---|---:|---:|
| SHAKE128 | ~10,200 CU | ~83,000 CU |
| SHAKE256 | ~10,200 CU | ~103,000 CU |
| TurboSHAKE128 | ~5,500 CU | ~45,500 CU |
| TurboSHAKE256 | ~5,500 CU | ~56,000 CU |

## Tests

```sh
cargo test --lib --test kat --test shake --test turboshake
cargo test --doc
cargo build-sbf --arch v3 --manifest-path program/Cargo.toml
cargo test --test sbpf -- --nocapture
```

SBPF tests require `cargo-build-sbf 4.2.0`. JavaScript callers can use
[`@noble/hashes`](https://github.com/paulmillr/noble-hashes).

Not independently audited.

## License

[MIT](LICENSE).

From `solana-shake256`: output bytes are unchanged; `finalize()` now returns
the `Xof` used for squeezing, and `RATE` is `Shake256::RATE`.
