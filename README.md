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
solana-shake = { git = "https://github.com/blueshift-gg/solana-shake" }
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

### Migrating from solana-shake256

SHAKE256 output bytes are unchanged. `finalize` now returns the `Xof` used
for output: `let mut output = sponge.finalize(); output.squeeze(&mut bytes)`.
The old crate-level `RATE` is `Shake256::RATE`.

## Compute units

Measured on SBPF v3 under Mollusk, platform-tools v1.56:

| Operation | CU |
|---|---:|
| SHAKE256 finalize, empty input | 9,910 |
| SHAKE256 absorb 1,312 bytes, squeeze 64 | 102,310 |
| SHAKE128 drain three rate blocks | 39,837 |
| TurboSHAKE256 finalize, empty input | 5,216 |

The permutation uses lane complementing and an unrolled in-place schedule.
The SBPF tests reproduce these measurements through the public API.

## Tests

CI runs fmt, strict Clippy, doctests, NIST CAVP vectors, RFC 9861 vectors,
comparisons with RustCrypto `sha3` and the published `solana-shake256`,
and SBPF known-output checks. Chunked input and output are checked at rate
boundaries, including `hashv`.

```sh
cargo test --lib --test kat --test shake --test turboshake
cargo test --doc
cargo test --test sbpf -- --nocapture --test-threads=1
```

SBPF tests require `cargo-build-sbf 4.2.0`. JavaScript callers can use
[`@noble/hashes`](https://github.com/paulmillr/noble-hashes).

Not independently audited.

## License

[MIT](LICENSE).
