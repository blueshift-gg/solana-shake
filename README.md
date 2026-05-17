# Solana SHAKE256

[![CI](https://github.com/blueshift-gg/solana-shake256/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/solana-shake256/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/solana-shake256.svg)](https://crates.io/crates/solana-shake256)
[![docs.rs](https://docs.rs/solana-shake256/badge.svg)](https://docs.rs/solana-shake256)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/blueshift-gg/solana-shake256/blob/master/LICENSE)

A `no_std`, zero-dependency, SVM-optimized **SHAKE256 / Keccak-f[1600]** (FIPS 202) library.

## Features

- **no_std, zero dependencies**: works in embedded, WebAssembly, and on-chain
  Solana programs without the standard library or any transitive crates.
- **Bertoni lane-complementing**: the 6-lane Keccak-Team set
  `{1,2,8,12,17,20}`, complemented once per permute, fused with an in-place
  chi-row + 10 cell-saves layout (no `B[25]` scratch) — ~456 NOTs eliminated
  across the 24 rounds.
- **Zero crate-boundary cost**: every method is `#[inline]`; with the
  consumers' `opt-level=3` SBF build there is no codegen penalty versus an
  in-tree module.
- **Both output styles**: the bulk **rate-draining** path
  (`rate_lanes()` + `permute()`, for Falcon's `hash_to_point` rejection
  sampling) and a const-length `squeeze::<LEN>()` (for HAWK's
  `hpub`/`M`/`h`).

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
solana-shake256 = "0.1.0"
```

The lifecycle is `new → absorb* → finalize → (squeeze | rate_lanes/permute)`.

### Fixed-length output

```rust
use solana_shake256::Shake256;

let mut s = Shake256::new();
s.absorb(b"message");
s.finalize();

let mut out = [0u8; 64];
s.squeeze(&mut out);
```

### Draining the rate (bulk path)

```rust
use solana_shake256::Shake256;

let mut s = Shake256::new();
s.absorb(b"message");
s.finalize();

loop {
    for &lane in s.rate_lanes() {
        // consume `lane` (e.g. Falcon rejection sampling)
    }
    s.permute(); // next 136-byte block
}
```

## Status

**Not audited.** Cross-checked against the NIST SHAKE256 KATs (`""`, `"abc"`,
multi-block) and, transitively, the full PQCsignKAT suites of the two consumer
crates.

## Disclaimer

Use this library at your own risk.

## License

Licensed under the [MIT License](https://github.com/blueshift-gg/solana-shake256/blob/master/LICENSE).
The license includes the standard "as-is" warranty disclaimer — use at your
own risk.
