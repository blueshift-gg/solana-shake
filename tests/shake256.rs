//! Correctness tests for the SHAKE256 / Keccak-f[1600] core.
//!
//! Kept out of `src/lib.rs` (and out of the published tarball via the
//! `exclude` in `Cargo.toml`) so the crate ships only the primitive. They
//! exercise the public API exactly as the `solana-hawk512` /
//! `solana-falcon512` consumers do.

use solana_shake256::{RATE, Shake256};

#[test]
fn shake256_empty() {
    // NIST KAT: SHAKE256("") first 32 bytes
    let expected: [u8; 32] = [
        0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb,
        0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5,
        0x76, 0x2f,
    ];
    let mut s = Shake256::new();
    s.finalize();
    let mut out = [0u8; 32];
    s.squeeze(&mut out);
    assert_eq!(out, expected);
}

#[test]
fn shake256_abc() {
    // SHAKE256("abc") first 32 bytes
    let expected: [u8; 32] = [
        0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77, 0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11,
        0x4d, 0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee, 0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b,
        0x57, 0x39,
    ];
    let mut s = Shake256::new();
    s.absorb(b"abc");
    s.finalize();
    let mut out = [0u8; 32];
    s.squeeze(&mut out);
    assert_eq!(out, expected);
}

#[test]
fn shake256_long_squeeze() {
    // Squeeze across multiple rate blocks (RATE = 136 B/permute).
    let mut s = Shake256::new();
    s.finalize();
    let mut out = [0u8; 200];
    s.squeeze(&mut out);
    let mut s2 = Shake256::new();
    s2.finalize();
    let mut a = [0u8; 100];
    let mut b = [0u8; 100];
    s2.squeeze(&mut a);
    s2.squeeze(&mut b);
    assert_eq!(&out[..100], &a[..]);
    assert_eq!(&out[100..], &b[..]);
}

#[test]
fn rate_lanes_match_squeeze() {
    // The bulk-rate path (`rate_lanes` + `permute`) yields the same
    // 136-byte blocks as the byte `squeeze`.
    let mut a = Shake256::new();
    a.absorb(b"the shared keccak core");
    a.finalize();
    let mut sq = [0u8; 272]; // 2 rate blocks
    a.squeeze(&mut sq);

    let mut b = Shake256::new();
    b.absorb(b"the shared keccak core");
    b.finalize();
    let mut drained = [0u8; 272];
    for blk in 0..2 {
        for (l, &lane) in b.rate_lanes().iter().enumerate() {
            drained[blk * RATE + l * 8..blk * RATE + l * 8 + 8]
                .copy_from_slice(&lane.to_le_bytes());
        }
        b.permute();
    }
    assert_eq!(sq, drained);
}
