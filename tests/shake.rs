//! API and differential tests for the SHAKE128 / SHAKE256 sponge.
//!
//! Kept out of `src/lib.rs` (and out of the published tarball via the
//! `exclude` in `Cargo.toml`) so the crate ships only the primitive. They
//! exercise the public API exactly as the verifier consumers do. The NIST
//! CAVP vectors live in `kat.rs`; this file covers the streaming behaviour
//! the vectors cannot see (absorb and squeeze split at arbitrary points,
//! the rate-draining path) against the RustCrypto `sha3` crate, and every
//! SHAKE256 output path against the published `solana-shake256 0.1.0`.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use solana_shake::{SHAKE128_RATE, SHAKE256_RATE, Shake, Shake128, Shake256};

#[test]
fn rates() {
    assert_eq!(Shake128::RATE, SHAKE128_RATE);
    assert_eq!(Shake256::RATE, SHAKE256_RATE);
    assert_eq!(SHAKE128_RATE, 200 - 2 * 16);
    assert_eq!(SHAKE256_RATE, 200 - 2 * 32);
}

#[test]
fn shake256_empty() {
    // NIST KAT: SHAKE256("") first 32 bytes
    let expected: [u8; 32] = [
        0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb,
        0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82, 0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5,
        0x76, 0x2f,
    ];
    let mut s = Shake256::new();
    let mut xof = s.finalize();
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    assert_eq!(out, expected);
}

#[test]
fn shake128_empty() {
    // NIST KAT: SHAKE128("") first 32 bytes
    let expected: [u8; 32] = [
        0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d, 0x61, 0x60, 0x45, 0x50, 0x76, 0x05, 0x85,
        0x3e, 0xd7, 0x3b, 0x80, 0x93, 0xf6, 0xef, 0xbc, 0x88, 0xeb, 0x1a, 0x6e, 0xac, 0xfa, 0x66,
        0xef, 0x26,
    ];
    let mut s = Shake128::new();
    let mut xof = s.finalize();
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
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
    let mut xof = s.finalize();
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    assert_eq!(out, expected);
}

fn long_squeeze<const BITS: usize>() {
    // Squeeze across multiple rate blocks in one call and in two.
    let mut s = Shake::<BITS>::new();
    let mut xof = s.finalize();
    let mut out = [0u8; 400];
    xof.squeeze(&mut out);
    let mut s2 = Shake::<BITS>::new();
    let mut xof2 = s2.finalize();
    let mut a = [0u8; 150];
    let mut b = [0u8; 250];
    xof2.squeeze(&mut a);
    xof2.squeeze(&mut b);
    assert_eq!(&out[..150], &a[..]);
    assert_eq!(&out[150..], &b[..]);
}

#[test]
fn shake128_long_squeeze() {
    long_squeeze::<128>();
}

#[test]
fn shake256_long_squeeze() {
    long_squeeze::<256>();
}

fn rate_lanes_match_squeeze<const BITS: usize, const RATE: usize>() {
    // The bulk-rate path (`rate_lanes` + `permute`) yields the same bytes as
    // `squeeze`, block after block.
    assert_eq!(RATE, Shake::<BITS>::RATE);
    let mut a = Shake::<BITS>::new();
    a.absorb(b"rate-drain");
    let mut a = a.finalize();
    let mut b = Shake::<BITS>::new();
    b.absorb(b"rate-drain");
    let mut b = b.finalize();
    for _ in 0..3 {
        let lanes = a.rate_lanes();
        assert_eq!(lanes.len(), RATE / 8);
        let mut drained = Vec::with_capacity(RATE);
        for lane in lanes {
            drained.extend_from_slice(&lane.to_le_bytes());
        }
        a.permute();
        let mut squeezed = [0u8; RATE];
        b.squeeze(&mut squeezed);
        assert_eq!(&squeezed[..], &drained[..]);
    }
}

#[test]
fn shake128_rate_lanes_match_squeeze() {
    rate_lanes_match_squeeze::<128, SHAKE128_RATE>();
}

#[test]
fn shake256_rate_lanes_match_squeeze() {
    rate_lanes_match_squeeze::<256, SHAKE256_RATE>();
}

/// Deterministic xorshift so the differential inputs are reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn fill(&mut self, buf: &mut [u8]) {
        for b in buf {
            *b = self.next() as u8;
        }
    }
}

fn sha3_reference<H: Default + Update + ExtendableOutput>(input: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = H::default();
    h.update(input);
    let mut reader = h.finalize_xof();
    let mut out = vec![0u8; out_len];
    reader.read(&mut out);
    out
}

/// Random input lengths around every rate boundary, absorbed in random
/// chunks and squeezed in random chunks, against the `sha3` crate.
fn chunked_matches_sha3<const BITS: usize, H: Default + Update + ExtendableOutput>(seed: u64) {
    let rate = Shake::<BITS>::RATE;
    let mut rng = Rng(seed);
    for iter in 0..4000 {
        let in_len = match iter % 4 {
            0 => rng.below(3 * rate + 8),
            // Exactly around a rate boundary: rate·k − 1, rate·k, rate·k + 1.
            1 => rate * (1 + rng.below(3)) + rng.below(3) - 1,
            2 => rng.below(2048),
            _ => rng.below(9),
        };
        let out_len = 1 + rng.below(3 * rate + 8);
        let mut input = vec![0u8; in_len];
        rng.fill(&mut input);
        let expected = sha3_reference::<H>(&input, out_len);

        let mut s = Shake::<BITS>::new();
        let mut pos = 0;
        while pos < in_len {
            let take = 1 + rng.below(in_len - pos);
            s.absorb(&input[pos..pos + take]);
            pos += take;
        }
        let mut s = s.finalize();
        let mut ours = Vec::with_capacity(out_len);
        let mut remaining = out_len;
        while remaining > 0 {
            // `squeeze` takes a const length; pick from a few sizes.
            match rng.below(4) {
                0 if remaining >= 1 => {
                    let mut b = [0u8; 1];
                    s.squeeze(&mut b);
                    ours.extend_from_slice(&b);
                    remaining -= 1;
                }
                1 if remaining >= 7 => {
                    let mut b = [0u8; 7];
                    s.squeeze(&mut b);
                    ours.extend_from_slice(&b);
                    remaining -= 7;
                }
                2 if remaining >= 64 => {
                    let mut b = [0u8; 64];
                    s.squeeze(&mut b);
                    ours.extend_from_slice(&b);
                    remaining -= 64;
                }
                _ => {
                    let mut b = [0u8; 1];
                    s.squeeze(&mut b);
                    ours.extend_from_slice(&b);
                    remaining -= 1;
                }
            }
        }
        assert_eq!(
            ours, expected,
            "iter {iter}: BITS={BITS} diverges from sha3 (in_len={in_len}, out_len={out_len})"
        );
    }
}

#[test]
fn shake128_chunked_matches_sha3() {
    chunked_matches_sha3::<128, sha3::Shake128>(0x9e37_79b9_7f4a_7c15);
}

#[test]
fn shake256_chunked_matches_sha3() {
    chunked_matches_sha3::<256, sha3::Shake256>(0x2545_f491_4f6c_dd1d);
}

/// The rate-draining path against `sha3`: drain whole blocks through
/// `rate_lanes` + `permute` and compare with one long reference output.
fn drained_matches_sha3<const BITS: usize, H: Default + Update + ExtendableOutput>() {
    let rate = Shake::<BITS>::RATE;
    let input = b"drain the rate, block after block";
    let blocks = 5;
    let expected = sha3_reference::<H>(input, blocks * rate);
    let mut s = Shake::<BITS>::new();
    s.absorb(input);
    let mut s = s.finalize();
    let mut ours = Vec::with_capacity(blocks * rate);
    for _ in 0..blocks {
        for &lane in s.rate_lanes() {
            ours.extend_from_slice(&lane.to_le_bytes());
        }
        s.permute();
    }
    assert_eq!(ours, expected);
}

#[test]
fn shake128_drained_matches_sha3() {
    drained_matches_sha3::<128, sha3::Shake128>();
}

#[test]
fn shake256_drained_matches_sha3() {
    drained_matches_sha3::<256, sha3::Shake256>();
}

/// Every SHAKE256 output path against the published `solana-shake256 0.1.0`,
/// the crate HAWK and Falcon run today: the same bytes from `squeeze` at
/// mixed lengths and from the rate-draining path, over inputs absorbed in
/// random chunks around every rate boundary.
#[test]
fn shake256_matches_published_solana_shake256_0_1_0() {
    use solana_shake256::Shake256 as Published;
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    for iter in 0..2000 {
        let in_len = match iter % 3 {
            0 => rng.below(3 * SHAKE256_RATE + 8),
            1 => SHAKE256_RATE * (1 + rng.below(3)) + rng.below(3) - 1,
            _ => rng.below(9),
        };
        let mut input = vec![0u8; in_len];
        rng.fill(&mut input);
        let mut old = Published::new();
        let mut new = Shake256::new();
        let mut pos = 0;
        while pos < in_len {
            let take = 1 + rng.below(in_len - pos);
            old.absorb(&input[pos..pos + take]);
            new.absorb(&input[pos..pos + take]);
            pos += take;
        }
        old.finalize();
        let mut new = new.finalize();
        if iter % 2 == 0 {
            for _ in 0..3 {
                let mut a = [0u8; 7];
                let mut b = [0u8; 7];
                old.squeeze(&mut a);
                new.squeeze(&mut b);
                assert_eq!(a, b, "iter {iter}, in_len {in_len}");
                let mut a = [0u8; 200];
                let mut b = [0u8; 200];
                old.squeeze(&mut a);
                new.squeeze(&mut b);
                assert_eq!(a, b, "iter {iter}, in_len {in_len}");
            }
        } else {
            for _ in 0..3 {
                assert_eq!(
                    old.rate_lanes(),
                    new.rate_lanes(),
                    "iter {iter}, in_len {in_len}"
                );
                old.permute();
                new.permute();
            }
        }
    }
}

/// The sponge evaluates in a const context; the result matches runtime.
const CONST_DIGEST: [u8; 40] = {
    let mut s = Shake128::new();
    s.absorb(b"compile-time SHAKE128");
    let mut xof = s.finalize();
    let mut out = [0u8; 40];
    xof.squeeze(&mut out);
    out
};

#[test]
fn const_evaluation_matches_runtime() {
    let expected = sha3_reference::<sha3::Shake128>(b"compile-time SHAKE128", 40);
    assert_eq!(CONST_DIGEST.to_vec(), expected);
    const LANE: u64 = {
        let mut s = Shake256::new();
        s.absorb(b"lanes");
        let mut xof = s.finalize();
        xof.permute();
        xof.rate_lanes()[3]
    };
    let mut s = Shake256::new();
    s.absorb(b"lanes");
    let mut xof = s.finalize();
    xof.permute();
    assert_eq!(LANE, xof.rate_lanes()[3]);
}

#[test]
fn hashv_matches_sha3_at_rate_boundaries() {
    fn check<const BITS: usize, H: Default + Update + ExtendableOutput>() {
        const OUT: usize = 400;
        let input = [0x5a; 337];
        for len in [0, 1, 135, 136, 137, 167, 168, 169, 337] {
            let input = &input[..len];
            let expected = sha3_reference::<H>(input, OUT);
            assert_eq!(Shake::<BITS>::hash::<OUT>(input).as_slice(), expected);
            for split in 0..=len {
                assert_eq!(
                    Shake::<BITS>::hashv::<OUT>(&[&[], &input[..split], &[], &input[split..]])
                        .as_slice(),
                    expected
                );
            }
        }
    }
    check::<128, sha3::Shake128>();
    check::<256, sha3::Shake256>();
    const EMPTY: [u8; 32] = Shake256::hashv(&[]);
    assert_eq!(EMPTY.as_slice(), sha3_reference::<sha3::Shake256>(&[], 32));
}
