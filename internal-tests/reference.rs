//! A plain FIPS 202 reference, written from the specification text rather
//! than from the optimized code in `lib.rs`: the five step mappings of
//! §3.2 on a `[u64; 25]` state indexed `x + 5y` (lane `(x, y)`, bit `z` of
//! the lane is bit `z` of the `u64`, which is the §3.1.2 string-to-state
//! order), the round constants from the §3.2.5 LFSR, Keccak-p of §3.3, and
//! a byte-at-a-time sponge (§4) with the SHAKE / TurboSHAKE padding.
//!
//! Compiled only for `cargo test` and `cargo kani`.

/// `rc(t)` of FIPS 202 Algorithm 5: the output bit of the LFSR
/// `x^8 + x^6 + x^5 + x^4 + 1` after `t mod 255` steps.
const fn lfsr_rc(t: usize) -> u64 {
    let t = t % 255;
    if t == 0 {
        return 1;
    }
    // R = 10000000, bit i of `r` is R[i].
    let mut r: u16 = 0b0000_0001;
    let mut i = 1;
    while i <= t {
        // R = 0 || R; R[0] ^= R[8]; R[4] ^= R[8]; R[5] ^= R[8]; R[6] ^= R[8];
        r <<= 1;
        let r8 = (r >> 8) & 1;
        r ^= r8 | (r8 << 4) | (r8 << 5) | (r8 << 6);
        r &= 0xff;
        i += 1;
    }
    (r & 1) as u64
}

/// The iota round constant for round index `ir` (FIPS 202 Algorithm 6
/// steps 2–3, w = 64, l = 6): bit `2^j - 1` of RC is `rc(j + 7 ir)`.
const fn round_constant(ir: usize) -> u64 {
    let mut rc = 0u64;
    let mut j = 0;
    while j <= 6 {
        rc |= lfsr_rc(j + 7 * ir) << ((1usize << j) - 1);
        j += 1;
    }
    rc
}

/// All 24 round constants of Keccak-f[1600], from the LFSR.
pub const ROUND_CONSTANTS: [u64; 24] = {
    let mut t = [0u64; 24];
    let mut ir = 0;
    while ir < 24 {
        t[ir] = round_constant(ir);
        ir += 1;
    }
    t
};

/// The rho offsets of FIPS 202 Algorithm 2, indexed `x + 5y`: lane (0, 0)
/// is not rotated; starting from (x, y) = (1, 0), for t = 0..24 the lane
/// (x, y) is rotated by (t + 1)(t + 2)/2 mod 64, then
/// (x, y) = (y, (2x + 3y) mod 5).
const fn rho_offsets_from_spec() -> [u32; 25] {
    let mut r = [0u32; 25];
    let (mut x, mut y) = (1usize, 0usize);
    let mut t = 0;
    while t < 24 {
        r[x + 5 * y] = (((t + 1) * (t + 2) / 2) % 64) as u32;
        let nx = y;
        let ny = (2 * x + 3 * y) % 5;
        x = nx;
        y = ny;
        t += 1;
    }
    r
}

/// The rho offsets as printed in FIPS 202 Table 2 (and the Keccak
/// reference), indexed `x + 5y`.
pub const RHO_TABLE: [u32; 25] = [
    0, 1, 62, 28, 27, //
    36, 44, 6, 55, 20, //
    3, 10, 43, 25, 39, //
    41, 45, 15, 21, 8, //
    18, 2, 61, 56, 14, //
];

/// The rho offsets used by the reference, computed from the spec's walk.
pub const RHO: [u32; 25] = rho_offsets_from_spec();

const _: () = {
    let mut i = 0;
    while i < 25 {
        assert!(RHO[i] == RHO_TABLE[i], "rho walk disagrees with Table 2");
        i += 1;
    }
};

/// theta (Algorithm 1): C[x] = parity of column x,
/// D[x] = C[x - 1] ^ rot(C[x + 1], 1), A'[x, y] = A[x, y] ^ D[x].
pub fn theta(a: &mut [u64; 25]) {
    let mut c = [0u64; 5];
    for x in 0..5 {
        c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
    }
    for x in 0..5 {
        let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
        for y in 0..5 {
            a[x + 5 * y] ^= d;
        }
    }
}

/// rho (Algorithm 2): rotate each lane by its offset.
pub fn rho(a: &mut [u64; 25]) {
    for i in 0..25 {
        a[i] = a[i].rotate_left(RHO[i]);
    }
}

/// pi (Algorithm 3): A'[x, y] = A[(x + 3y) mod 5, x].
pub fn pi(a: &mut [u64; 25]) {
    let src = *a;
    for x in 0..5 {
        for y in 0..5 {
            a[x + 5 * y] = src[(x + 3 * y) % 5 + 5 * x];
        }
    }
}

/// chi (Algorithm 4): A'[x, y] = A[x, y] ^ (!A[x + 1, y] & A[x + 2, y]).
pub fn chi(a: &mut [u64; 25]) {
    let src = *a;
    for y in 0..5 {
        for x in 0..5 {
            a[x + 5 * y] = src[x + 5 * y] ^ (!src[(x + 1) % 5 + 5 * y] & src[(x + 2) % 5 + 5 * y]);
        }
    }
}

/// iota (Algorithm 6): A'[0, 0] = A[0, 0] ^ RC.
pub fn iota(a: &mut [u64; 25], rc: u64) {
    a[0] ^= rc;
}

/// Rnd(A, ir) = iota(chi(pi(rho(theta(A)))), ir), with the round constant
/// passed in directly.
pub fn round(a: &mut [u64; 25], rc: u64) {
    theta(a);
    rho(a);
    pi(a);
    chi(a);
    iota(a, rc);
}

/// Rounds `first_round .. first_round + n_rounds` of Keccak-f[1600].
/// Keccak-p[1600, n_r] (Algorithm 7) is `reference_p1600(a, 24 - n_r, n_r)`.
pub fn reference_p1600(a: &mut [u64; 25], first_round: usize, n_rounds: usize) {
    for &rc in &ROUND_CONSTANTS[first_round..first_round + n_rounds] {
        round(a, rc);
    }
}

/// Keccak-p[1600, 24] for SHAKE, Keccak-p[1600, 12] for TurboSHAKE.
pub fn reference_permutation<const TURBO: bool>(a: &mut [u64; 25]) {
    if TURBO {
        reference_p1600(a, 12, 12);
    } else {
        reference_p1600(a, 0, 24);
    }
}

/// A byte-at-a-time sponge with a pluggable permutation (so the Kani
/// harnesses can stub it). Byte `pos` of the rate is bits `8 (pos mod 8)`
/// .. of lane `pos / 8`, the FIPS 202 little-endian lane order.
pub struct RefSponge<const RATE: usize> {
    pub state: [u64; 25],
    pub pos: usize,
}

impl<const RATE: usize> RefSponge<RATE> {
    pub fn absorb_byte(&mut self, b: u8, permute: fn(&mut [u64; 25])) {
        self.state[self.pos / 8] ^= (b as u64) << (8 * (self.pos % 8));
        self.pos += 1;
        if self.pos == RATE {
            permute(&mut self.state);
            self.pos = 0;
        }
    }

    pub fn absorb(&mut self, data: &[u8], permute: fn(&mut [u64; 25])) {
        let mut i = 0;
        while i < data.len() {
            self.absorb_byte(data[i], permute);
            i += 1;
        }
    }

    /// The domain byte at `pos`, then the final `1` of pad10*1 at bit 7 of
    /// byte `RATE - 1` (the same byte when `pos == RATE - 1`), then the
    /// permutation. The squeeze position restarts at 0.
    pub fn pad(&mut self, domain: u8, permute: fn(&mut [u64; 25])) {
        self.state[self.pos / 8] ^= (domain as u64) << (8 * (self.pos % 8));
        self.state[(RATE - 1) / 8] ^= 0x80u64 << (8 * ((RATE - 1) % 8));
        permute(&mut self.state);
        self.pos = 0;
    }

    pub fn squeeze_byte(&mut self, permute: fn(&mut [u64; 25])) -> u8 {
        let b = (self.state[self.pos / 8] >> (8 * (self.pos % 8))) as u8;
        self.pos += 1;
        if self.pos == RATE {
            permute(&mut self.state);
            self.pos = 0;
        }
        b
    }

    pub fn squeeze(&mut self, out: &mut [u8], permute: fn(&mut [u64; 25])) {
        let mut i = 0;
        while i < out.len() {
            out[i] = self.squeeze_byte(permute);
            i += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use crate::{Shake, keccak_p1600};
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    use std::vec::Vec;

    struct Rng(u64);
    impl Rng {
        // splitmix64
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }
        fn state(&mut self) -> [u64; 25] {
            core::array::from_fn(|_| self.next())
        }
        fn bytes(&mut self, n: usize) -> Vec<u8> {
            (0..n).map(|_| self.next() as u8).collect()
        }
    }

    #[test]
    fn rho_walk_matches_table() {
        assert_eq!(rho_offsets_from_spec(), RHO_TABLE);
        assert_eq!(RHO, RHO_TABLE);
    }

    #[test]
    fn lfsr_round_constants_match_crate_table() {
        assert_eq!(ROUND_CONSTANTS, crate::RC);
    }

    #[test]
    fn keccak_f1600_zero_state_kat() {
        // Keccak team KeccakF-1600-IntermediateValues.txt: first permutation
        // of the all-zero state, lanes 0 and 24.
        let mut a = [0u64; 25];
        reference_p1600(&mut a, 0, 24);
        assert_eq!(a[0], 0xF1258F7940E1DDE7);
        assert_eq!(a[24], 0xEAF1FF7B5CECA249);
    }

    #[test]
    fn optimized_permutation_matches_reference() {
        let mut rng = Rng(0x5eed);
        for _ in 0..2000 {
            let s = rng.state();
            let (mut a, mut b) = (s, s);
            keccak_p1600::<false>(&mut a);
            reference_p1600(&mut b, 0, 24);
            assert_eq!(a, b);
            let (mut a, mut b) = (s, s);
            keccak_p1600::<true>(&mut a);
            reference_p1600(&mut b, 12, 12);
            assert_eq!(a, b);
        }
    }

    #[test]
    fn optimized_round_matches_reference_round() {
        let mut rng = Rng(0xa11ce);
        for i in 0..2000 {
            let s = rng.state();
            let rc = if i % 2 == 0 {
                ROUND_CONSTANTS[i % 24]
            } else {
                rng.next()
            };
            let (mut a, mut b) = (s, s);
            crate::complement_lanes(&mut a);
            crate::bertoni_round(&mut a, rc);
            crate::complement_lanes(&mut a);
            round(&mut b, rc);
            assert_eq!(a, b);
        }
    }

    /// `keccak_p1600` is literally complement; the rounds; complement.
    #[test]
    fn permutation_is_complement_rounds_complement() {
        let mut rng = Rng(0xc0ffee);
        for _ in 0..500 {
            let s = rng.state();
            for (turbo, first) in [(false, 0), (true, 12)] {
                let mut a = s;
                if turbo {
                    keccak_p1600::<true>(&mut a);
                } else {
                    keccak_p1600::<false>(&mut a);
                }
                let mut b = s;
                crate::complement_lanes(&mut b);
                for rc in &crate::RC[first..] {
                    crate::bertoni_round(&mut b, *rc);
                }
                crate::complement_lanes(&mut b);
                assert_eq!(a, b);
            }
        }
    }

    fn sha3_out<H: Update + ExtendableOutput>(mut h: H, msg: &[u8], n: usize) -> Vec<u8> {
        h.update(msg);
        let mut out = std::vec![0; n];
        h.finalize_xof().read(&mut out);
        out
    }

    macro_rules! sponge_case {
        ($rng:expr, $bits:literal, $turbo:literal, $domain:literal, $sha3:expr) => {{
            const RATE: usize = Shake::<$bits, $turbo>::RATE;
            let rng: &mut Rng = $rng;
            let len = (rng.next() % 700) as usize;
            let msg = rng.bytes(len);
            let n = 1 + (rng.next() % 600) as usize;
            let expected = sha3_out($sha3, &msg, n);

            // Reference sponge.
            let mut r = RefSponge::<RATE> {
                state: [0; 25],
                pos: 0,
            };
            r.absorb(&msg, reference_permutation::<$turbo>);
            r.pad($domain, reference_permutation::<$turbo>);
            let mut got = std::vec![0u8; n];
            r.squeeze(&mut got, reference_permutation::<$turbo>);
            assert_eq!(got, expected, "reference sponge vs sha3");

            // Real sponge, absorbing in random pieces, squeezing via
            // `squeeze::<LEN>` chunks of a few fixed sizes.
            let mut s = Shake::<$bits, $turbo>::new();
            let mut i = 0;
            while i < msg.len() {
                let k = core::cmp::min(msg.len() - i, (rng.next() % 300) as usize);
                s.absorb(&msg[i..i + k]);
                i += k;
            }
            let mut xof = s.finalize_with_domain::<$domain>();
            let mut got = Vec::new();
            while got.len() < n {
                match rng.next() % 5 {
                    0 => {
                        let mut o = [0u8; 1];
                        xof.squeeze(&mut o);
                        got.extend_from_slice(&o);
                    }
                    1 => {
                        let mut o = [0u8; 7];
                        xof.squeeze(&mut o);
                        got.extend_from_slice(&o);
                    }
                    2 => {
                        let mut o = [0u8; 8];
                        xof.squeeze(&mut o);
                        got.extend_from_slice(&o);
                    }
                    3 => {
                        let mut o = [0u8; 61];
                        xof.squeeze(&mut o);
                        got.extend_from_slice(&o);
                    }
                    _ => {
                        let mut o = [0u8; RATE + 3];
                        xof.squeeze(&mut o);
                        got.extend_from_slice(&o);
                    }
                }
            }
            assert_eq!(&got[..n], &expected[..], "sponge squeeze vs sha3");

            // Real sponge, rate_lanes + permute path.
            let mut s = Shake::<$bits, $turbo>::new();
            s.absorb(&msg);
            let mut xof = s.finalize_with_domain::<$domain>();
            let mut got = Vec::new();
            while got.len() < n {
                for lane in xof.rate_lanes() {
                    got.extend_from_slice(&lane.to_le_bytes());
                }
                xof.permute();
            }
            assert_eq!(&got[..n], &expected[..], "rate_lanes vs sha3");
        }};
    }

    #[test]
    fn sponges_match_sha3() {
        use sha3::{
            Shake128, Shake256, TurboShake128, TurboShake128Core, TurboShake256, TurboShake256Core,
        };
        let mut rng = Rng(0xfeed);
        for _ in 0..150 {
            sponge_case!(&mut rng, 128, false, 0x1f, Shake128::default());
            sponge_case!(&mut rng, 256, false, 0x1f, Shake256::default());
            sponge_case!(
                &mut rng,
                128,
                true,
                0x01,
                TurboShake128::from_core(TurboShake128Core::new(0x01))
            );
            sponge_case!(
                &mut rng,
                128,
                true,
                0x06,
                TurboShake128::from_core(TurboShake128Core::new(0x06))
            );
            sponge_case!(
                &mut rng,
                128,
                true,
                0x1f,
                TurboShake128::from_core(TurboShake128Core::new(0x1f))
            );
            sponge_case!(
                &mut rng,
                128,
                true,
                0x7f,
                TurboShake128::from_core(TurboShake128Core::new(0x7f))
            );
            sponge_case!(
                &mut rng,
                256,
                true,
                0x01,
                TurboShake256::from_core(TurboShake256Core::new(0x01))
            );
            sponge_case!(
                &mut rng,
                256,
                true,
                0x0b,
                TurboShake256::from_core(TurboShake256Core::new(0x0b))
            );
            sponge_case!(
                &mut rng,
                256,
                true,
                0x1f,
                TurboShake256::from_core(TurboShake256Core::new(0x1f))
            );
            sponge_case!(
                &mut rng,
                256,
                true,
                0x7f,
                TurboShake256::from_core(TurboShake256Core::new(0x7f))
            );
        }
    }
}
