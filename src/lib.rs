#![doc = include_str!("../README.md")]
#![no_std]

const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// Keccak-p[1600, 24], i.e. Keccak-f[1600], when `TURBO` is false; the last
/// twelve rounds with their constants `RC[12..24]` (Keccak-p[1600, 12], RFC
/// 9861) when it is true. The lane-complementing pattern is invariant per
/// round, so the entry and exit complements are the same for both.
const fn keccak_p1600<const TURBO: bool>(s: &mut [u64; 25]) {
    // **Bertoni lane-complementing + chi-row** layout.
    //
    // Pre-complement the canonical 6-lane Keccak Team set
    //     CS = {1, 2, 8, 12, 17, 20}
    // chosen so that across one full round (theta+rho+pi+chi+iota), the
    // complementation pattern is invariant. Per-row IN-complemented b's at
    // post-pi positions (derived from theta+rho+pi propagation):
    //     row 0: b0, b2, b3   row 1: b0, b2     row 2: b0, b2
    //     row 3: b1, b3, b4   row 4: b0, b3
    // Per-row OUT-complemented (must store ~A_logical_new):
    //     row 0: x=1, x=2     row 1: x=3        row 2: x=2
    //     row 3: x=2          row 4: x=0
    // Net ~456 NOTs eliminated per 24-round permute, ~12 added at boundaries.

    // Entry: complement the 6 CS lanes once.
    s[1] = !s[1];
    s[2] = !s[2];
    s[8] = !s[8];
    s[12] = !s[12];
    s[17] = !s[17];
    s[20] = !s[20];

    macro_rules! round {
        ($rc:expr) => {{
            // theta — column parities
            let c0 = s[0] ^ s[5] ^ s[10] ^ s[15] ^ s[20];
            let c1 = s[1] ^ s[6] ^ s[11] ^ s[16] ^ s[21];
            let c2 = s[2] ^ s[7] ^ s[12] ^ s[17] ^ s[22];
            let c3 = s[3] ^ s[8] ^ s[13] ^ s[18] ^ s[23];
            let c4 = s[4] ^ s[9] ^ s[14] ^ s[19] ^ s[24];

            let d0 = c4 ^ c1.rotate_left(1);
            let d1 = c0 ^ c2.rotate_left(1);
            let d2 = c1 ^ c3.rotate_left(1);
            let d3 = c2 ^ c4.rotate_left(1);
            let d4 = c3 ^ c0.rotate_left(1);

            // **In-place chi-row + 10 cell-saves**.
            // Row 0 outputs to s[0..5]; rows 1..4 read s[3], s[1], s[4], s[2]
            // from this range — save before overwriting.
            let s3 = s[3];
            let s1 = s[1];
            let s4 = s[4];
            let s2 = s[2];

            // Row 0 — IN: b0,b2,b3 complemented; OUT-complement: x=1,2.
            // Iota fused into lane 0.
            {
                let b0 = s[0] ^ d0;
                let b1 = (s[6] ^ d1).rotate_left(44);
                let b2 = (s[12] ^ d2).rotate_left(43);
                let b3 = (s[18] ^ d3).rotate_left(21);
                let b4 = (s[24] ^ d4).rotate_left(14);
                s[0] = b0 ^ (b1 | b2) ^ $rc;
                s[1] = b1 ^ ((!b2) | b3);
                s[2] = b2 ^ (b3 & b4);
                s[3] = b3 ^ (b4 | b0);
                s[4] = b4 ^ (b0 & b1);
            }

            // Row 1 outputs to s[5..10]; rows 2..4 read s[7], s[5], s[8].
            let s7 = s[7];
            let s5 = s[5];
            let s8 = s[8];

            // Row 1 — IN: b0,b2 complemented; OUT-complement: x=3.
            {
                let b0 = (s3 ^ d3).rotate_left(28);
                let b1 = (s[9] ^ d4).rotate_left(20);
                let b2 = (s[10] ^ d0).rotate_left(3);
                let b3 = (s[16] ^ d1).rotate_left(45);
                let b4 = (s[22] ^ d2).rotate_left(61);
                s[5] = b0 ^ (b1 | b2);
                s[6] = b1 ^ (b2 & b3);
                s[7] = (!b2) ^ b4 ^ (b3 & b4);
                s[8] = b3 ^ (b4 | b0);
                s[9] = b4 ^ (b0 & b1);
            }

            // Row 2 outputs to s[10..15]; rows 3..4 read s[11], s[14].
            let s11 = s[11];
            let s14 = s[14];

            // Row 2 — IN: b0,b2 complemented; OUT-complement: x=2.
            {
                let b0 = (s1 ^ d1).rotate_left(1);
                let b1 = (s7 ^ d2).rotate_left(6);
                let b2 = (s[13] ^ d3).rotate_left(25);
                let b3 = (s[19] ^ d4).rotate_left(8);
                let b4 = (s[20] ^ d0).rotate_left(18);
                s[10] = b0 ^ (b1 | b2);
                s[11] = b1 ^ (b2 & b3);
                s[12] = b2 ^ b4 ^ (b3 & b4);
                s[13] = b3 ^ !(b4 | b0);
                s[14] = b4 ^ (b0 & b1);
            }

            // Row 3 outputs to s[15..20]; row 4 reads s[15].
            let s15 = s[15];

            // Row 3 — IN: b1,b3,b4 complemented; OUT-complement: x=2.
            {
                let b0 = (s4 ^ d4).rotate_left(27);
                let b1 = (s5 ^ d0).rotate_left(36);
                let b2 = (s11 ^ d1).rotate_left(10);
                let b3 = (s[17] ^ d2).rotate_left(15);
                let b4 = (s[23] ^ d3).rotate_left(56);
                s[15] = b0 ^ (b1 & b2);
                s[16] = b1 ^ (b2 | b3);
                s[17] = b2 ^ ((!b3) | b4);
                s[18] = (!b3) ^ (b4 & b0);
                s[19] = b4 ^ (b0 | b1);
            }

            // Row 4 — IN: b0,b3 complemented; OUT-complement: x=0.
            {
                let b0 = (s2 ^ d2).rotate_left(62);
                let b1 = (s8 ^ d3).rotate_left(55);
                let b2 = (s14 ^ d4).rotate_left(39);
                let b3 = (s15 ^ d0).rotate_left(41);
                let b4 = (s[21] ^ d1).rotate_left(2);
                s[20] = b0 ^ b2 ^ (b1 & b2);
                s[21] = b1 ^ !(b2 | b3);
                s[22] = b2 ^ (b3 & b4);
                s[23] = b3 ^ (b4 | b0);
                s[24] = b4 ^ (b0 & b1);
            }
        }};
    }

    if !TURBO {
        round!(RC[0]);
        round!(RC[1]);
        round!(RC[2]);
        round!(RC[3]);
        round!(RC[4]);
        round!(RC[5]);
        round!(RC[6]);
        round!(RC[7]);
        round!(RC[8]);
        round!(RC[9]);
        round!(RC[10]);
        round!(RC[11]);
    }
    round!(RC[12]);
    round!(RC[13]);
    round!(RC[14]);
    round!(RC[15]);
    round!(RC[16]);
    round!(RC[17]);
    round!(RC[18]);
    round!(RC[19]);
    round!(RC[20]);
    round!(RC[21]);
    round!(RC[22]);
    round!(RC[23]);

    // Exit: un-complement the 6 CS lanes so the caller sees the normal
    // (uncomplemented) state. Cost paid once per permute.
    s[1] = !s[1];
    s[2] = !s[2];
    s[8] = !s[8];
    s[12] = !s[12];
    s[17] = !s[17];
    s[20] = !s[20];
}

/// SHAKE128 rate in bytes (1600-bit state − 2·128-bit capacity = 1344 bits).
pub const SHAKE128_RATE: usize = Shake128::RATE;
/// SHAKE256 rate in bytes (1600-bit state − 2·256-bit capacity = 1088 bits).
pub const SHAKE256_RATE: usize = Shake256::RATE;

/// SHAKE128 (FIPS 202): `Shake<128>`.
pub type Shake128 = Shake<128>;
/// SHAKE256 (FIPS 202): `Shake<256>`.
pub type Shake256 = Shake<256>;
/// TurboSHAKE128 (RFC 9861): `Shake<128, true>`, twelve rounds and a domain
/// byte chosen at `finalize`.
pub type TurboShake128 = Shake<128, true>;
/// TurboSHAKE256 (RFC 9861): `Shake<256, true>`.
pub type TurboShake256 = Shake<256, true>;

/// A Keccak sponge at security level `BITS`, in its absorbing phase: `new` →
/// `absorb`* → `finalize`, which pads, permutes and returns the [`Xof`] that
/// squeezes. Output is only reachable through that value, so nothing can be
/// squeezed before `finalize`, and while it lives the sponge cannot be
/// absorbed into.
///
/// `TURBO` selects the permutation and the padding. `false` is SHAKE (FIPS
/// 202): 24 rounds and the suffix `0x1F`. `true` is TurboSHAKE (RFC 9861):
/// the last 12 rounds and a domain byte given to `finalize`. The rate is
/// derived, 200 bytes of state less a capacity of `2 · BITS` bits: 168 at
/// 128 and 136 at 256. Any other `BITS` fails to compile:
///
/// ```compile_fail,E0080
/// // There is no SHAKE192; the security levels are 128 and 256.
/// let _ = solana_shake::Shake::<192>::new();
/// ```
///
/// Every method is `#[inline]` so the consumer (built `lto`/`opt-level=3`
/// for SBF) folds the whole thing in exactly as if it were a local module —
/// the crate boundary has no codegen cost.
pub struct Shake<const BITS: usize, const TURBO: bool = false> {
    state: [u64; 25],
    pos: usize,
}

/// The squeezing phase of a [`Shake`] sponge, borrowed from its `finalize`.
/// Either drain the rate ([`rate_lanes`](Self::rate_lanes) +
/// [`permute`](Self::permute)) or [`squeeze`](Self::squeeze) a fixed number
/// of bytes. Use one path per value: `permute` refills the rate without
/// moving the `squeeze` cursor.
///
/// A borrow rather than a move: the 200-byte state stays where it is, so
/// the phase change costs nothing on SBF.
pub struct Xof<'a, const BITS: usize, const TURBO: bool> {
    sponge: &'a mut Shake<BITS, TURBO>,
}

impl<const BITS: usize, const TURBO: bool> Default for Shake<BITS, TURBO> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<const BITS: usize, const TURBO: bool> Shake<BITS, TURBO> {
    /// Rate in bytes: the 200-byte state less a capacity of `2 · BITS` bits.
    pub const RATE: usize = 200 - BITS / 4;
    /// Rate in 64-bit lanes.
    const LANES: usize = Self::RATE / 8;
    const VALID: () = assert!(BITS == 128 || BITS == 256, "BITS must be 128 or 256");

    #[inline]
    pub const fn new() -> Self {
        let () = Self::VALID;
        Self {
            state: [0; 25],
            pos: 0,
        }
    }

    #[inline(always)]
    pub const fn absorb(&mut self, data: &[u8]) {
        let mut i = 0;
        let len = data.len();

        // Phase 1: byte-by-byte until lane-aligned.
        while i < len && !self.pos.is_multiple_of(8) {
            let lane = self.pos / 8;
            let shift = 8 * (self.pos % 8);
            self.state[lane] ^= (data[i] as u64) << shift;
            self.pos += 1;
            if self.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut self.state);
                self.pos = 0;
            }
            i += 1;
        }

        // Phase 2: bulk 8-byte chunks XORed straight into a lane. Bytes within
        // a lane are little-endian per FIPS 202, so `from_le_bytes` is the
        // correct assembly. `split_first_chunk` yields the `[u8; 8]` inside a
        // `const fn`; `try_into` on a subslice is a trait call and is not.
        let (_, mut rest) = data.split_at(i);
        while i + 8 <= len {
            // SAFETY: phase 1 made `self.pos` lane-aligned (multiple of 8),
            // and `pos < RATE = LANES * 8`, so `pos / 8 < LANES ≤ 24 < 25`.
            unsafe { core::hint::assert_unchecked(self.pos / 8 < Self::LANES) };
            let (chunk, tail) = match rest.split_first_chunk::<8>() {
                Some(split) => split,
                None => break,
            };
            rest = tail;
            self.state[self.pos / 8] ^= u64::from_le_bytes(*chunk);
            self.pos += 8;
            i += 8;
            if self.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut self.state);
                self.pos = 0;
            }
        }

        // Phase 3: tail bytes (< 8 left).
        while i < len {
            let lane = self.pos / 8;
            let shift = 8 * (self.pos % 8);
            self.state[lane] ^= (data[i] as u64) << shift;
            self.pos += 1;
            if self.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut self.state);
                self.pos = 0;
            }
            i += 1;
        }
    }

    /// Finalize when `TURBO` is a const parameter. SHAKE requires `0x1f`;
    /// TurboSHAKE accepts `0x01..=0x7f` (RFC 9861).
    ///
    /// ```compile_fail,E0080
    /// let mut s = solana_shake::Shake256::new();
    /// let _ = s.finalize_with_domain::<0x07>();
    /// ```
    #[inline(always)]
    pub const fn finalize_with_domain<const DOMAIN: u8>(&mut self) -> Xof<'_, BITS, TURBO> {
        const {
            assert!(
                DOMAIN >= 0x01 && DOMAIN <= 0x7f,
                "DOMAIN must be in 0x01..=0x7f"
            );
            assert!(TURBO || DOMAIN == 0x1f, "SHAKE requires DOMAIN = 0x1f");
        };
        let lane = self.pos / 8;
        let shift = 8 * (self.pos % 8);
        self.state[lane] ^= (DOMAIN as u64) << shift;
        let last = Self::RATE - 1;
        self.state[last / 8] ^= 0x80u64 << (8 * (last % 8));
        keccak_p1600::<TURBO>(&mut self.state);
        self.pos = 0;
        Xof { sponge: self }
    }
}

impl<const BITS: usize> Shake<BITS, false> {
    /// Hash a byte slice to exactly `LEN` output bytes.
    #[inline]
    pub const fn hash<const LEN: usize>(data: &[u8]) -> [u8; LEN] {
        Self::hashv::<LEN>(&[data])
    }

    /// Hash concatenated byte slices without allocating.
    /// Slice boundaries add no padding or domain separation.
    #[inline]
    pub const fn hashv<const LEN: usize>(data: &[&[u8]]) -> [u8; LEN] {
        let mut sponge = Self::new();
        let mut i = 0;
        while i < data.len() {
            sponge.absorb(data[i]);
            i += 1;
        }
        let mut out = [0; LEN];
        sponge.finalize().squeeze(&mut out);
        out
    }

    /// SHAKE padding (FIPS 202 §6.2: the suffix `1111` then `pad10*1`, so
    /// the byte `0x1F`) and the permutation. The returned [`Xof`] is the only
    /// way to read output.
    #[inline(always)]
    pub const fn finalize(&mut self) -> Xof<'_, BITS, false> {
        self.finalize_with_domain::<0x1f>()
    }
}

impl<const BITS: usize> Shake<BITS, true> {
    /// Hash a byte slice to exactly `LEN` output bytes.
    #[inline]
    pub const fn hash<const LEN: usize, const DOMAIN: u8>(data: &[u8]) -> [u8; LEN] {
        Self::hashv::<LEN, DOMAIN>(&[data])
    }

    /// Hash concatenated byte slices without allocating.
    /// Slice boundaries add no padding or domain separation.
    #[inline]
    pub const fn hashv<const LEN: usize, const DOMAIN: u8>(data: &[&[u8]]) -> [u8; LEN] {
        let mut sponge = Self::new();
        let mut i = 0;
        while i < data.len() {
            sponge.absorb(data[i]);
            i += 1;
        }
        let mut out = [0; LEN];
        sponge.finalize::<DOMAIN>().squeeze(&mut out);
        out
    }

    /// TurboSHAKE padding (RFC 9861: the domain byte `DOMAIN`, in
    /// `0x01..=0x7F`, then `pad10*1`) and the permutation. The domain byte
    /// is a protocol constant, so it is a const parameter, and one outside
    /// the range fails to compile:
    ///
    /// ```compile_fail,E0080
    /// let mut s = solana_shake::TurboShake128::new();
    /// let _ = s.finalize::<0x80>();
    /// ```
    #[inline(always)]
    pub const fn finalize<const DOMAIN: u8>(&mut self) -> Xof<'_, BITS, true> {
        self.finalize_with_domain::<DOMAIN>()
    }
}

impl<const BITS: usize, const TURBO: bool> Xof<'_, BITS, TURBO> {
    const RATE: usize = Shake::<BITS, TURBO>::RATE;
    const LANES: usize = Shake::<BITS, TURBO>::LANES;

    /// The first `RATE / 8` u64 lanes (= the rate). Bytes within each lane
    /// are little-endian per FIPS 202: byte at offset `b` of lane `l` is
    /// `(rate_lanes()[l] >> (8*b)) & 0xff`. Drain this, then call
    /// [`permute`](Self::permute) for the next block — the bulk-rate squeeze
    /// path (e.g. Falcon's `hash_to_point`, ML-DSA's `RejNTTPoly`).
    #[inline]
    pub const fn rate_lanes(&self) -> &[u64] {
        self.sponge.state.split_at(Self::LANES).0
    }

    /// Apply the permutation to refill the rate (used with
    /// [`rate_lanes`](Self::rate_lanes)).
    #[inline]
    pub const fn permute(&mut self) {
        keccak_p1600::<TURBO>(&mut self.sponge.state);
    }

    /// Squeeze exactly `LEN` bytes, handling rate-boundary permutes. `LEN`
    /// is const so the loop bounds and the rate-boundary check fold and the
    /// bulk lane copy fully unrolls (the fixed-length path, e.g. HAWK's
    /// `hpub`/`M`/`h`). Bytes within a lane are little-endian per FIPS 202,
    /// so a lane-aligned run of ≥ 8 bytes is one `to_le_bytes` copy (the
    /// same bytes as eight `state[lane] >> 8k` reads).
    #[inline]
    pub const fn squeeze<const LEN: usize>(&mut self, out: &mut [u8; LEN]) {
        let s: &mut Shake<BITS, TURBO> = self.sponge;
        let len = LEN;
        let mut i = 0;

        // Byte-by-byte until lane-aligned.
        while i < len && !s.pos.is_multiple_of(8) {
            let lane = s.pos / 8;
            let shift = 8 * (s.pos % 8);
            out[i] = (s.state[lane] >> shift) as u8;
            s.pos += 1;
            i += 1;
            if s.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut s.state);
                s.pos = 0;
            }
        }

        // Bulk 8-byte lanes (no rate boundary lands mid-lane: RATE = LANES·8).
        while i + 8 <= len && s.pos + 8 <= Self::RATE {
            // SAFETY: `pos` lane-aligned, `pos + 8 ≤ RATE` ⇒ `pos/8 < LANES`.
            unsafe { core::hint::assert_unchecked(s.pos / 8 < Self::LANES) };
            let (_, tail) = out.split_at_mut(i);
            let Some((chunk, _)) = tail.split_first_chunk_mut::<8>() else {
                break;
            };
            *chunk = s.state[s.pos / 8].to_le_bytes();
            s.pos += 8;
            i += 8;
            if s.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut s.state);
                s.pos = 0;
            }
        }

        // Tail bytes (< 8 left, or a partial lane before a rate boundary).
        while i < len {
            let lane = s.pos / 8;
            let shift = 8 * (s.pos % 8);
            out[i] = (s.state[lane] >> shift) as u8;
            s.pos += 1;
            i += 1;
            if s.pos == Self::RATE {
                keccak_p1600::<TURBO>(&mut s.state);
                s.pos = 0;
            }
        }
    }
}
