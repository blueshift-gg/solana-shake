//! Kani harnesses for the permutation and the sponge.
//!
//! Two tiers, selectable by `--harness` prefix:
//!
//! FAST (every PR, about a minute in total):
//!
//! ```text
//! RUSTFLAGS="--cfg solana_shake_kani" cargo kani -Z stubbing --harness bertoni_round_equals_reference_round \
//!     --harness complement_lanes_is_the_cs_involution --harness new_is_empty \
//!     --harness finalize_ --harness rate_lanes_and_permute_
//! ```
//!
//! SLOW (CI runs these only when `src/` or these proofs change, one job per
//! harness, or on manual dispatch; minutes each): every `squeeze_*` harness,
//! e.g. `RUSTFLAGS="--cfg solana_shake_kani" cargo kani -Z stubbing --harness kani_proofs::squeeze_shake256_9 --exact`.
//!
//! NOT YET COMPLETING: the `absorb_*` harnesses. They are written and bounded
//! as described below, but CBMC did not finish them within 20 minutes (bound
//! 10) or 40 minutes (bound 17), so they are compiled only with
//! `RUSTFLAGS="--cfg solana_shake_kani --cfg kani_absorb"` and are not in CI.
//! The plan is to replace the unrolled form with Kani loop contracts. Until then `absorb` is covered
//! by the differential tests against the byte-at-a-time reference and `sha3`.
//!
//! Proved for all inputs (every state, round constant and `pos < RATE`):
//!
//! * `bertoni_round_equals_reference_round`: one lane-complemented round,
//!   bracketed by `complement_lanes`, equals the plain FIPS 202 round of
//!   `reference.rs`. `keccak_p1600` is complement; rounds RC[0..24] (or
//!   RC[12..24]); complement with the same set, so chaining gives
//!   Keccak-p[1600, 24] / Keccak-p[1600, 12] (the chaining step is the
//!   unit test `permutation_is_complement_rounds_complement`, plus the
//!   differential tests).
//! * `complement_lanes_is_the_cs_involution`: exactly lanes
//!   {1, 2, 8, 12, 17, 20} are flipped, and twice is the identity.
//! * `new_is_empty`: `new` is the zero state at `pos == 0`.
//! * `finalize_*`: padding equals the reference (domain byte at `pos`,
//!   `0x80` at `RATE - 1`, the same byte when `pos == RATE - 1`), then one
//!   permutation of the right variant, and `pos` restarts at 0.
//! * `rate_lanes_and_permute_*`: `rate_lanes` is exactly `state[..RATE/8]`
//!   (the same memory); `permute` applies the permutation once, keeps `pos`.
//!
//! Bounded (arbitrary state, arbitrary `pos < RATE`, arbitrary
//! permutation via the [`Oracle`] stub):
//!
//! * `absorb_*` (opt-in, see above; not yet completing): absorbing any 0..=10 bytes equals the byte-at-a-time
//!   reference (state, `pos`, and the permutation call). 10 bytes from any
//!   `pos` exercise phase 1 running into a lane boundary, a full phase-2
//!   lane, a phase-3 tail, and, for `pos` near `RATE`, a permutation inside
//!   phase 1 and inside phase 2. (Phase 3 starts lane-aligned with fewer
//!   than 8 bytes, so it can never reach the rate boundary.)
//! * `squeeze_*_{1,7,8,9,17}`: `squeeze::<LEN>` equals the reference
//!   (bytes, state, `pos`, permutation call), likewise from any `pos`.
//!
//! Every harness also checks `pos < RATE` afterwards. The two
//! `assert_unchecked` preconditions are checked by Kani itself (it turns
//! `core::hint::assert_unchecked` into a "Rust intrinsic assumption" check;
//! a deliberately broken precondition fails), so the `absorb_*` and
//! `squeeze_*` harnesses prove them on all paths up to their bounds.
//!
//! Longer inputs and outputs are covered by the differential tests in
//! `reference.rs` (real sponge vs. reference sponge vs. the `sha3` crate).

use crate::reference::{self, RefSponge};
use crate::{Shake, Xof, bertoni_round, complement_lanes};

/// Lane-by-lane equality, unrolled (array `==` lowers to a 200-byte
/// `memcmp` loop, and a loop would force the unwind bound to 26).
fn assert_state_eq(a: &[u64; 25], b: &[u64; 25]) {
    macro_rules! lanes {
        ($($i:literal)*) => { $(assert!(a[$i] == b[$i]);)* };
    }
    lanes!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24);
}

fn assert_bytes_eq(a: &[u8], b: &[u8]) {
    assert!(a.len() == b.len());
    let mut i = 0;
    while i < a.len() {
        assert!(a[i] == b[i]);
        i += 1;
    }
}

#[kani::proof]
#[kani::unwind(26)]
fn bertoni_round_equals_reference_round() {
    let s: [u64; 25] = kani::any();
    let rc: u64 = kani::any();
    let mut a = s;
    complement_lanes(&mut a);
    bertoni_round(&mut a, rc);
    complement_lanes(&mut a);
    let mut b = s;
    reference::round(&mut b, rc);
    assert_state_eq(&a, &b);
}

/// `complement_lanes` flips exactly the six `COMPLEMENTED` lanes and is an
/// involution, so the exit complement undoes the entry complement.
#[kani::proof]
fn complement_lanes_is_the_cs_involution() {
    let s: [u64; 25] = kani::any();
    let mut a = s;
    complement_lanes(&mut a);
    let mut i = 0;
    while i < 25 {
        let flipped = matches!(i, 1 | 2 | 8 | 12 | 17 | 20);
        assert!(a[i] == if flipped { !s[i] } else { s[i] });
        i += 1;
    }
    complement_lanes(&mut a);
    assert_state_eq(&a, &s);
}

/// An uninterpreted stand-in for the permutation. The harness runs the
/// real sponge (run 0, through the stub) and then the reference sponge
/// (run 1, calling `stub_p1600` directly). A call in either run logs its
/// input and returns the same arbitrary state `output`, chosen symbolically
/// before the runs. `oracle_check` then asserts both runs made the same
/// number of calls on identical inputs, so they would have got identical
/// outputs from *any* function: the result holds for every permutation,
/// Keccak-p included, not just for this stub.
///
/// Within the bounds of these harnesses (at most 17 bytes from any
/// `pos < RATE`) a run permutes at most once, and the stub asserts that,
/// so a single slot suffices (and keeps the formula free of symbolically
/// indexed logs, which made the solver an order of magnitude slower).
struct Oracle {
    turbo: bool,
    run: usize,
    calls: [usize; 2],
    input: [[u64; 25]; 2],
    output: [u64; 25],
}

static mut ORACLE: Oracle = Oracle {
    turbo: false,
    run: 0,
    calls: [0; 2],
    input: [[0; 25]; 2],
    output: [0; 25],
};

fn oracle() -> &'static mut Oracle {
    // SAFETY: harnesses are single-threaded and no two of these borrows are
    // live at once.
    unsafe { &mut *(&raw mut ORACLE) }
}

/// Start run 0 (the real sponge), expecting `keccak_p1600::<turbo>`.
fn oracle_init(turbo: bool) {
    let o = oracle();
    o.turbo = turbo;
    o.run = 0;
    o.calls = [0; 2];
    o.output = kani::any();
}

/// Start run 1 (the reference sponge).
fn oracle_switch() {
    oracle().run = 1;
}

/// Both runs called the permutation equally often on identical states;
/// returns the number of calls.
fn oracle_check() -> usize {
    let o = oracle();
    assert!(o.calls[0] == o.calls[1]);
    if o.calls[0] == 1 {
        assert_state_eq(&o.input[0], &o.input[1]);
    }
    o.calls[0]
}

/// Replaces `keccak_p1600::<TURBO>` (see [`Oracle`]). Also asserts that the
/// sponge calls the permutation variant (24 or 12 rounds) of its `TURBO`.
fn stub_p1600<const TURBO: bool>(s: &mut [u64; 25]) {
    let o = oracle();
    assert!(TURBO == o.turbo, "wrong permutation variant");
    let run = o.run;
    assert!(o.calls[run] == 0, "more than one permutation in a harness");
    o.input[run] = *s;
    *s = o.output;
    o.calls[run] = 1;
}

#[cfg(kani_absorb)]
macro_rules! absorb_harness {
    ($name:ident, $bits:literal, $turbo:literal) => {
        #[kani::proof]
        #[kani::stub(crate::keccak_p1600, stub_p1600)]
        #[kani::unwind(12)]
        fn $name() {
            const RATE: usize = Shake::<$bits, $turbo>::RATE;
            const MAX: usize = 10;
            let state: [u64; 25] = kani::any();
            let pos: usize = kani::any();
            kani::assume(pos < RATE);
            let buf: [u8; MAX] = kani::any();
            let len: usize = kani::any();
            kani::assume(len <= MAX);
            let data = &buf[..len];
            kani::cover!(pos % 8 == 7 && len == MAX, "phases 1, 2 and 3");
            kani::cover!(pos % 8 != 0 && pos + len >= RATE, "permute in phase 1");
            kani::cover!(pos + 8 == RATE && len >= 8, "permute in phase 2");

            let mut s = Shake::<$bits, $turbo> { state, pos };
            oracle_init($turbo);
            s.absorb(data);
            assert!(s.pos < RATE);

            oracle_switch();
            let mut r = RefSponge::<RATE> { state, pos };
            r.absorb(data, stub_p1600::<$turbo>);

            oracle_check();
            assert!(s.pos == r.pos);
            assert_state_eq(&s.state, &r.state);
        }
    };
}

#[cfg(kani_absorb)]
absorb_harness!(absorb_shake128, 128, false);
#[cfg(kani_absorb)]
absorb_harness!(absorb_shake256, 256, false);
#[cfg(kani_absorb)]
absorb_harness!(absorb_turboshake128, 128, true);
#[cfg(kani_absorb)]
absorb_harness!(absorb_turboshake256, 256, true);

macro_rules! finalize_harness {
    ($name:ident, $bits:literal, $turbo:literal, $domain:literal) => {
        #[kani::proof]
        #[kani::stub(crate::keccak_p1600, stub_p1600)]
        fn $name() {
            const RATE: usize = Shake::<$bits, $turbo>::RATE;
            let state: [u64; 25] = kani::any();
            let pos: usize = kani::any();
            kani::assume(pos < RATE);
            kani::cover!(pos == RATE - 1, "domain and 0x80 share a byte");

            let mut s = Shake::<$bits, $turbo> { state, pos };
            oracle_init($turbo);
            let xof = s.finalize_with_domain::<$domain>();
            assert!(xof.sponge.pos == 0);

            oracle_switch();
            let mut r = RefSponge::<RATE> { state, pos };
            r.pad($domain, stub_p1600::<$turbo>);

            assert!(oracle_check() == 1);
            assert!(s.pos == r.pos);
            assert_state_eq(&s.state, &r.state);
        }
    };
}

finalize_harness!(finalize_shake128, 128, false, 0x1f);
finalize_harness!(finalize_shake256, 256, false, 0x1f);
finalize_harness!(finalize_turboshake128_01, 128, true, 0x01);
finalize_harness!(finalize_turboshake128_1f, 128, true, 0x1f);
finalize_harness!(finalize_turboshake128_7f, 128, true, 0x7f);
finalize_harness!(finalize_turboshake256_01, 256, true, 0x01);
finalize_harness!(finalize_turboshake256_1f, 256, true, 0x1f);
finalize_harness!(finalize_turboshake256_7f, 256, true, 0x7f);

macro_rules! squeeze_harness {
    ($name:ident, $bits:literal, $turbo:literal, $len:expr, $unwind:literal) => {
        #[kani::proof]
        #[kani::stub(crate::keccak_p1600, stub_p1600)]
        #[kani::unwind($unwind)]
        fn $name() {
            const RATE: usize = Shake::<$bits, $turbo>::RATE;
            const LEN: usize = $len;
            let state: [u64; 25] = kani::any();
            let pos: usize = kani::any();
            kani::assume(pos < RATE);

            let mut s = Shake::<$bits, $turbo> { state, pos };
            let mut out = [0u8; LEN];
            oracle_init($turbo);
            Xof { sponge: &mut s }.squeeze(&mut out);
            assert!(s.pos < RATE);

            oracle_switch();
            let mut r = RefSponge::<RATE> { state, pos };
            let mut ref_out = [0u8; LEN];
            r.squeeze(&mut ref_out, stub_p1600::<$turbo>);

            oracle_check();
            assert_bytes_eq(&out, &ref_out);
            assert!(s.pos == r.pos);
            assert_state_eq(&s.state, &r.state);
        }
    };
}

// Unwind bound LEN + 2: every squeeze loop and the reference loop run at
// most LEN times.
squeeze_harness!(squeeze_shake128_1, 128, false, 1, 3);
squeeze_harness!(squeeze_shake128_7, 128, false, 7, 9);
squeeze_harness!(squeeze_shake128_8, 128, false, 8, 10);
squeeze_harness!(squeeze_shake128_9, 128, false, 9, 11);
squeeze_harness!(squeeze_shake128_17, 128, false, 17, 19);

squeeze_harness!(squeeze_shake256_1, 256, false, 1, 3);
squeeze_harness!(squeeze_shake256_7, 256, false, 7, 9);
squeeze_harness!(squeeze_shake256_8, 256, false, 8, 10);
squeeze_harness!(squeeze_shake256_9, 256, false, 9, 11);
squeeze_harness!(squeeze_shake256_17, 256, false, 17, 19);

squeeze_harness!(squeeze_turboshake128_1, 128, true, 1, 3);
squeeze_harness!(squeeze_turboshake128_7, 128, true, 7, 9);
squeeze_harness!(squeeze_turboshake128_8, 128, true, 8, 10);
squeeze_harness!(squeeze_turboshake128_9, 128, true, 9, 11);
squeeze_harness!(squeeze_turboshake128_17, 128, true, 17, 19);

squeeze_harness!(squeeze_turboshake256_1, 256, true, 1, 3);
squeeze_harness!(squeeze_turboshake256_7, 256, true, 7, 9);
squeeze_harness!(squeeze_turboshake256_8, 256, true, 8, 10);
squeeze_harness!(squeeze_turboshake256_9, 256, true, 9, 11);
squeeze_harness!(squeeze_turboshake256_17, 256, true, 17, 19);

macro_rules! xof_lanes_harness {
    ($name:ident, $bits:literal, $turbo:literal) => {
        /// `rate_lanes` is exactly `state[..RATE / 8]` (the same memory),
        /// and `permute` applies the permutation once and leaves `pos`.
        #[kani::proof]
        #[kani::stub(crate::keccak_p1600, stub_p1600)]
        fn $name() {
            const RATE: usize = Shake::<$bits, $turbo>::RATE;
            let state: [u64; 25] = kani::any();
            let pos: usize = kani::any();
            kani::assume(pos < RATE);
            let mut s = Shake::<$bits, $turbo> { state, pos };
            let mut xof = Xof { sponge: &mut s };

            let lanes = xof.rate_lanes();
            assert!(lanes.len() == RATE / 8);
            assert!(core::ptr::eq(lanes.as_ptr(), state_ptr(&xof)));
            let i: usize = kani::any();
            kani::assume(i < RATE / 8);
            assert!(lanes[i] == state[i]);

            oracle_init($turbo);
            xof.permute();
            let o = oracle();
            assert!(o.calls[0] == 1);
            assert_state_eq(&o.input[0], &state);
            assert_state_eq(&s.state, &o.output);
            assert!(s.pos == pos);
        }
    };
}

fn state_ptr<const BITS: usize, const TURBO: bool>(x: &Xof<'_, BITS, TURBO>) -> *const u64 {
    x.sponge.state.as_ptr()
}

xof_lanes_harness!(rate_lanes_and_permute_shake128, 128, false);
xof_lanes_harness!(rate_lanes_and_permute_shake256, 256, false);
xof_lanes_harness!(rate_lanes_and_permute_turboshake128, 128, true);
xof_lanes_harness!(rate_lanes_and_permute_turboshake256, 256, true);

/// `new` starts at the all-zero state and `pos == 0 < RATE`.
#[kani::proof]
fn new_is_empty() {
    let s = Shake::<128, true>::new();
    assert!(s.pos == 0);
    assert_state_eq(&s.state, &[0; 25]);
    let s = Shake::<256, false>::new();
    assert!(s.pos == 0);
    assert_state_eq(&s.state, &[0; 25]);
}
