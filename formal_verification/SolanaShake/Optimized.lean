/-
  SolanaShake.Optimized — line-by-line transcription of the optimized
  Keccak-p[1600] in `src/lib.rs` (`keccak_p1600::<TURBO>`, the `round!`
  macro, and the entry/exit lane complements).

  Transcription rules (checked by inspection against `src/lib.rs`):
  * `u64` is `BitVec 64`; `^`, `&`, `|`, `!` are `^^^`, `&&&`, `|||`, `~~~`;
    `x.rotate_left(n)` is `x.rotateLeft n` (same semantics for every n).
  * The Rust mutates `s: &mut [u64; 25]` in place. Each assignment
    `s[i] = e` is transcribed as `let s := upd s i e`, and each read
    `s[i]` reads the CURRENT (possibly already overwritten) state, so the
    cell-saves `let s3 = s[3]; ...` and their read-after-write ordering are
    modelled exactly; using a stale or missing save would make the proof
    in `SolanaShake.Proof` fail.
  * Every b_i, rotation amount and per-row `!`/`&`/`|` expression is copied
    verbatim, including operator association (Rust `^`, `&`, `|` are
    left-associative, as are Lean's `^^^`, `&&&`, `|||`; parenthesisation is
    kept as written).
  * `RC` is the Rust table, copied literally (`RCrust`); `RCrust_eq_spec`
    checks it against `Spec.RCtable`.

  Nothing here is trusted to be *correct*; `SolanaShake.Proof` proves it
  equals the FIPS 202 specification in `SolanaShake.Spec`.
-/
import SolanaShake.Spec

namespace SolanaShake.Optimized

open SolanaShake.Spec (Word State)

/-- In-place store `s[i] = v`. -/
def upd (s : State) (i : Fin 25) (v : Word) : State :=
  fun j => if j = i then v else s j

/-- `const RC: [u64; 24]` from `src/lib.rs`, verbatim. -/
def RCrust : List Word :=
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

/-- `RC[i]`. -/
def RC (i : Nat) : Word := RCrust.getD i 0

/-- Entry/exit: `s[1] = !s[1]; s[2] = !s[2]; s[8] = !s[8]; s[12] = !s[12];
    s[17] = !s[17]; s[20] = !s[20];` -/
def complementLanes (s : State) : State :=
  let s := upd s 1 (~~~(s 1))
  let s := upd s 2 (~~~(s 2))
  let s := upd s 8 (~~~(s 8))
  let s := upd s 12 (~~~(s 12))
  let s := upd s 17 (~~~(s 17))
  let s := upd s 20 (~~~(s 20))
  s

/-- The body of `macro_rules! round` (src/lib.rs lines 58–163), with
    `$rc` = `rc`. -/
def bertoniRound (s : State) (rc : Word) : State :=
  -- theta — column parities
  let c0 := s 0 ^^^ s 5 ^^^ s 10 ^^^ s 15 ^^^ s 20
  let c1 := s 1 ^^^ s 6 ^^^ s 11 ^^^ s 16 ^^^ s 21
  let c2 := s 2 ^^^ s 7 ^^^ s 12 ^^^ s 17 ^^^ s 22
  let c3 := s 3 ^^^ s 8 ^^^ s 13 ^^^ s 18 ^^^ s 23
  let c4 := s 4 ^^^ s 9 ^^^ s 14 ^^^ s 19 ^^^ s 24

  let d0 := c4 ^^^ c1.rotateLeft 1
  let d1 := c0 ^^^ c2.rotateLeft 1
  let d2 := c1 ^^^ c3.rotateLeft 1
  let d3 := c2 ^^^ c4.rotateLeft 1
  let d4 := c3 ^^^ c0.rotateLeft 1

  let s3 := s 3
  let s1 := s 1
  let s4 := s 4
  let s2 := s 2

  -- Row 0
  let s :=
    let b0 := s 0 ^^^ d0
    let b1 := (s 6 ^^^ d1).rotateLeft 44
    let b2 := (s 12 ^^^ d2).rotateLeft 43
    let b3 := (s 18 ^^^ d3).rotateLeft 21
    let b4 := (s 24 ^^^ d4).rotateLeft 14
    let s := upd s 0 (b0 ^^^ (b1 ||| b2) ^^^ rc)
    let s := upd s 1 (b1 ^^^ ((~~~b2) ||| b3))
    let s := upd s 2 (b2 ^^^ (b3 &&& b4))
    let s := upd s 3 (b3 ^^^ (b4 ||| b0))
    let s := upd s 4 (b4 ^^^ (b0 &&& b1))
    s

  let s7 := s 7
  let s5 := s 5
  let s8 := s 8

  -- Row 1
  let s :=
    let b0 := (s3 ^^^ d3).rotateLeft 28
    let b1 := (s 9 ^^^ d4).rotateLeft 20
    let b2 := (s 10 ^^^ d0).rotateLeft 3
    let b3 := (s 16 ^^^ d1).rotateLeft 45
    let b4 := (s 22 ^^^ d2).rotateLeft 61
    let s := upd s 5 (b0 ^^^ (b1 ||| b2))
    let s := upd s 6 (b1 ^^^ (b2 &&& b3))
    let s := upd s 7 ((~~~b2) ^^^ b4 ^^^ (b3 &&& b4))
    let s := upd s 8 (b3 ^^^ (b4 ||| b0))
    let s := upd s 9 (b4 ^^^ (b0 &&& b1))
    s

  let s11 := s 11
  let s14 := s 14

  -- Row 2
  let s :=
    let b0 := (s1 ^^^ d1).rotateLeft 1
    let b1 := (s7 ^^^ d2).rotateLeft 6
    let b2 := (s 13 ^^^ d3).rotateLeft 25
    let b3 := (s 19 ^^^ d4).rotateLeft 8
    let b4 := (s 20 ^^^ d0).rotateLeft 18
    let s := upd s 10 (b0 ^^^ (b1 ||| b2))
    let s := upd s 11 (b1 ^^^ (b2 &&& b3))
    let s := upd s 12 (b2 ^^^ b4 ^^^ (b3 &&& b4))
    let s := upd s 13 (b3 ^^^ ~~~(b4 ||| b0))
    let s := upd s 14 (b4 ^^^ (b0 &&& b1))
    s

  let s15 := s 15

  -- Row 3
  let s :=
    let b0 := (s4 ^^^ d4).rotateLeft 27
    let b1 := (s5 ^^^ d0).rotateLeft 36
    let b2 := (s11 ^^^ d1).rotateLeft 10
    let b3 := (s 17 ^^^ d2).rotateLeft 15
    let b4 := (s 23 ^^^ d3).rotateLeft 56
    let s := upd s 15 (b0 ^^^ (b1 &&& b2))
    let s := upd s 16 (b1 ^^^ (b2 ||| b3))
    let s := upd s 17 (b2 ^^^ ((~~~b3) ||| b4))
    let s := upd s 18 ((~~~b3) ^^^ (b4 &&& b0))
    let s := upd s 19 (b4 ^^^ (b0 ||| b1))
    s

  -- Row 4
  let s :=
    let b0 := (s2 ^^^ d2).rotateLeft 62
    let b1 := (s8 ^^^ d3).rotateLeft 55
    let b2 := (s14 ^^^ d4).rotateLeft 39
    let b3 := (s15 ^^^ d0).rotateLeft 41
    let b4 := (s 21 ^^^ d1).rotateLeft 2
    let s := upd s 20 (b0 ^^^ b2 ^^^ (b1 &&& b2))
    let s := upd s 21 (b1 ^^^ ~~~(b2 ||| b3))
    let s := upd s 22 (b2 ^^^ (b3 &&& b4))
    let s := upd s 23 (b3 ^^^ (b4 ||| b0))
    let s := upd s 24 (b4 ^^^ (b0 &&& b1))
    s
  s

/-- `keccak_p1600::<TURBO>` (src/lib.rs lines 35–201). -/
def keccakP1600 (turbo : Bool) (s : State) : State :=
  let s := complementLanes s
  let s :=
    if !turbo then
      let s := bertoniRound s (RC 0)
      let s := bertoniRound s (RC 1)
      let s := bertoniRound s (RC 2)
      let s := bertoniRound s (RC 3)
      let s := bertoniRound s (RC 4)
      let s := bertoniRound s (RC 5)
      let s := bertoniRound s (RC 6)
      let s := bertoniRound s (RC 7)
      let s := bertoniRound s (RC 8)
      let s := bertoniRound s (RC 9)
      let s := bertoniRound s (RC 10)
      let s := bertoniRound s (RC 11)
      s
    else s
  let s := bertoniRound s (RC 12)
  let s := bertoniRound s (RC 13)
  let s := bertoniRound s (RC 14)
  let s := bertoniRound s (RC 15)
  let s := bertoniRound s (RC 16)
  let s := bertoniRound s (RC 17)
  let s := bertoniRound s (RC 18)
  let s := bertoniRound s (RC 19)
  let s := bertoniRound s (RC 20)
  let s := bertoniRound s (RC 21)
  let s := bertoniRound s (RC 22)
  let s := bertoniRound s (RC 23)
  complementLanes s

/-- The transcribed Rust `RC` table is the FIPS 202 table. -/
theorem RCrust_eq_spec : RCrust = Spec.RCtable := by decide

end SolanaShake.Optimized
