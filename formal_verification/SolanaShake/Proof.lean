/-
  SolanaShake.Proof — the Bertoni lane-complementing Keccak-p[1600] in
  `src/lib.rs` equals FIPS 202 Keccak-p[1600, n_r].

  MAIN THEOREMS (State = Fin 25 → BitVec 64, lane x + 5y):
  * `bertoni_round_correct (s rc) :
       complementLanes (bertoniRound (complementLanes s) rc) = Spec.round s rc`
    where `complementLanes` complements lanes {1, 2, 8, 12, 17, 20}
    (`complementLanes_xor_allOnes`: i.e. XOR with all-ones on exactly those
    lanes) and `Spec.round s rc = ι(χ(π(ρ(θ s))), rc)`. Holds for every
    64-bit `rc`.
  * `keccak_p1600_false_correct (s) : keccakP1600 false s = Spec.keccakP 24 s`
    (Keccak-f[1600]).
  * `keccak_p1600_true_correct (s) : keccakP1600 true s = Spec.keccakP 12 s`
    (Keccak-p[1600, 12], rounds 12..23, RFC 9861 / TurboSHAKE).

  PROOF OUTLINE.
  1. `bertoniRound_factor` (by `rfl`, lane by lane): the in-place
     transcription, with its cell-saves, equals `rows (bvals s) rc`, where
     `bvals` computes the 25 values b_x of each row from the round input and
     `rows` applies the per-row output expressions. (These two helper
     definitions are proof-internal; they are tied to the transcription by
     this lemma, not trusted.)
  2. `bvals_spec`: `bvals s = π(ρ(θ s))` (ρ offsets via
     `Spec.rhoOffset_eq_table`).
  3. `bvals_complement` (linear part): complementing CS on input
     complements exactly the b's in `maskB` = {0,2,3,5,7,10,12,16,18,19,20,23}
     (row 0: b0,b2,b3; row 1: b0,b2; row 2: b0,b2; row 3: b1,b3,b4;
     row 4: b0,b3), via `~a ^ b = ~(a ^ b)`, `rotl(~a) = ~rotl(a)`, `~~a = a`.
  4. `rows_maskB` (nonlinear part): on those inputs every row expression
     yields χ+ι of the uncomplemented b's, complemented exactly on CS. Each
     lane is reduced to `BitVec.getLsbD` and closed by case analysis on the
     three (four for lane 0, with rc) Bool bits involved.
  5. Conjugation: `complementLanes` is an involution, so each Rust round is
     `complementLanes ∘ Spec.round ∘ complementLanes` (`bertoniRound_conj`),
     the inner pairs cancel, and the entry/exit complements cancel the rest.

  TRUST BASE. The Lean 4.15.0 kernel and core library only (no Mathlib, no
  Batteries). `#print axioms` on every theorem: at most
  [propext, Classical.choice, Quot.sound]. No `sorry`, no `native_decide`,
  no `bv_decide` (so no `Lean.ofReduceBool`); all finite checks are kernel
  `decide`/`rfl`.

  WHAT IS NOT PROVED HERE. The link from `SolanaShake.Optimized` to the Rust
  source is (a) transcription by inspection (see that file's header), and
  (b) independently, the Kani harness `bertoni_round_equals_reference_round`,
  which proves the REAL Rust round equals a Rust FIPS 202 reference round,
  together with differential tests and the NIST KATs. Lean also does not
  model sponge/padding/byte (de)serialisation, only the permutation.
-/
import SolanaShake.Spec
import SolanaShake.Optimized

namespace SolanaShake.Proof
open SolanaShake.Spec SolanaShake.Optimized

theorem rotateLeft_not (a : Word) (n : Nat) :
    (~~~a).rotateLeft n = ~~~(a.rotateLeft n) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hi := i.isLt
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_not]
  by_cases h : (i : Nat) < n % 64
  · have h2 : 64 - n % 64 + (i : Nat) < 64 := by omega
    simp [h, h2]
  · have h2 : (i : Nat) - n % 64 < 64 := by omega
    simp [h, h2, hi]

theorem not_xor_left (a b : Word) : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, i.isLt, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem not_xor_right (a b : Word) : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, i.isLt, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

/-- The six complemented lanes `{1, 2, 8, 12, 17, 20}`. -/
def inCS (k : Fin 25) : Bool :=
  k.val == 1 || k.val == 2 || k.val == 8 || k.val == 12 || k.val == 17 || k.val == 20

def complement (s : State) : State := fun k => if inCS k then ~~~(s k) else s k

theorem complementLanes_eq (s : State) : complementLanes s = complement s := by
  funext k
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  all_goals first | omega | rfl

/-- The 25 values b_x of rows y = 0..4 (index x + 5y) that the Rust round
    computes, read from the round's INPUT state. -/
def bvals (s : State) : State :=
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
  fun k => match k.val with
  | 0 => s 0 ^^^ d0
  | 1 => (s 6 ^^^ d1).rotateLeft 44
  | 2 => (s 12 ^^^ d2).rotateLeft 43
  | 3 => (s 18 ^^^ d3).rotateLeft 21
  | 4 => (s 24 ^^^ d4).rotateLeft 14
  | 5 => (s 3 ^^^ d3).rotateLeft 28
  | 6 => (s 9 ^^^ d4).rotateLeft 20
  | 7 => (s 10 ^^^ d0).rotateLeft 3
  | 8 => (s 16 ^^^ d1).rotateLeft 45
  | 9 => (s 22 ^^^ d2).rotateLeft 61
  | 10 => (s 1 ^^^ d1).rotateLeft 1
  | 11 => (s 7 ^^^ d2).rotateLeft 6
  | 12 => (s 13 ^^^ d3).rotateLeft 25
  | 13 => (s 19 ^^^ d4).rotateLeft 8
  | 14 => (s 20 ^^^ d0).rotateLeft 18
  | 15 => (s 4 ^^^ d4).rotateLeft 27
  | 16 => (s 5 ^^^ d0).rotateLeft 36
  | 17 => (s 11 ^^^ d1).rotateLeft 10
  | 18 => (s 17 ^^^ d2).rotateLeft 15
  | 19 => (s 23 ^^^ d3).rotateLeft 56
  | 20 => (s 2 ^^^ d2).rotateLeft 62
  | 21 => (s 8 ^^^ d3).rotateLeft 55
  | 22 => (s 14 ^^^ d4).rotateLeft 39
  | 23 => (s 15 ^^^ d0).rotateLeft 41
  | _ => (s 21 ^^^ d1).rotateLeft 2

/-- The per-row output expressions of the Rust round, applied to b-values. -/
def rows (b : State) (rc : Word) : State :=
  fun k => match k.val with
  | 0 => b 0 ^^^ (b 1 ||| b 2) ^^^ rc
  | 1 => b 1 ^^^ ((~~~b 2) ||| b 3)
  | 2 => b 2 ^^^ (b 3 &&& b 4)
  | 3 => b 3 ^^^ (b 4 ||| b 0)
  | 4 => b 4 ^^^ (b 0 &&& b 1)
  | 5 => b 5 ^^^ (b 6 ||| b 7)
  | 6 => b 6 ^^^ (b 7 &&& b 8)
  | 7 => (~~~b 7) ^^^ b 9 ^^^ (b 8 &&& b 9)
  | 8 => b 8 ^^^ (b 9 ||| b 5)
  | 9 => b 9 ^^^ (b 5 &&& b 6)
  | 10 => b 10 ^^^ (b 11 ||| b 12)
  | 11 => b 11 ^^^ (b 12 &&& b 13)
  | 12 => b 12 ^^^ b 14 ^^^ (b 13 &&& b 14)
  | 13 => b 13 ^^^ ~~~(b 14 ||| b 10)
  | 14 => b 14 ^^^ (b 10 &&& b 11)
  | 15 => b 15 ^^^ (b 16 &&& b 17)
  | 16 => b 16 ^^^ (b 17 ||| b 18)
  | 17 => b 17 ^^^ ((~~~b 18) ||| b 19)
  | 18 => (~~~b 18) ^^^ (b 19 &&& b 15)
  | 19 => b 19 ^^^ (b 15 ||| b 16)
  | 20 => b 20 ^^^ b 22 ^^^ (b 21 &&& b 22)
  | 21 => b 21 ^^^ ~~~(b 22 ||| b 23)
  | 22 => b 22 ^^^ (b 23 &&& b 24)
  | 23 => b 23 ^^^ (b 24 ||| b 20)
  | _ => b 24 ^^^ (b 20 &&& b 21)

theorem bertoniRound_factor (s : State) (rc : Word) :
    bertoniRound s rc = rows (bvals s) rc := by
  funext k
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  all_goals first | omega | rfl

theorem rho_apply (A : State) (k : Fin 25) :
    rho A k = (A k).rotateLeft (rhoTable.getD k.val 0) := by
  simp only [rho, rhoOffset_eq_table]

theorem rotateLeft_zero' (a : Word) : a.rotateLeft 0 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp [BitVec.getLsbD_rotateLeft, i.isLt]

set_option maxHeartbeats 4000000 in
theorem bvals_spec (s : State) : bvals s = pi (rho (theta s)) := by
  funext k
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  all_goals first
    | omega
    | (simp only [pi, rho_apply, piSrc, idx, xOf, yOf, rhoTable, bvals, theta, thetaD, thetaC,
         Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
         List.getD_cons_zero, List.getD_cons_succ, rotateLeft_zero']
       rfl)

/-! ## Per-lane evaluation lemmas (all by `rfl`) -/

theorem complement_0 (s : State) : complement s 0 = s 0 := rfl
theorem complement_1 (s : State) : complement s 1 = ~~~(s 1) := rfl
theorem complement_2 (s : State) : complement s 2 = ~~~(s 2) := rfl
theorem complement_3 (s : State) : complement s 3 = s 3 := rfl
theorem complement_4 (s : State) : complement s 4 = s 4 := rfl
theorem complement_5 (s : State) : complement s 5 = s 5 := rfl
theorem complement_6 (s : State) : complement s 6 = s 6 := rfl
theorem complement_7 (s : State) : complement s 7 = s 7 := rfl
theorem complement_8 (s : State) : complement s 8 = ~~~(s 8) := rfl
theorem complement_9 (s : State) : complement s 9 = s 9 := rfl
theorem complement_10 (s : State) : complement s 10 = s 10 := rfl
theorem complement_11 (s : State) : complement s 11 = s 11 := rfl
theorem complement_12 (s : State) : complement s 12 = ~~~(s 12) := rfl
theorem complement_13 (s : State) : complement s 13 = s 13 := rfl
theorem complement_14 (s : State) : complement s 14 = s 14 := rfl
theorem complement_15 (s : State) : complement s 15 = s 15 := rfl
theorem complement_16 (s : State) : complement s 16 = s 16 := rfl
theorem complement_17 (s : State) : complement s 17 = ~~~(s 17) := rfl
theorem complement_18 (s : State) : complement s 18 = s 18 := rfl
theorem complement_19 (s : State) : complement s 19 = s 19 := rfl
theorem complement_20 (s : State) : complement s 20 = ~~~(s 20) := rfl
theorem complement_21 (s : State) : complement s 21 = s 21 := rfl
theorem complement_22 (s : State) : complement s 22 = s 22 := rfl
theorem complement_23 (s : State) : complement s 23 = s 23 := rfl
theorem complement_24 (s : State) : complement s 24 = s 24 := rfl

/-- Complement pattern of the b-values as the Rust round sees them, when its
    input state is complemented on `CS`: row 0: b0,b2,b3; row 1: b0,b2;
    row 2: b0,b2; row 3: b1,b3,b4; row 4: b0,b3 (index x + 5y). -/
def inMB (k : Fin 25) : Bool :=
  [0, 2, 3, 5, 7, 10, 12, 16, 18, 19, 20, 23].contains k.val

def maskB (b : State) : State := fun k => if inMB k then ~~~(b k) else b k

theorem maskB_0 (b : State) : maskB b 0 = ~~~(b 0) := rfl
theorem maskB_1 (b : State) : maskB b 1 = b 1 := rfl
theorem maskB_2 (b : State) : maskB b 2 = ~~~(b 2) := rfl
theorem maskB_3 (b : State) : maskB b 3 = ~~~(b 3) := rfl
theorem maskB_4 (b : State) : maskB b 4 = b 4 := rfl
theorem maskB_5 (b : State) : maskB b 5 = ~~~(b 5) := rfl
theorem maskB_6 (b : State) : maskB b 6 = b 6 := rfl
theorem maskB_7 (b : State) : maskB b 7 = ~~~(b 7) := rfl
theorem maskB_8 (b : State) : maskB b 8 = b 8 := rfl
theorem maskB_9 (b : State) : maskB b 9 = b 9 := rfl
theorem maskB_10 (b : State) : maskB b 10 = ~~~(b 10) := rfl
theorem maskB_11 (b : State) : maskB b 11 = b 11 := rfl
theorem maskB_12 (b : State) : maskB b 12 = ~~~(b 12) := rfl
theorem maskB_13 (b : State) : maskB b 13 = b 13 := rfl
theorem maskB_14 (b : State) : maskB b 14 = b 14 := rfl
theorem maskB_15 (b : State) : maskB b 15 = b 15 := rfl
theorem maskB_16 (b : State) : maskB b 16 = ~~~(b 16) := rfl
theorem maskB_17 (b : State) : maskB b 17 = b 17 := rfl
theorem maskB_18 (b : State) : maskB b 18 = ~~~(b 18) := rfl
theorem maskB_19 (b : State) : maskB b 19 = ~~~(b 19) := rfl
theorem maskB_20 (b : State) : maskB b 20 = ~~~(b 20) := rfl
theorem maskB_21 (b : State) : maskB b 21 = b 21 := rfl
theorem maskB_22 (b : State) : maskB b 22 = b 22 := rfl
theorem maskB_23 (b : State) : maskB b 23 = ~~~(b 23) := rfl
theorem maskB_24 (b : State) : maskB b 24 = b 24 := rfl

theorem chi_0 (b : State) : chi b 0 = b 0 ^^^ (~~~(b 1) &&& b 2) := rfl
theorem chi_1 (b : State) : chi b 1 = b 1 ^^^ (~~~(b 2) &&& b 3) := rfl
theorem chi_2 (b : State) : chi b 2 = b 2 ^^^ (~~~(b 3) &&& b 4) := rfl
theorem chi_3 (b : State) : chi b 3 = b 3 ^^^ (~~~(b 4) &&& b 0) := rfl
theorem chi_4 (b : State) : chi b 4 = b 4 ^^^ (~~~(b 0) &&& b 1) := rfl
theorem chi_5 (b : State) : chi b 5 = b 5 ^^^ (~~~(b 6) &&& b 7) := rfl
theorem chi_6 (b : State) : chi b 6 = b 6 ^^^ (~~~(b 7) &&& b 8) := rfl
theorem chi_7 (b : State) : chi b 7 = b 7 ^^^ (~~~(b 8) &&& b 9) := rfl
theorem chi_8 (b : State) : chi b 8 = b 8 ^^^ (~~~(b 9) &&& b 5) := rfl
theorem chi_9 (b : State) : chi b 9 = b 9 ^^^ (~~~(b 5) &&& b 6) := rfl
theorem chi_10 (b : State) : chi b 10 = b 10 ^^^ (~~~(b 11) &&& b 12) := rfl
theorem chi_11 (b : State) : chi b 11 = b 11 ^^^ (~~~(b 12) &&& b 13) := rfl
theorem chi_12 (b : State) : chi b 12 = b 12 ^^^ (~~~(b 13) &&& b 14) := rfl
theorem chi_13 (b : State) : chi b 13 = b 13 ^^^ (~~~(b 14) &&& b 10) := rfl
theorem chi_14 (b : State) : chi b 14 = b 14 ^^^ (~~~(b 10) &&& b 11) := rfl
theorem chi_15 (b : State) : chi b 15 = b 15 ^^^ (~~~(b 16) &&& b 17) := rfl
theorem chi_16 (b : State) : chi b 16 = b 16 ^^^ (~~~(b 17) &&& b 18) := rfl
theorem chi_17 (b : State) : chi b 17 = b 17 ^^^ (~~~(b 18) &&& b 19) := rfl
theorem chi_18 (b : State) : chi b 18 = b 18 ^^^ (~~~(b 19) &&& b 15) := rfl
theorem chi_19 (b : State) : chi b 19 = b 19 ^^^ (~~~(b 15) &&& b 16) := rfl
theorem chi_20 (b : State) : chi b 20 = b 20 ^^^ (~~~(b 21) &&& b 22) := rfl
theorem chi_21 (b : State) : chi b 21 = b 21 ^^^ (~~~(b 22) &&& b 23) := rfl
theorem chi_22 (b : State) : chi b 22 = b 22 ^^^ (~~~(b 23) &&& b 24) := rfl
theorem chi_23 (b : State) : chi b 23 = b 23 ^^^ (~~~(b 24) &&& b 20) := rfl
theorem chi_24 (b : State) : chi b 24 = b 24 ^^^ (~~~(b 20) &&& b 21) := rfl

theorem iota_0 (A : State) (rc : Word) : iota A rc 0 = A 0 ^^^ rc := rfl
theorem iota_1 (A : State) (rc : Word) : iota A rc 1 = A 1 := rfl
theorem iota_2 (A : State) (rc : Word) : iota A rc 2 = A 2 := rfl
theorem iota_3 (A : State) (rc : Word) : iota A rc 3 = A 3 := rfl
theorem iota_4 (A : State) (rc : Word) : iota A rc 4 = A 4 := rfl
theorem iota_5 (A : State) (rc : Word) : iota A rc 5 = A 5 := rfl
theorem iota_6 (A : State) (rc : Word) : iota A rc 6 = A 6 := rfl
theorem iota_7 (A : State) (rc : Word) : iota A rc 7 = A 7 := rfl
theorem iota_8 (A : State) (rc : Word) : iota A rc 8 = A 8 := rfl
theorem iota_9 (A : State) (rc : Word) : iota A rc 9 = A 9 := rfl
theorem iota_10 (A : State) (rc : Word) : iota A rc 10 = A 10 := rfl
theorem iota_11 (A : State) (rc : Word) : iota A rc 11 = A 11 := rfl
theorem iota_12 (A : State) (rc : Word) : iota A rc 12 = A 12 := rfl
theorem iota_13 (A : State) (rc : Word) : iota A rc 13 = A 13 := rfl
theorem iota_14 (A : State) (rc : Word) : iota A rc 14 = A 14 := rfl
theorem iota_15 (A : State) (rc : Word) : iota A rc 15 = A 15 := rfl
theorem iota_16 (A : State) (rc : Word) : iota A rc 16 = A 16 := rfl
theorem iota_17 (A : State) (rc : Word) : iota A rc 17 = A 17 := rfl
theorem iota_18 (A : State) (rc : Word) : iota A rc 18 = A 18 := rfl
theorem iota_19 (A : State) (rc : Word) : iota A rc 19 = A 19 := rfl
theorem iota_20 (A : State) (rc : Word) : iota A rc 20 = A 20 := rfl
theorem iota_21 (A : State) (rc : Word) : iota A rc 21 = A 21 := rfl
theorem iota_22 (A : State) (rc : Word) : iota A rc 22 = A 22 := rfl
theorem iota_23 (A : State) (rc : Word) : iota A rc 23 = A 23 := rfl
theorem iota_24 (A : State) (rc : Word) : iota A rc 24 = A 24 := rfl

/-! ## Linear part: theta, rho, pi map the CS complement pattern to `maskB` -/

theorem bvals_complement_0 (s : State) :
    bvals (complement s) 0 = maskB (bvals s) 0 := by
  simp only [bvals, maskB_0, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_1 (s : State) :
    bvals (complement s) 1 = maskB (bvals s) 1 := by
  simp only [bvals, maskB_1, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_2 (s : State) :
    bvals (complement s) 2 = maskB (bvals s) 2 := by
  simp only [bvals, maskB_2, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_3 (s : State) :
    bvals (complement s) 3 = maskB (bvals s) 3 := by
  simp only [bvals, maskB_3, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_4 (s : State) :
    bvals (complement s) 4 = maskB (bvals s) 4 := by
  simp only [bvals, maskB_4, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_5 (s : State) :
    bvals (complement s) 5 = maskB (bvals s) 5 := by
  simp only [bvals, maskB_5, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_6 (s : State) :
    bvals (complement s) 6 = maskB (bvals s) 6 := by
  simp only [bvals, maskB_6, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_7 (s : State) :
    bvals (complement s) 7 = maskB (bvals s) 7 := by
  simp only [bvals, maskB_7, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_8 (s : State) :
    bvals (complement s) 8 = maskB (bvals s) 8 := by
  simp only [bvals, maskB_8, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_9 (s : State) :
    bvals (complement s) 9 = maskB (bvals s) 9 := by
  simp only [bvals, maskB_9, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_10 (s : State) :
    bvals (complement s) 10 = maskB (bvals s) 10 := by
  simp only [bvals, maskB_10, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_11 (s : State) :
    bvals (complement s) 11 = maskB (bvals s) 11 := by
  simp only [bvals, maskB_11, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_12 (s : State) :
    bvals (complement s) 12 = maskB (bvals s) 12 := by
  simp only [bvals, maskB_12, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_13 (s : State) :
    bvals (complement s) 13 = maskB (bvals s) 13 := by
  simp only [bvals, maskB_13, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_14 (s : State) :
    bvals (complement s) 14 = maskB (bvals s) 14 := by
  simp only [bvals, maskB_14, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_15 (s : State) :
    bvals (complement s) 15 = maskB (bvals s) 15 := by
  simp only [bvals, maskB_15, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_16 (s : State) :
    bvals (complement s) 16 = maskB (bvals s) 16 := by
  simp only [bvals, maskB_16, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_17 (s : State) :
    bvals (complement s) 17 = maskB (bvals s) 17 := by
  simp only [bvals, maskB_17, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_18 (s : State) :
    bvals (complement s) 18 = maskB (bvals s) 18 := by
  simp only [bvals, maskB_18, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_19 (s : State) :
    bvals (complement s) 19 = maskB (bvals s) 19 := by
  simp only [bvals, maskB_19, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_20 (s : State) :
    bvals (complement s) 20 = maskB (bvals s) 20 := by
  simp only [bvals, maskB_20, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_21 (s : State) :
    bvals (complement s) 21 = maskB (bvals s) 21 := by
  simp only [bvals, maskB_21, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_22 (s : State) :
    bvals (complement s) 22 = maskB (bvals s) 22 := by
  simp only [bvals, maskB_22, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_23 (s : State) :
    bvals (complement s) 23 = maskB (bvals s) 23 := by
  simp only [bvals, maskB_23, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]
theorem bvals_complement_24 (s : State) :
    bvals (complement s) 24 = maskB (bvals s) 24 := by
  simp only [bvals, maskB_24, complement_0, complement_1, complement_2, complement_3, complement_4, complement_5, complement_6, complement_7, complement_8, complement_9, complement_10, complement_11, complement_12, complement_13, complement_14, complement_15, complement_16, complement_17, complement_18, complement_19, complement_20, complement_21, complement_22, complement_23, complement_24,
    not_xor_left, not_xor_right, rotateLeft_not, BitVec.not_not]

theorem bvals_complement (s : State) : bvals (complement s) = maskB (bvals s) := by
  funext k
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  · exact bvals_complement_0 s
  · exact bvals_complement_1 s
  · exact bvals_complement_2 s
  · exact bvals_complement_3 s
  · exact bvals_complement_4 s
  · exact bvals_complement_5 s
  · exact bvals_complement_6 s
  · exact bvals_complement_7 s
  · exact bvals_complement_8 s
  · exact bvals_complement_9 s
  · exact bvals_complement_10 s
  · exact bvals_complement_11 s
  · exact bvals_complement_12 s
  · exact bvals_complement_13 s
  · exact bvals_complement_14 s
  · exact bvals_complement_15 s
  · exact bvals_complement_16 s
  · exact bvals_complement_17 s
  · exact bvals_complement_18 s
  · exact bvals_complement_19 s
  · exact bvals_complement_20 s
  · exact bvals_complement_21 s
  · exact bvals_complement_22 s
  · exact bvals_complement_23 s
  · exact bvals_complement_24 s
  · omega

/-! ## Nonlinear part: the per-row chi expressions absorb the complements -/

theorem rows_maskB_0 (b : State) (rc : Word) :
    rows (maskB b) rc 0 = complement (iota (chi b) rc) 0 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_0, iota_0, chi_0]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 0).getLsbD ↑i = x0
  all_goals generalize (b 1).getLsbD ↑i = x1
  all_goals generalize (b 2).getLsbD ↑i = x2
  all_goals generalize rc.getLsbD ↑i = r
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> cases r <;> rfl
theorem rows_maskB_1 (b : State) (rc : Word) :
    rows (maskB b) rc 1 = complement (iota (chi b) rc) 1 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_1, iota_1, chi_1]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 1).getLsbD ↑i = x0
  all_goals generalize (b 2).getLsbD ↑i = x1
  all_goals generalize (b 3).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_2 (b : State) (rc : Word) :
    rows (maskB b) rc 2 = complement (iota (chi b) rc) 2 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_2, iota_2, chi_2]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 2).getLsbD ↑i = x0
  all_goals generalize (b 3).getLsbD ↑i = x1
  all_goals generalize (b 4).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_3 (b : State) (rc : Word) :
    rows (maskB b) rc 3 = complement (iota (chi b) rc) 3 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_3, iota_3, chi_3]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 3).getLsbD ↑i = x0
  all_goals generalize (b 4).getLsbD ↑i = x1
  all_goals generalize (b 0).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_4 (b : State) (rc : Word) :
    rows (maskB b) rc 4 = complement (iota (chi b) rc) 4 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_4, iota_4, chi_4]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 4).getLsbD ↑i = x0
  all_goals generalize (b 0).getLsbD ↑i = x1
  all_goals generalize (b 1).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_5 (b : State) (rc : Word) :
    rows (maskB b) rc 5 = complement (iota (chi b) rc) 5 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_5, iota_5, chi_5]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 5).getLsbD ↑i = x0
  all_goals generalize (b 6).getLsbD ↑i = x1
  all_goals generalize (b 7).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_6 (b : State) (rc : Word) :
    rows (maskB b) rc 6 = complement (iota (chi b) rc) 6 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_6, iota_6, chi_6]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 6).getLsbD ↑i = x0
  all_goals generalize (b 7).getLsbD ↑i = x1
  all_goals generalize (b 8).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_7 (b : State) (rc : Word) :
    rows (maskB b) rc 7 = complement (iota (chi b) rc) 7 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_7, iota_7, chi_7]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 7).getLsbD ↑i = x0
  all_goals generalize (b 8).getLsbD ↑i = x1
  all_goals generalize (b 9).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_8 (b : State) (rc : Word) :
    rows (maskB b) rc 8 = complement (iota (chi b) rc) 8 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_8, iota_8, chi_8]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 8).getLsbD ↑i = x0
  all_goals generalize (b 9).getLsbD ↑i = x1
  all_goals generalize (b 5).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_9 (b : State) (rc : Word) :
    rows (maskB b) rc 9 = complement (iota (chi b) rc) 9 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_9, iota_9, chi_9]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 9).getLsbD ↑i = x0
  all_goals generalize (b 5).getLsbD ↑i = x1
  all_goals generalize (b 6).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_10 (b : State) (rc : Word) :
    rows (maskB b) rc 10 = complement (iota (chi b) rc) 10 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_10, iota_10, chi_10]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 10).getLsbD ↑i = x0
  all_goals generalize (b 11).getLsbD ↑i = x1
  all_goals generalize (b 12).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_11 (b : State) (rc : Word) :
    rows (maskB b) rc 11 = complement (iota (chi b) rc) 11 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_11, iota_11, chi_11]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 11).getLsbD ↑i = x0
  all_goals generalize (b 12).getLsbD ↑i = x1
  all_goals generalize (b 13).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_12 (b : State) (rc : Word) :
    rows (maskB b) rc 12 = complement (iota (chi b) rc) 12 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_12, iota_12, chi_12]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 12).getLsbD ↑i = x0
  all_goals generalize (b 13).getLsbD ↑i = x1
  all_goals generalize (b 14).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_13 (b : State) (rc : Word) :
    rows (maskB b) rc 13 = complement (iota (chi b) rc) 13 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_13, iota_13, chi_13]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 13).getLsbD ↑i = x0
  all_goals generalize (b 14).getLsbD ↑i = x1
  all_goals generalize (b 10).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_14 (b : State) (rc : Word) :
    rows (maskB b) rc 14 = complement (iota (chi b) rc) 14 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_14, iota_14, chi_14]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 14).getLsbD ↑i = x0
  all_goals generalize (b 10).getLsbD ↑i = x1
  all_goals generalize (b 11).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_15 (b : State) (rc : Word) :
    rows (maskB b) rc 15 = complement (iota (chi b) rc) 15 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_15, iota_15, chi_15]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 15).getLsbD ↑i = x0
  all_goals generalize (b 16).getLsbD ↑i = x1
  all_goals generalize (b 17).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_16 (b : State) (rc : Word) :
    rows (maskB b) rc 16 = complement (iota (chi b) rc) 16 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_16, iota_16, chi_16]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 16).getLsbD ↑i = x0
  all_goals generalize (b 17).getLsbD ↑i = x1
  all_goals generalize (b 18).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_17 (b : State) (rc : Word) :
    rows (maskB b) rc 17 = complement (iota (chi b) rc) 17 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_17, iota_17, chi_17]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 17).getLsbD ↑i = x0
  all_goals generalize (b 18).getLsbD ↑i = x1
  all_goals generalize (b 19).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_18 (b : State) (rc : Word) :
    rows (maskB b) rc 18 = complement (iota (chi b) rc) 18 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_18, iota_18, chi_18]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 18).getLsbD ↑i = x0
  all_goals generalize (b 19).getLsbD ↑i = x1
  all_goals generalize (b 15).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_19 (b : State) (rc : Word) :
    rows (maskB b) rc 19 = complement (iota (chi b) rc) 19 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_19, iota_19, chi_19]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 19).getLsbD ↑i = x0
  all_goals generalize (b 15).getLsbD ↑i = x1
  all_goals generalize (b 16).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_20 (b : State) (rc : Word) :
    rows (maskB b) rc 20 = complement (iota (chi b) rc) 20 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_20, iota_20, chi_20]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 20).getLsbD ↑i = x0
  all_goals generalize (b 21).getLsbD ↑i = x1
  all_goals generalize (b 22).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_21 (b : State) (rc : Word) :
    rows (maskB b) rc 21 = complement (iota (chi b) rc) 21 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_21, iota_21, chi_21]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 21).getLsbD ↑i = x0
  all_goals generalize (b 22).getLsbD ↑i = x1
  all_goals generalize (b 23).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_22 (b : State) (rc : Word) :
    rows (maskB b) rc 22 = complement (iota (chi b) rc) 22 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_22, iota_22, chi_22]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 22).getLsbD ↑i = x0
  all_goals generalize (b 23).getLsbD ↑i = x1
  all_goals generalize (b 24).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_23 (b : State) (rc : Word) :
    rows (maskB b) rc 23 = complement (iota (chi b) rc) 23 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_23, iota_23, chi_23]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 23).getLsbD ↑i = x0
  all_goals generalize (b 24).getLsbD ↑i = x1
  all_goals generalize (b 20).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl
theorem rows_maskB_24 (b : State) (rc : Word) :
    rows (maskB b) rc 24 = complement (iota (chi b) rc) 24 := by
  simp only [rows, maskB_0, maskB_1, maskB_2, maskB_3, maskB_4, maskB_5, maskB_6, maskB_7, maskB_8, maskB_9, maskB_10, maskB_11, maskB_12, maskB_13, maskB_14, maskB_15, maskB_16, maskB_17, maskB_18, maskB_19, maskB_20, maskB_21, maskB_22, maskB_23, maskB_24, complement_24, iota_24, chi_24]
  all_goals apply BitVec.eq_of_getLsbD_eq; intro i
  all_goals simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_or, i.isLt, decide_true, Bool.true_and]
  all_goals generalize (b 24).getLsbD ↑i = x0
  all_goals generalize (b 20).getLsbD ↑i = x1
  all_goals generalize (b 21).getLsbD ↑i = x2
  all_goals cases x0 <;> cases x1 <;> cases x2 <;> rfl

theorem rows_maskB (b : State) (rc : Word) :
    rows (maskB b) rc = complement (iota (chi b) rc) := by
  funext k
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  · exact rows_maskB_0 b rc
  · exact rows_maskB_1 b rc
  · exact rows_maskB_2 b rc
  · exact rows_maskB_3 b rc
  · exact rows_maskB_4 b rc
  · exact rows_maskB_5 b rc
  · exact rows_maskB_6 b rc
  · exact rows_maskB_7 b rc
  · exact rows_maskB_8 b rc
  · exact rows_maskB_9 b rc
  · exact rows_maskB_10 b rc
  · exact rows_maskB_11 b rc
  · exact rows_maskB_12 b rc
  · exact rows_maskB_13 b rc
  · exact rows_maskB_14 b rc
  · exact rows_maskB_15 b rc
  · exact rows_maskB_16 b rc
  · exact rows_maskB_17 b rc
  · exact rows_maskB_18 b rc
  · exact rows_maskB_19 b rc
  · exact rows_maskB_20 b rc
  · exact rows_maskB_21 b rc
  · exact rows_maskB_22 b rc
  · exact rows_maskB_23 b rc
  · exact rows_maskB_24 b rc
  · omega

/-! ## One round -/

theorem complement_complement (s : State) : complement (complement s) = s := by
  funext k
  simp only [complement]
  cases inCS k <;> simp [BitVec.not_not]

theorem not_eq_xor_allOnes (a : Word) : ~~~a = a ^^^ BitVec.allOnes 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_xor, BitVec.getLsbD_allOnes, i.isLt,
    decide_true, Bool.true_and]
  cases a.getLsbD i <;> rfl

/-- `complementLanes` is "XOR all-ones on lanes {1, 2, 8, 12, 17, 20}". -/
theorem complementLanes_xor_allOnes (s : State) (k : Fin 25) :
    complementLanes s k =
      if k.val ∈ [1, 2, 8, 12, 17, 20] then s k ^^^ BitVec.allOnes 64 else s k := by
  rcases k with ⟨_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|k, hk⟩
  all_goals first
    | omega
    | (rw [complementLanes_eq, ← not_eq_xor_allOnes]; rfl)

theorem complementLanes_complementLanes (s : State) :
    complementLanes (complementLanes s) = s := by
  rw [complementLanes_eq, complementLanes_eq, complement_complement]

/-- **Bertoni round correctness.** Conjugating the transcribed Rust round by
    the entry/exit complement of lanes {1, 2, 8, 12, 17, 20} gives exactly
    one FIPS 202 round Rnd(·, ·) with the same round constant. -/
theorem bertoni_round_correct (s : State) (rc : Word) :
    complementLanes (bertoniRound (complementLanes s) rc) = Spec.round s rc := by
  rw [complementLanes_eq, complementLanes_eq, bertoniRound_factor, bvals_complement,
    rows_maskB, complement_complement, bvals_spec]
  rfl

/-- The same statement, read as: the Rust round is the FIPS round conjugated
    by the lane complement. -/
theorem bertoniRound_conj (t : State) (rc : Word) :
    bertoniRound t rc = complementLanes (Spec.round (complementLanes t) rc) := by
  rw [← bertoni_round_correct, complementLanes_complementLanes,
    complementLanes_complementLanes]

theorem RC_eq : Optimized.RC = Spec.RC := by
  funext i
  simp only [Optimized.RC, Spec.RC, RCrust_eq_spec]

/-! ## The permutation -/

/-- `keccak_p1600::<false>` is Keccak-p[1600, 24] = Keccak-f[1600]. -/
theorem keccak_p1600_false_correct (s : State) :
    keccakP1600 false s = Spec.keccakP 24 s := by
  simp only [keccakP1600, Bool.not_false, ite_true, bertoniRound_conj,
    complementLanes_complementLanes, RC_eq]
  rfl

/-- `keccak_p1600::<true>` is Keccak-p[1600, 12] (rounds 12..23), as used by
    TurboSHAKE (RFC 9861). -/
theorem keccak_p1600_true_correct (s : State) :
    keccakP1600 true s = Spec.keccakP 12 s := by
  simp only [keccakP1600, Bool.not_true, Bool.false_eq_true, ite_false, bertoniRound_conj,
    complementLanes_complementLanes, RC_eq]
  rfl

end SolanaShake.Proof
