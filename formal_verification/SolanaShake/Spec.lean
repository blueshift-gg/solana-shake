/-
  SolanaShake.Spec — Keccak-p[1600, n_r] as specified in FIPS 202 §3.2–3.3.

  This file is the reference side of the proof. Nothing in it refers to the
  Rust code; it is a direct transcription of the FIPS 202 step mappings.

  Conventions (FIPS 202 §3.1.2 / §3.1.3 with w = 64):
  * A state is 25 lanes; lane `x + 5*y` holds `A[x, y, 0..63]`.
  * Bit `z` of a lane is bit `z` of the `BitVec 64` (least-significant first),
    i.e. the little-endian u64 lane used by every Keccak implementation.
  * Rotating a lane "by r" in the FIPS sense (`A'[x,y,z] = A[x,y,(z-r) mod w]`)
    is `BitVec.rotateLeft _ r`, whose `getLsbD` semantics are
    `(x.rotateLeft r).getLsbD z = x.getLsbD ((z - r) mod 64)`.

  Definitions:
  * `theta`, `rho`, `pi`, `chi`, `iota` — FIPS 202 Algorithms 1–4, 6.
  * `rhoOffset` — DEFINED by the walk of FIPS 202 Algorithm 2 (t = 0..23,
    (x, y) starts at (1, 0), offset (t+1)(t+2)/2 mod 64,
    (x, y) := (y, (2x + 3y) mod 5)); lane (0, 0) has offset 0.
  * `piSrc` — DEFINED by the formula of FIPS 202 Algorithm 3:
    `A'[x, y] = A[(x + 3y) mod 5, x]`.
  * `rc` — the LFSR bit function of FIPS 202 Algorithm 5, and `RC` — the 24
    round constants as a literal table.
  * `round` — Rnd(A, i_r) = ι(χ(π(ρ(θ(A))))), FIPS 202 §3.3.
  * `keccakP n_r` — FIPS 202 Algorithm 7 with ℓ = 6: rounds
    i_r = 24 - n_r, …, 23. `keccakP 24` is Keccak-f[1600];
    `keccakP 12` is the Keccak-p[1600, 12] used by TurboSHAKE (RFC 9861).

  Sanity theorems proved here (all by kernel `decide`/`rfl`, no
  `native_decide`):
  * `rhoOffset_eq_table` — the walk produces the standard offset table.
  * `piSrc_eq_table` — π, as "destination lane k reads source lane
    piSrc k", is the table [0,6,12,18,24,3,9,10,16,22,1,7,13,19,20,
    4,5,11,17,23,2,8,14,15,21] (the order in which the Rust round reads
    lanes into b0..b4 of rows 0..4).
  * `RC_eq_lfsr` — each `RC i` equals the value built from `rc(j + 7 i)`
    per FIPS 202 Algorithm 6.
-/

namespace SolanaShake.Spec

/-- One 64-bit lane. -/
abbrev Word := BitVec 64

/-- A Keccak-p[1600] state: lane `x + 5*y` is `A[x, y]`. -/
abbrev State := Fin 25 → Word

/-- Lane index of `A[x, y]` (both coordinates taken mod 5). -/
def idx (x y : Nat) : Fin 25 :=
  ⟨x % 5 + 5 * (y % 5), by omega⟩

/-- `x` coordinate of a lane index. -/
def xOf (k : Fin 25) : Nat := k.val % 5
/-- `y` coordinate of a lane index. -/
def yOf (k : Fin 25) : Nat := k.val / 5

/-! ## θ (FIPS 202 Algorithm 1) -/

/-- `C[x] = A[x,0] ⊕ A[x,1] ⊕ A[x,2] ⊕ A[x,3] ⊕ A[x,4]`. -/
def thetaC (A : State) (x : Nat) : Word :=
  A (idx x 0) ^^^ A (idx x 1) ^^^ A (idx x 2) ^^^ A (idx x 3) ^^^ A (idx x 4)

/-- `D[x] = C[(x-1) mod 5] ⊕ rot(C[(x+1) mod 5], 1)`. -/
def thetaD (A : State) (x : Nat) : Word :=
  thetaC A ((x + 4) % 5) ^^^ (thetaC A ((x + 1) % 5)).rotateLeft 1

/-- `A'[x,y] = A[x,y] ⊕ D[x]`. -/
def theta (A : State) : State :=
  fun k => A k ^^^ thetaD A (xOf k)

/-! ## ρ (FIPS 202 Algorithm 2) -/

/-- The (x, y) positions visited by Algorithm 2, step t = 0..23, paired with
    the offset `(t+1)(t+2)/2 mod 64`. -/
def rhoWalk : Nat → Nat → Nat → List (Fin 25 × Nat)
  | 0, _, _ => []
  | n + 1, x, y =>
    let t := 24 - (n + 1)
    (idx x y, ((t + 1) * (t + 2) / 2) % 64) :: rhoWalk n y ((2 * x + 3 * y) % 5)

/-- The 24 (lane, offset) pairs of Algorithm 2, starting at (x, y) = (1, 0). -/
def rhoSteps : List (Fin 25 × Nat) := rhoWalk 24 1 0

/-- Rotation offset of lane `k`: the offset the walk assigns to it, and 0 for
    lane (0, 0) (which the walk never visits). -/
def rhoOffset (k : Fin 25) : Nat :=
  match rhoSteps.find? (fun p => p.1 == k) with
  | some p => p.2
  | none => 0

/-- `A'[x,y,z] = A[x,y,(z - offset) mod 64]`, i.e. rotate left by the offset. -/
def rho (A : State) : State :=
  fun k => (A k).rotateLeft (rhoOffset k)

/-! ## π (FIPS 202 Algorithm 3) -/

/-- Source lane for destination `(x, y)`: `A'[x,y] = A[(x + 3y) mod 5, x]`. -/
def piSrc (k : Fin 25) : Fin 25 :=
  idx ((xOf k + 3 * yOf k) % 5) (xOf k)

def pi (A : State) : State :=
  fun k => A (piSrc k)

/-! ## χ (FIPS 202 Algorithm 4) -/

/-- `A'[x,y] = A[x,y] ⊕ ((A[(x+1) mod 5, y] ⊕ 1) · A[(x+2) mod 5, y])`. -/
def chi (A : State) : State :=
  fun k => A k ^^^ (~~~(A (idx (xOf k + 1) (yOf k))) &&& A (idx (xOf k + 2) (yOf k)))

/-! ## ι (FIPS 202 Algorithms 5, 6) -/

/-- One LFSR step on the 8-bit register R of Algorithm 5 (as a Nat, bit i =
    R[i]): R = 0 ‖ R; R[0..8] ^= R[8]·(1,0,0,0,1,1,1,0); R = Trunc8(R). -/
def lfsrStep (r : Nat) : Nat :=
  let r := r <<< 1
  let b := (r >>> 8) &&& 1
  (r ^^^ (b * 0x171)) &&& 0xff

/-- `rc(t)` of Algorithm 5 (for t ≥ 0; `t mod 255` is applied as specified). -/
def rc (t : Nat) : Bool :=
  (Nat.repeat lfsrStep (t % 255) 1) &&& 1 == 1

/-- Algorithm 6 steps 2–3: `RC[2^j - 1] = rc(j + 7 i_r)` for j = 0..6. -/
def rcFromLfsr (ir : Nat) : Word :=
  BitVec.ofNat 64 <|
    (List.range 7).foldl
      (fun acc j => if rc (j + 7 * ir) then acc ||| (1 <<< (2 ^ j - 1)) else acc) 0

/-- The 24 round constants of Keccak-f[1600] (standard table). -/
def RCtable : List Word :=
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

/-- Round constant for round index `ir` (0..23). -/
def RC (ir : Nat) : Word := RCtable.getD ir 0

/-- `A'[0,0] = A[0,0] ⊕ RC`. -/
def iota (A : State) (rcv : Word) : State :=
  fun k => if k = 0 then A k ^^^ rcv else A k

/-! ## Rounds and the permutation (FIPS 202 §3.3, Algorithm 7) -/

/-- Rnd(A, i_r) = ι(χ(π(ρ(θ(A)))), RC[i_r]), parameterised by the constant. -/
def round (A : State) (rcv : Word) : State :=
  iota (chi (pi (rho (theta A)))) rcv

/-- Apply rounds `ir, ir+1, …, ir+n-1`. -/
def roundsFrom : Nat → Nat → State → State
  | 0, _, A => A
  | n + 1, ir, A => roundsFrom n (ir + 1) (round A (RC ir))

/-- Keccak-p[1600, n_r] (Algorithm 7, ℓ = 6): rounds `24 - n_r .. 23`. -/
def keccakP (nr : Nat) (A : State) : State :=
  roundsFrom nr (24 - nr) A

/-! ## Sanity theorems -/

/-- Standard ρ offset table, lane order `x + 5y`. -/
def rhoTable : List Nat :=
  [ 0,  1, 62, 28, 27,
   36, 44,  6, 55, 20,
    3, 10, 43, 25, 39,
   41, 45, 15, 21,  8,
   18,  2, 61, 56, 14]

theorem rhoOffset_eq_table : ∀ k : Fin 25, rhoOffset k = rhoTable.getD k.val 0 := by
  decide

/-- π source-lane table: destination lane k (b_x of row y, k = x + 5y)
    reads source lane `piTable[k]`. -/
def piTable : List Nat :=
  [0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20,
   4, 5, 11, 17, 23, 2, 8, 14, 15, 21]

theorem piSrc_eq_table : ∀ k : Fin 25, (piSrc k).val = piTable.getD k.val 0 := by
  decide

/-- π is a permutation of the lanes (its source map is injective). -/
theorem piSrc_injective : ∀ j k : Fin 25, piSrc j = piSrc k → j = k := by
  decide

/-- FIPS 202 §3.2.3 formula, restated: `π(A)[x, y] = A[(x + 3y) mod 5, x]`. -/
theorem pi_spec (A : State) (x y : Nat) (hx : x < 5) :
    pi A (idx x y) = A (idx ((x + 3 * y) % 5) x) := by
  simp only [pi, piSrc, xOf, yOf, idx]
  congr 3 <;> omega

theorem RC_eq_lfsr : ∀ i : Fin 24, RC i.val = rcFromLfsr i.val := by
  decide

end SolanaShake.Spec
