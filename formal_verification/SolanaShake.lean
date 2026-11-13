-- Formal verification of the Bertoni lane-complementing Keccak-p[1600]
-- permutation in `src/lib.rs` (`keccak_p1600::<TURBO>`), Lean 4 core only.
--
--   SolanaShake.Spec      FIPS 202 §3.2–3.3 reference (θ, ρ, π, χ, ι, Rnd,
--                         Keccak-p[1600, n_r]) and table sanity theorems.
--   SolanaShake.Optimized Line-by-line transcription of the Rust round and
--                         of `keccak_p1600::<TURBO>`.
--   SolanaShake.Proof     `bertoni_round_correct`,
--                         `keccak_p1600_false_correct` (= Keccak-p[1600, 24]),
--                         `keccak_p1600_true_correct`  (= Keccak-p[1600, 12]).
--
-- See the header of SolanaShake/Proof.lean for the trust base and for how the
-- Lean transcription is linked to the Rust code.
import SolanaShake.Spec
import SolanaShake.Optimized
import SolanaShake.Proof
