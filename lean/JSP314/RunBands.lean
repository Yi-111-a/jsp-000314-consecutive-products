import JSP314.BandSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# JSP-000314 — prime-band splitting of `runCountSum`

This file splits the run-count double sum
`runCountSum x = ∑_{p ≤ √(2x), p prime} ∑_{k ≤ 2p} (right + left)` into
*prime bands* `(lo, hi]` via the interval decomposition
`Ioc 0 √(2x) = Ioc 0 Z ∪ Ioc Z W ∪ Ioc W √(2x)` and the Mathlib bridge
`Nat.primesLE_eq_filter_Ioc_zero`.

Contents:

* `bandInnerSum x p` — the per-prime inner sum `∑_{k ∈ [1,2p]} (right+left)`.
* `bandSum x lo hi` — `runCountSum` restricted to primes `p ∈ Ioc lo hi`.
* `bandSum_add_bandSum` — adjacent-band gluing
  `bandSum x a b + bandSum x b c = bandSum x a c`.
* `runCountSum_eq_bandSum_add` — two-band split of `runCountSum`.
* `runCountSum_eq_three_bands` — three-band split for `Z ≤ W ≤ √(2x)`.
* `badNonSingletonCount_le_bands` — the master hypothesis-driven assembly
  `N(x) ≤ 2·(B(0,Z] + B(Z,W] + B(W,√(2x)]) + (2·10^16+1)`.
* Monotonicity/bounding helpers: `bandSum_mono`, `bandSum_mono_right`,
  `bandSum_mono_left`, `bandSum_le_of_forall`, `bandSum_le_sum`,
  `bandSum_le_card_mul`, `bandSum_eq_zero_of_le`.
-/

namespace JSP314

/-- The per-prime inner summand of `runCountSum`:
`∑_{k ∈ [1, 2p]} (rightRunCount x p k + leftRunCount x p k)`. -/
noncomputable def bandInnerSum (x p : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- `runCountSum` restricted to the prime band `(lo, hi]`:
the sum over primes `p ∈ Ioc lo hi` of `bandInnerSum x p`. -/
noncomputable def bandSum (x lo hi : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, bandInnerSum x p

/-- `bandInnerSum` agrees definitionally with the raw `runCountSum` inner
term; exposed for rewriting. -/
theorem bandInnerSum_def (x p : ℕ) :
    bandInnerSum x p =
      ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k) :=
  rfl

/-- The band sum as an `ite`-sum over the whole interval `Ioc lo hi`. -/
theorem bandSum_eq_sum_Ioc_ite (x lo hi : ℕ) :
    bandSum x lo hi =
      ∑ p ∈ Finset.Ioc lo hi, (if p.Prime then bandInnerSum x p else 0) := by
  show ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, bandInnerSum x p = _
  exact Finset.sum_filter _ _

/-- Adjacent bands glue: `(a,b] ∪ (b,c] = (a,c]` for `a ≤ b ≤ c`, and the two
intervals are disjoint, so the filtered sums add. -/
theorem bandSum_add_bandSum (x a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    bandSum x a b + bandSum x b c = bandSum x a c := by
  rw [bandSum_eq_sum_Ioc_ite, bandSum_eq_sum_Ioc_ite,
    bandSum_eq_sum_Ioc_ite]
  exact Finset.sum_Ioc_consecutive _ hab hbc

/-- **Two-band split of `runCountSum`.**  For `Z ≤ √(2x)`,
`Nat.primesLE √(2x) = (Ioc 0 Z).filter Prime ∪ (Ioc Z √(2x)).filter Prime`. -/
theorem runCountSum_eq_bandSum_add (x Z : ℕ)
    (hZ : Z ≤ Nat.sqrt (2 * x)) :
    runCountSum x = bandSum x 0 Z + bandSum x Z (Nat.sqrt (2 * x)) := by
  show (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), bandInnerSum x p) = _
  rw [Nat.primesLE_eq_filter_Ioc_zero, Finset.sum_filter,
    bandSum_eq_sum_Ioc_ite, bandSum_eq_sum_Ioc_ite]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le Z) hZ).symm

/-- **Three-band split of `runCountSum`** for `Z ≤ W ≤ √(2x)`. -/
theorem runCountSum_eq_three_bands (x Z W : ℕ) (hZ : Z ≤ W)
    (hW : W ≤ Nat.sqrt (2 * x)) :
    runCountSum x =
      bandSum x 0 Z + bandSum x Z W + bandSum x W (Nat.sqrt (2 * x)) := by
  rw [runCountSum_eq_bandSum_add x Z (hZ.trans hW),
    ← bandSum_add_bandSum x Z W _ hZ hW, add_assoc]

/-- **Master hypothesis-driven assembly.**  Combining the three-band split
with `BandSum.badNonSingletonCount_le_two_mul_runCountSum_add_const`:
`N(x) ≤ 2·(bandSum(0,Z] + bandSum(Z,W] + bandSum(W,√(2x)]) + (2·10^16+1)`. -/
theorem badNonSingletonCount_le_bands (x Z W : ℕ) (hZ : Z ≤ W)
    (hW : W ≤ Nat.sqrt (2 * x)) :
    badNonSingletonCount x ≤
      2 * (bandSum x 0 Z + bandSum x Z W + bandSum x W (Nat.sqrt (2 * x))) +
        (2 * 10 ^ 16 + 1) := by
  have h := badNonSingletonCount_le_two_mul_runCountSum_add_const x
  rwa [runCountSum_eq_three_bands x Z W hZ hW] at h

/-- Two-band variant of the assembly, needing only `Z ≤ √(2x)`. -/
theorem badNonSingletonCount_le_two_bands (x Z : ℕ)
    (hZ : Z ≤ Nat.sqrt (2 * x)) :
    badNonSingletonCount x ≤
      2 * (bandSum x 0 Z + bandSum x Z (Nat.sqrt (2 * x))) +
        (2 * 10 ^ 16 + 1) := by
  have h := badNonSingletonCount_le_two_mul_runCountSum_add_const x
  rwa [runCountSum_eq_bandSum_add x Z hZ] at h

/-- Empty-band vanishing: `Ioc lo hi = ∅` when `hi ≤ lo`. -/
theorem bandSum_eq_zero_of_le {x lo hi : ℕ} (h : hi ≤ lo) :
    bandSum x lo hi = 0 := by
  show ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, bandInnerSum x p = 0
  rw [Finset.Ioc_eq_empty_of_le h]
  simp

/-- Monotonicity of `bandSum` under band inclusion (all summands are
nonnegative naturals). -/
theorem bandSum_mono {x : ℕ} {a b c d : ℕ}
    (h : Finset.Ioc a b ⊆ Finset.Ioc c d) :
    bandSum x a b ≤ bandSum x c d := by
  show ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, bandInnerSum x p ≤
    ∑ p ∈ (Finset.Ioc c d).filter Nat.Prime, bandInnerSum x p
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter Nat.Prime h) (fun i _ _ ↦ Nat.zero_le _)

/-- Enlarging the right endpoint enlarges the band sum. -/
theorem bandSum_mono_right {x lo : ℕ} {hi₁ hi₂ : ℕ} (h : hi₁ ≤ hi₂) :
    bandSum x lo hi₁ ≤ bandSum x lo hi₂ :=
  bandSum_mono (Finset.Ioc_subset_Ioc_right h)

/-- Shrinking the left endpoint enlarges the band sum. -/
theorem bandSum_mono_left {x : ℕ} {lo₁ lo₂ hi : ℕ} (h : lo₂ ≤ lo₁) :
    bandSum x lo₁ hi ≤ bandSum x lo₂ hi :=
  bandSum_mono (Finset.Ioc_subset_Ioc_left h)

/-- Pointwise per-prime bounds on `bandInnerSum` lift to `bandSum`, summed
over the primes in the band. -/
theorem bandSum_le_of_forall {x lo hi : ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, bandInnerSum x p ≤ f p) :
    bandSum x lo hi ≤ ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, f p :=
  Finset.sum_le_sum fun p hp ↦ h p hp

/-- Pointwise per-prime bounds lift to `bandSum`, summed over the whole
interval `Ioc lo hi` (non-prime indices contribute `f p` unconditionally). -/
theorem bandSum_le_sum {x lo hi : ℕ} {f : ℕ → ℕ}
    (h : ∀ p ∈ Finset.Ioc lo hi, p.Prime → bandInnerSum x p ≤ f p) :
    bandSum x lo hi ≤ ∑ p ∈ Finset.Ioc lo hi, f p := by
  rw [bandSum_eq_sum_Ioc_ite]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  split
  · next hP => exact h p hp hP
  · exact Nat.zero_le _

/-- A uniform per-prime bound `bandInnerSum x p ≤ C` on the band gives
`bandSum ≤ (# primes in band)·C`. -/
theorem bandSum_le_card_mul {x lo hi C : ℕ}
    (h : ∀ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, bandInnerSum x p ≤ C) :
    bandSum x lo hi ≤ ((Finset.Ioc lo hi).filter Nat.Prime).card * C := by
  calc bandSum x lo hi
      ≤ ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, C :=
        bandSum_le_of_forall h
    _ = ((Finset.Ioc lo hi).filter Nat.Prime).card * C := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

end JSP314
