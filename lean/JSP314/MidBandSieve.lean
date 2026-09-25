import JSP314.AntiSieveCore
import JSP314.BandLarge
import JSP314.SmallBandZ
import Mathlib.Tactic

/-!
# JSP-000314 — the mid band of `runCountSum`

This file assembles the *middle* band of the run-count decomposition
`runCountSum x` from `BandSum.lean`, i.e. the contribution of primes `p`
with `Z < p ≤ √(2x)` lying between the small-`p` band (`SmallBandZ`) and the
large-`p` band (`p⁴ > 2x`, `BandLarge`).

Three ingredients, each elementary:

1. **Residue-class count for the anti-sieve set.**
   `smoothCongruentOne_card_le_div`: every `s ∈ smoothCongruentOne N p`
   satisfies `s ≡ 1 (mod p²)` (via `mem_smoothCongruentOne`), hence lies in a
   single residue class mod `p²`, so
   `(smoothCongruentOne N p).card ≤ N / p² + 1`
   (`card_residue_class_le` from `AntiSieveCore`).
   Consequence `rightRunCount_one_le_div_add`:
   `rightRunCount x p 1 ≤ 2x / p² + 2`.

2. **Per-prime inner-sum bound.**  `T_k = rightRunCount + leftRunCount` is
   antitone in `k` (`rightRunCount_anti'`, `leftRunCount_anti'` in
   `BandLarge`), so
   `midBand_inner_le`:
   `∑_{k ≤ 2p} T_k ≤ 2·(2p)·T₁`, with the sharper
   `midBand_inner_le'`: `∑_{k ≤ 2p} T_k ≤ (2p)·T₁`.

3. **Band assembly.**  Combining `T₁ ≤ 2·(2x/p²)` (`rightRunCount_le_div`,
   `leftRunCount_le_div`) with the inner bound gives, for any cutoff `Z`,

   `midBandSum_le`:
   `∑_{Z < p ≤ √(2x), p prime} ∑_{k ≤ 2p} T_k ≤ 8x·∑_{Z < p ≤ √(2x)} 1/p`
   (as reals).  Two corollaries bound the reciprocal sum:
   `midBandSum_le_log` via `∑_{p ≤ y} 1/p ≤ 1 + log y`
   (`sum_primesLE_inv_le` in `AntiSieveCore`), and
   `midBandSum_le_card_div` via the count bound `≤ (√(2x) + 1)/(Z + 1)`
   (`card_primesLE_le`).
-/

namespace JSP314

open Finset

/-! ### 1. Residue-class bound for `smoothCongruentOne` -/

/-- Every `s ∈ smoothCongruentOne N p` lies in the single class `1 mod p²`,
so its cardinality is at most `N / p² + 1`. -/
theorem smoothCongruentOne_card_le_div (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card ≤ N / p ^ 2 + 1 := by
  classical
  have hsub : smoothCongruentOne N p ⊆
      (Finset.Icc 1 N).filter (fun s => s ≡ 1 [MOD p ^ 2]) := by
    intro s hs
    obtain ⟨hs2, hsN, -, hmod⟩ := mem_smoothCongruentOne.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hsN⟩, (modEq_one_iff hp).mpr hmod⟩
  exact (Finset.card_le_card hsub).trans (card_residue_class_le N (p ^ 2) 1)

/-- Consequence for the run count: `rightRunCount x p 1 ≤ 2x / p² + 2`
(each `k = 1` right witness `m` gives `s = m + 1 ≡ 1 (mod p²)`, and
`(2x + 1) / p² ≤ 2x / p² + 1`). -/
theorem rightRunCount_one_le_div_add (x p : ℕ) (hp : p.Prime) :
    rightRunCount x p 1 ≤ 2 * x / p ^ 2 + 2 := by
  calc rightRunCount x p 1
      ≤ (smoothCongruentOne (2 * x + 1) p).card :=
        rightRunCount_one_le_smoothCongruentOne hp
    _ ≤ (2 * x + 1) / p ^ 2 + 1 :=
        smoothCongruentOne_card_le_div _ _ hp.two_le
    _ ≤ 2 * x / p ^ 2 + 2 := by
        have h : (2 * x + 1) / p ^ 2 ≤ 2 * x / p ^ 2 + 1 := by
          rcases Nat.eq_zero_or_pos (p ^ 2) with hb | hb
          · simp [hb]
          · rw [Nat.div_le_iff_le_mul_add_pred hb]
            have hdm : p ^ 2 * (2 * x / p ^ 2) + 2 * x % p ^ 2 = 2 * x :=
              Nat.div_add_mod _ _
            have hmod : 2 * x % p ^ 2 < p ^ 2 := Nat.mod_lt _ hb
            have hexp : p ^ 2 * (2 * x / p ^ 2 + 1) =
                p ^ 2 * (2 * x / p ^ 2) + p ^ 2 := by ring
            rw [hexp]
            omega
        omega

/-! ### 2. Per-prime inner-sum bound -/

/-- Antitonicity in `k` gives `T_k ≤ T₁` for all `k ≥ 1`, so the inner
`k`-sum is at most `(2p)·T₁`. -/
theorem midBand_inner_le' (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)
      ≤ (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1) := by
  calc ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ _k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p 1 + leftRunCount x p 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        exact Nat.add_le_add (rightRunCount_anti' hk1) (leftRunCount_anti' hk1)
    _ = (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc,
          Nat.add_sub_cancel]

/-- The headline inner bound of the task statement:
`∑_{k ≤ 2p} T_k ≤ 2·(2p)·T₁`. -/
theorem midBand_inner_le (x p : ℕ) (hp : p.Prime) :
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)
      ≤ 2 * (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1) :=
  (midBand_inner_le' x p).trans (by
    rw [show 2 * (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1)
        = (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1)
          + (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1) by ring]
    exact Nat.le_add_right _ _)

/-! ### 3. Band assembly -/

/-- **Mid-band bound (prime-reciprocal form).**  For any cutoff `Z`,
the `k`-summed run counts over the primes `Z < p ≤ √(2x)` are at most
`8x` times the reciprocal sum over those primes:
`T₁ ≤ 2·(2x/p²)` gives `∑_{k} T_k ≤ 2p·T₁ ≲ 8x/p` per prime. -/
theorem midBandSum_le (x Z : ℕ) :
    ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)) : ℝ)
      ≤ 8 * (x : ℝ) *
        ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
          (1 : ℝ) / p := by
  have key : ∀ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
      ((∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
        ≤ 8 * (x : ℝ) / p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h1 := midBand_inner_le' x p
    have h2 := rightRunCount_le_div x p 1 hpp
    have h3 := leftRunCount_le_div x p 1 hpp
    have h4 : (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1)
        ≤ (2 * p) * (2 * (2 * x / p ^ 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : ((∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
        ≤ (((2 * p) * (2 * (2 * x / p ^ 2)) : ℕ) : ℝ) := by
      exact_mod_cast h1.trans h4
    calc ((∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
        ≤ (((2 * p) * (2 * (2 * x / p ^ 2)) : ℕ) : ℝ) := h5
      _ = (2 * p : ℝ) * (2 * ((2 * x / p ^ 2 : ℕ) : ℝ)) := by
          push_cast
          ring
      _ ≤ (2 * p : ℝ) * (2 * ((2 * x : ℝ) / (p : ℝ) ^ 2)) := by
          have hcd : ((2 * x / p ^ 2 : ℕ) : ℝ) ≤
              ((2 * x : ℕ) : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
          simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcd
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcd (by norm_num)) (by positivity)
      _ = 8 * (x : ℝ) / p := by
          have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
          field_simp
          ring
  calc (∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
          ∑ k ∈ Finset.Icc 1 (2 * p),
            ((rightRunCount x p k : ℝ) + leftRunCount x p k))
      = ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
          ((∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) := by
        simp only [Nat.cast_sum, Nat.cast_add]
    _ ≤ ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
          (8 * (x : ℝ) / p) :=
        Finset.sum_le_sum fun p hp => key p hp
    _ = 8 * (x : ℝ) * ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
          (fun p => Z < p), (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [mul_one_div]

/-- Extending the reciprocal sum to *all* primes `≤ √(2x)` and using
`∑_{p ≤ y} 1/p ≤ 1 + log y` gives the log-scale bound
`midBandSum x Z ≤ 8x·(1 + log √(2x))`. -/
theorem midBandSum_le_log (x Z : ℕ) :
    ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)) : ℝ)
      ≤ 8 * (x : ℝ) * (1 + Real.log (Nat.sqrt (2 * x))) := by
  refine (midBandSum_le x Z).trans ?_
  calc 8 * (x : ℝ) * ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
          (fun p => Z < p), (1 : ℝ) / p
      ≤ 8 * (x : ℝ) * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (1 : ℝ) / p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p _ _
        positivity
    _ ≤ 8 * (x : ℝ) * (1 + Real.log (Nat.sqrt (2 * x))) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_le _) (by positivity)

/-- The crude count bound: each prime in the band is `> Z`, so `1/p ≤ 1/(Z+1)`
and the reciprocal sum is at most `π(√(2x))/(Z+1) ≤ (√(2x)+1)/(Z+1)`. -/
theorem midBandSum_le_card_div (x Z : ℕ) :
    ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)) : ℝ)
      ≤ 8 * (x : ℝ) * ((Nat.sqrt (2 * x) : ℝ) + 1) / (Z + 1) := by
  refine (midBandSum_le x Z).trans ?_
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcard : (((Nat.primesLE (Nat.sqrt (2 * x))).filter
        (fun p => Z < p)).card : ℝ) ≤ (Nat.sqrt (2 * x) : ℝ) + 1 := by
    have hsub : ((Nat.primesLE (Nat.sqrt (2 * x))).filter
          (fun p => Z < p)).card
        ≤ (Nat.primesLE (Nat.sqrt (2 * x))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hcap := card_primesLE_le (Nat.sqrt (2 * x))
    exact_mod_cast hsub.trans hcap
  calc ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
        (1 : ℝ) / p
      ≤ ∑ _p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
          (1 : ℝ) / (Z + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hZp : Z < p := (Finset.mem_filter.mp hp).2
        have hle : (Z : ℝ) + 1 ≤ (p : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hZp)
        exact one_div_le_one_div_of_le (by positivity) hle
    _ = (((Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p)).card : ℝ)
          / (Z + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ ((Nat.sqrt (2 * x) : ℝ) + 1) / (Z + 1) := by
        simp only [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

end JSP314
