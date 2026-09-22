import JSP314.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# JSP-000314 — elementary bounds relating `B` and `badSingletonCount`

This file proves the easy comparison facts:

* a degenerate interval `[n, n]` is bad iff `1 < n` and `P(n)^2 ∣ n`
  (`isBadInterval_self_iff`);
* every singleton bad point is covered by the bad interval `[n, n]`, so
  `badSingletonCount x ≤ B x` (`badSingletonCount_le_B`);
* `B x ≤ x + 1` (`B_le`);
* real-valued versions of the above bounds;
* a lower bound on `badSingletonCount` in terms of prime squares
  (`badSingletonCount_ge_prime_sq`), using the auxiliary fact
  `largestPrimeFactor_prime_sq_self : largestPrimeFactor (p^2) = p`.
-/

namespace JSP314

open Classical

/-- The product over a singleton interval `[n, n]` is `n` itself. -/
private theorem prod_Icc_self_eq (n : ℕ) : (Finset.Icc n n).prod id = n := by
  simp

/-- A degenerate interval `[n, n]` is bad iff `1 < n` and `P(n)^2 ∣ n`. -/
theorem isBadInterval_self_iff {n : ℕ} :
    IsBadInterval n n ↔ 1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n := by
  have hprod : (Finset.Icc n n).prod id = n := prod_Icc_self_eq n
  unfold IsBadInterval
  show n ≤ n ∧ _ ↔ _
  rw [hprod]
  show n ≤ n ∧ largestPrimeFactor n ≠ 1 ∧ (largestPrimeFactor n) ^ 2 ∣ n ↔ _
  simp only [le_refl, true_and]
  constructor
  · rintro ⟨hP, hdiv⟩
    refine ⟨?_, hdiv⟩
    by_contra h1
    exact hP (largestPrimeFactor_eq_one_iff.mpr (not_lt.mp h1))
  · rintro ⟨h1, hdiv⟩
    exact ⟨fun hP => absurd (largestPrimeFactor_eq_one_iff.mp hP) (by omega), hdiv⟩

/-- Every `n` with `P(n)^2 ∣ n` is covered by the bad interval `[n, n]`. -/
theorem badSingletonCount_le_B (x : ℕ) : badSingletonCount x ≤ B x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, n, n, isBadInterval_self_iff.mpr hn.2, le_refl n, le_refl n⟩

/-- `B x` counts a subset of `range (x + 1)`. -/
theorem B_le (x : ℕ) : B x ≤ x + 1 := by
  show ((Finset.range (x + 1)).filter _).card ≤ x + 1
  calc ((Finset.range (x + 1)).filter _).card
      ≤ (Finset.range (x + 1)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = x + 1 := Finset.card_range (x + 1)

/-- Real-valued version of `badSingletonCount_le_B`. -/
theorem badSingletonCount_le_B_real (x : ℕ) :
    (badSingletonCount x : ℝ) ≤ (B x : ℝ) := by
  exact_mod_cast badSingletonCount_le_B x

/-- The difference `B x - badSingletonCount x` is nonnegative. -/
theorem B_sub_badSingletonCount_nonneg (x : ℕ) :
    (0 : ℝ) ≤ (B x : ℝ) - (badSingletonCount x : ℝ) :=
  sub_nonneg.mpr (badSingletonCount_le_B_real x)

/-- The difference `B x - badSingletonCount x` is at most `x + 1`. -/
theorem B_sub_badSingletonCount_le (x : ℕ) :
    (B x : ℝ) - (badSingletonCount x : ℝ) ≤ (x : ℝ) + 1 := by
  have hB : (B x : ℝ) ≤ (x : ℝ) + 1 := by exact_mod_cast B_le x
  have h0 : (0 : ℝ) ≤ (badSingletonCount x : ℝ) := by positivity
  linarith

/-- Absolute-value bound: `|B x - badSingletonCount x| ≤ x + 1`. -/
theorem abs_B_sub_badSingletonCount_le (x : ℕ) :
    |(B x : ℝ) - (badSingletonCount x : ℝ)| ≤ (x : ℝ) + 1 := by
  rw [abs_of_nonneg (B_sub_badSingletonCount_nonneg x)]
  exact B_sub_badSingletonCount_le x

/-- Every prime square `p^2 ≤ x` is a singleton bad point. -/
theorem badSingletonCount_ge_prime_sq (x : ℕ) :
    ((Finset.range (x + 1)).filter
        (fun n => ∃ p : ℕ, Nat.Prime p ∧ n = p ^ 2 ∧ p ^ 2 ≤ x)).card ≤
      badSingletonCount x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  obtain ⟨hnx, p, hp, rfl, -⟩ := hn
  have h2 : 2 ≤ p ^ 2 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left hp.two_le 2)
  have h1 : 1 < p ^ 2 := lt_of_lt_of_le (by norm_num) h2
  refine ⟨hnx, h1, ?_⟩
  rw [largestPrimeFactor_prime_sq_self hp]

end JSP314
