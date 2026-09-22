import JSP314.Main

/-!
# JSP-000314 — AnalyticCore: honest partial results toward `N(x) ≤ (log x)^{-1+ε} · S(x)`

This file records what can currently be proved about `badNonSingletonCount`
(the count `N(x)` of `n ≤ x` lying in a non-singleton bad interval) **without**
the deep analytic input of Tao's Ta26c paper, and documents precisely which
mathematical ingredient is missing for the headline bound
`badNonSingleton_interval_bound`.

## What is proved here (no placeholders)

* `badNonSingletonCount_le`, `badNonSingletonCount_le_real`: `N(x) ≤ x + 1`
  (the counted set is a subset of `range (x+1)`).
* `badNonSingletonCount_le_B`: `N(x) ≤ B(x)` (a non-singleton bad interval is,
  in particular, a bad interval).
* `badNonSingletonCount_mono`: `N` is monotone in `x`.
* `not_inNonSingletonBadInterval_zero`, `badNonSingletonCount_zero`: `N(0) = 0`.
  Any non-singleton bad interval covering `0` must start at `u = 0`, and then
  `0 ∈ Icc 0 v` forces the product to be `0`, whose largest prime factor is `1`
  by convention — contradicting badness.
* `largestPrimeFactor_72`, `isBadInterval_8_9`, `inNonSingletonBadInterval_8`,
  `inNonSingletonBadInterval_9`, `two_le_badNonSingletonCount_nine`,
  `badNonSingletonCount_eventually_two_le`: the interval `[8, 9]` is bad
  (product `72 = 2³·3²`, largest prime factor `3`, `3² ∣ 72`), so `N(x) ≥ 2`
  for all `x ≥ 9` — the target bound is genuinely non-vacuous.
* `badNonSingletonCount_eventually_le`, `badNonSingletonCount_isBigO`:
  `N(x) = O(x)`, the best unconditional growth statement currently available.

## Why `badNonSingleton_interval_bound` is not provable here

The claim `N(x) ≤ (log x)^{-1+ε} · S(x)` is *not* degenerate in either
direction:

* It is not vacuous: `N(x) ≥ 2` for `x ≥ 9` (proved below via `[8,9]`), and in
  fact `N(x)` is expected to grow like `x` times a negative power of `log x`.
* The trivial bound `N(x) ≤ x + 1` is useless against the RHS: `S(x) = o(x)`
  (bad singletons have density `0`) and `(log x)^{-1+ε} → 0`, so the RHS is
  `o(S(x)) = o(x)` — strictly smaller than any bound obtainable from
  `N(x) ≤ x + 1` alone. One must prove `N(x)/S(x) → 0` at a polylogarithmic
  rate.

The missing mathematical input is the analytic core of Ta26c (~50 pages):
if `[u,v]` is bad with largest prime factor `p`, then either some element of
`[u,v]` is divisible by `p²` (so covered points cluster near multiples of
`p²`), or two distinct elements are divisible by `p` (forcing `v - u ≥ p`).
Bounding `N(x)` then requires (i) structural dichotomies of this kind,
(ii) upper bounds on `y`-smooth numbers in short intervals and on integers
close to `p²`-multiples, and (iii) a covering/summation argument showing these
configurations contribute `o((log x)^{-1+ε} · S(x))`. None of steps (i)–(iii)
is available in Mathlib, and there is no elementary shortcut.
-/

namespace JSP314

open Nat Filter Classical Asymptotics

/-- `N(x)` counts a subset of `range (x + 1)`. -/
theorem badNonSingletonCount_le (x : ℕ) : badNonSingletonCount x ≤ x + 1 := by
  show ((Finset.range (x + 1)).filter _).card ≤ x + 1
  rw [← Finset.card_range (x + 1)]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Real-valued version of `badNonSingletonCount_le`. -/
theorem badNonSingletonCount_le_real (x : ℕ) :
    (badNonSingletonCount x : ℝ) ≤ (x : ℝ) + 1 := by
  exact_mod_cast badNonSingletonCount_le x

/-- A non-singleton bad interval is a bad interval, so `N(x) ≤ B(x)`. -/
theorem badNonSingletonCount_le_B (x : ℕ) : badNonSingletonCount x ≤ B x := by
  unfold badNonSingletonCount B
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  obtain ⟨hnx, u, v, -, hbad, hun, hnv⟩ := hn
  exact ⟨hnx, u, v, hbad, hun, hnv⟩

/-- `badNonSingletonCount` is monotone in its argument. -/
theorem badNonSingletonCount_mono : Monotone badNonSingletonCount := by
  intro x y hxy
  unfold badNonSingletonCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- `0` lies in no non-singleton bad interval: such an interval would have to
start at `u = 0`, and then `0` is a factor of the interval product, forcing
`largestPrimeFactor = 1`. -/
theorem not_inNonSingletonBadInterval_zero : ¬ InNonSingletonBadInterval 0 := by
  rintro ⟨u, v, -, hbad, hu0, -⟩
  obtain rfl : u = 0 := by omega
  have hprod0 : (Finset.Icc 0 v).prod id = 0 :=
    Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨le_refl 0, zero_le v⟩) rfl
  obtain ⟨-, hP, -⟩ := hbad
  rw [hprod0] at hP
  exact hP (largestPrimeFactor_eq_one_iff.mpr (Nat.zero_le 0))

/-- `N(0) = 0`: the only candidate point `n = 0` is never covered. -/
theorem badNonSingletonCount_zero : badNonSingletonCount 0 = 0 := by
  unfold badNonSingletonCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_range] at hn
  obtain rfl : n = 0 := by omega
  exact not_inNonSingletonBadInterval_zero

/-- The largest prime factor of `72 = 2³·3²` is `3`, proved without evaluating
the noncomputable `largestPrimeFactor` (upper bound: every prime divisor of `72`
is `2` or `3`; lower bound: `3 ∣ 72`). -/
theorem largestPrimeFactor_72 : largestPrimeFactor 72 = 3 := by
  have hP : Nat.Prime (largestPrimeFactor 72) := largestPrimeFactor_prime (by norm_num)
  have hdvd : largestPrimeFactor 72 ∣ 72 := largestPrimeFactor_dvd (by norm_num)
  apply le_antisymm
  · -- `P ∣ 72 = 8·9` and `P` prime forces `P ∈ {2, 3}`.
    have hdvd' : largestPrimeFactor 72 ∣ 8 * 9 :=
      hdvd.trans (dvd_of_eq (by norm_num))
    rcases hP.dvd_mul.mp hdvd' with h8 | h9
    · have h2 : largestPrimeFactor 72 ∣ 2 ^ 3 :=
        h8.trans (dvd_of_eq (by norm_num))
      have h : largestPrimeFactor 72 = 2 :=
        (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp (hP.dvd_of_dvd_pow h2)
      omega
    · have h3 : largestPrimeFactor 72 ∣ 3 ^ 2 :=
        h9.trans (dvd_of_eq (by norm_num))
      have h : largestPrimeFactor 72 = 3 :=
        (Nat.prime_dvd_prime_iff_eq hP Nat.prime_three).mp (hP.dvd_of_dvd_pow h3)
      exact h.le
  · exact prime_dvd_le_largestPrimeFactor (by norm_num) Nat.prime_three (by norm_num)

/-- The interval `[8, 9]` is bad: its product is `72`, whose largest prime
factor `3` satisfies `3² ∣ 72`. This is the concrete witness showing that
non-singleton bad intervals exist, so `N(x)` is genuinely nonzero. -/
theorem isBadInterval_8_9 : IsBadInterval 8 9 := by
  have hprod : (Finset.Icc 8 9).prod id = 72 := by decide
  show 8 ≤ 9 ∧ largestPrimeFactor ((Finset.Icc 8 9).prod id) ≠ 1 ∧
    largestPrimeFactor ((Finset.Icc 8 9).prod id) ^ 2 ∣ (Finset.Icc 8 9).prod id
  rw [hprod, largestPrimeFactor_72]
  exact ⟨by norm_num, by norm_num, by norm_num⟩

/-- `8` is covered by the non-singleton bad interval `[8, 9]`. -/
theorem inNonSingletonBadInterval_8 : InNonSingletonBadInterval 8 :=
  ⟨8, 9, by norm_num, isBadInterval_8_9, by norm_num, by norm_num⟩

/-- `9` is covered by the non-singleton bad interval `[8, 9]`. -/
theorem inNonSingletonBadInterval_9 : InNonSingletonBadInterval 9 :=
  ⟨8, 9, by norm_num, isBadInterval_8_9, by norm_num, by norm_num⟩

/-- Non-vacuity of the target bound: `N(9) ≥ 2` since both `8` and `9` are
covered by the bad interval `[8, 9]`. -/
theorem two_le_badNonSingletonCount_nine : 2 ≤ badNonSingletonCount 9 := by
  have hsub : ({8, 9} : Finset ℕ) ⊆
      (Finset.range (9 + 1)).filter (fun n => InNonSingletonBadInterval n) := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hn with rfl | rfl
    · exact ⟨by norm_num, inNonSingletonBadInterval_8⟩
    · exact ⟨by norm_num, inNonSingletonBadInterval_9⟩
  calc 2 = ({8, 9} : Finset ℕ).card :=
        (Finset.card_pair_eq_two_iff.mpr (by norm_num)).symm
    _ ≤ badNonSingletonCount 9 := Finset.card_le_card hsub

/-- Eventually `N(x) ≥ 2`: the count is nonzero in the limit, so
`badNonSingleton_interval_bound` cannot be discharged by emptiness. -/
theorem badNonSingletonCount_eventually_two_le :
    ∀ᶠ x : ℕ in atTop, 2 ≤ badNonSingletonCount x := by
  filter_upwards [Filter.eventually_ge_atTop 9] with x hx
  exact two_le_badNonSingletonCount_nine.trans (badNonSingletonCount_mono hx)

/-- The trivial eventual bound `N(x) ≤ x + 1`. -/
theorem badNonSingletonCount_eventually_le :
    ∀ᶠ x : ℕ in atTop, (badNonSingletonCount x : ℝ) ≤ (x : ℝ) + 1 :=
  Filter.Eventually.of_forall badNonSingletonCount_le_real

/-- Crude honest milestone: `N(x) = O(x)` along `atTop`. The headline
`N(x) ≤ (log x)^{-1+ε} · S(x)` would be a *little-o* statement relative to
`S(x) = o(x)`, far beyond this linear bound. -/
theorem badNonSingletonCount_isBigO :
    (fun x : ℕ => (badNonSingletonCount x : ℝ)) =O[atTop] (fun x : ℕ => (x : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with x hx
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hle := badNonSingletonCount_le_real x
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  linarith

end JSP314
