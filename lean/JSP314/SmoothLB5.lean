import JSP314.SmoothLB4
import Mathlib.Tactic

/-!
# Improved z-scale lower bound for `badSingletonCount` (explicit constants)

`SmoothLB4.badSingletonCount_eventually_ge_zscale_two` proves the z-scale
lower bound

  `S(x) = badSingletonCount x ≥ x · exp(-C·√(log x · loglog x))`  eventually

for *every* `C > 2√2`.  This file packages that result with concrete
constants relevant for the squeeze argument:

* `badSingletonCount_eventually_ge_zscale_improved` — the bound with
  `C = 3` (which satisfies `2√2 < 3 < 4`, comfortably beating the
  `C ≤ 4` squeeze gate and improving on the original `C = 10` bound of
  `SingletonLBz.badSingletonCount_eventually_ge_zscale`);
* `badSingletonCount_eventually_ge_zscale_four` — the same bound at the
  gate constant `C = 4`;
* `badSingletonCount_eventually_ge_zscale_of_ge_three` — a parameterized
  form for any `C ≥ 3`;
* `badSingletonCount_eventually_ge_zscale_improved_exists` — an
  existential package `∃ C, 0 < C ∧ C < 4 ∧ …` matching the shape of
  `SingletonLBz.badSingletonCount_eventually_ge_zscale`.
-/

namespace JSP314

namespace SmoothLB5

open Finset Filter SmoothLB

open scoped Topology

/-- `2√2 < 3` (since `√2 < 3/2 ↔ 2 < 9/4`). -/
theorem two_mul_sqrt_two_lt_three : (2 : ℝ) * Real.sqrt 2 < 3 := by
  have h : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  linarith

/-- **Improved lower bound, `C = 3`.**  Eventually
`badSingletonCount x ≥ x · exp(-3·√(log x · loglog x))`.

Since `3 > 2√2`, this is a direct instance of
`SmoothLB4.badSingletonCount_eventually_ge_zscale_two`; it improves on the
`C = 10` bound of `SingletonLBz.badSingletonCount_eventually_ge_zscale` and
satisfies the `C ≤ 4` requirement of the squeeze argument. -/
theorem badSingletonCount_eventually_ge_zscale_improved :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-(3 : ℝ) * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) :=
  SmoothLB4.badSingletonCount_eventually_ge_zscale_two 3
    two_mul_sqrt_two_lt_three

/-- The same bound at the gate constant `C = 4`. -/
theorem badSingletonCount_eventually_ge_zscale_four :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-(4 : ℝ) * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) :=
  SmoothLB4.badSingletonCount_eventually_ge_zscale_two 4
    (by linarith [two_mul_sqrt_two_lt_three])

/-- Parameterized form: the z-scale lower bound holds for every `C ≥ 3`
(in fact for every `C > 2√2`, by `SmoothLB4`). -/
theorem badSingletonCount_eventually_ge_zscale_of_ge_three (C : ℝ) (hC : 3 ≤ C) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) :=
  SmoothLB4.badSingletonCount_eventually_ge_zscale_two C
    (lt_of_lt_of_le two_mul_sqrt_two_lt_three hC)

/-- Existential package matching the shape of
`SingletonLBz.badSingletonCount_eventually_ge_zscale`, but with the
constant explicitly bounded by `4`. -/
theorem badSingletonCount_eventually_ge_zscale_improved_exists :
    ∃ C : ℝ, 0 < C ∧ C < 4 ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) :=
  ⟨3, by norm_num, by norm_num, badSingletonCount_eventually_ge_zscale_improved⟩

end SmoothLB5

end JSP314
