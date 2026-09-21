import Mathlib
import JSP314.Defs

/-!
# JSP-000314 — Tao consecutive-products / bad-interval asymptotic (Ta26c)
-/

namespace JSP314

open Nat Filter

/-- Largest prime factor; convention P(0)=P(1)=1. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 1 else n.minFac  -- refine to true max over factors

/-- Interval `[u,v]` is bad if the square of the largest prime factor of the
product divides that product. -/
def IsBadInterval (u v : ℕ) : Prop :=
  u ≤ v ∧
    let prod := (Finset.Icc u v).prod id
    let P := largestPrimeFactor prod
    P ≠ 1 ∧ P ^ 2 ∣ prod

/-- B(x): count of n ≤ x lying in some bad interval. -/
noncomputable def B (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n =>
    ∃ u v : ℕ, IsBadInterval u v ∧ u ≤ n ∧ n ≤ v)).card

/-- Singleton bad points: n ≤ x with P(n)^2 ∣ n. -/
noncomputable def badSingletonCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n =>
    1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n)).card

/-- Ta26c full asymptotic: B(x) = (1 + O((log x)^{-1+o(1)})) · badSingletonCount(x). -/
theorem bad_interval_count_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      |(B x : ℝ) - (badSingletonCount x : ℝ)| ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  sorry

end JSP314
