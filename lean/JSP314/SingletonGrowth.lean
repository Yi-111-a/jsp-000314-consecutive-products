import Mathlib
import JSP314.Counting

/-!
# JSP-000314 — `badSingletonCount` tends to infinity

The count of bad singletons `n ≤ x` diverges: every prime `p ≤ √x` contributes
its square `p² ≤ x` to the count, so `π(√x) ≤ badSingletonCount x`
(`badSingletonCount_ge_primeCounting`).  Since `Nat.sqrt` tends to `atTop` and
`Nat.primeCounting` tends to `atTop` (infinitude of primes, via Mathlib's
`Nat.tendsto_primeCounting`), the bound forces `badSingletonCount → ∞`.
-/

namespace JSP314

open Filter

/-- `Nat.sqrt` tends to `atTop`: once `n ≥ b ^ 2` we have `b ≤ Nat.sqrt n`. -/
private theorem tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b ^ 2, fun _ hn => Nat.le_sqrt'.2 hn⟩

/-- `x ↦ π(√x)` tends to `atTop` (composition of two `atTop` maps). -/
private theorem tendsto_primeCounting_comp_sqrt :
    Tendsto (fun x : ℕ => Nat.primeCounting (Nat.sqrt x)) atTop atTop :=
  Nat.tendsto_primeCounting.comp tendsto_nat_sqrt_atTop

/-- For every `K`, eventually `K ≤ badSingletonCount x`. -/
theorem eventually_ge_badSingletonCount (K : ℕ) :
    ∀ᶠ x : ℕ in atTop, K ≤ badSingletonCount x :=
  (tendsto_atTop_mono badSingletonCount_ge_primeCounting
    tendsto_primeCounting_comp_sqrt).eventually_ge_atTop K

/-- The number of bad singletons `n ≤ x` tends to infinity as `x → ∞`. -/
theorem tendsto_badSingletonCount_atTop :
    Filter.Tendsto badSingletonCount Filter.atTop Filter.atTop :=
  tendsto_atTop_mono badSingletonCount_ge_primeCounting
    tendsto_primeCounting_comp_sqrt

end JSP314
