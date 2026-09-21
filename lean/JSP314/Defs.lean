import Mathlib

/-!
# JSP-000314 definitions

Tao's theorem (Ta26c) on the Erdős–Graham conjecture: the count `B(x)` of `n ≤ x`
lying in a "bad" interval `[u, v]` — one where the square of the largest prime
factor of `∏_{i=u}^{v} i` divides that product — is asymptotic to the count of
`n ≤ x` with `P(n)² ∣ n`.

This file defines `largestPrimeFactor` (the true greatest prime factor, with the
convention that it equals `1` for `n ≤ 1`), the bad-interval predicate
`IsBadInterval`, and the two counting functions `B` and `badSingletonCount`,
together with the basic API for `largestPrimeFactor`.
-/

namespace JSP314

open Classical

/-- The largest prime factor of `n`, with the convention
`largestPrimeFactor n = 1` when `n ≤ 1`.  Implemented via `Nat.maxPrimeFac`,
the greatest prime factor from Mathlib (which takes the junk values `0` at `0`
and `1` at `1`). -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 1 else Nat.maxPrimeFac n

/-- For `n ≥ 2`, `largestPrimeFactor n` agrees with `Nat.maxPrimeFac n`. -/
theorem largestPrimeFactor_eq_maxPrimeFac {n : ℕ} (h : 2 ≤ n) :
    largestPrimeFactor n = Nat.maxPrimeFac n := by
  have hn : ¬ n ≤ 1 := by omega
  simp [largestPrimeFactor, hn]

theorem largestPrimeFactor_eq_one_iff {n : ℕ} : largestPrimeFactor n = 1 ↔ n ≤ 1 := by
  by_cases hn : n ≤ 1
  · simp [largestPrimeFactor, hn]
  · have h2 : 2 ≤ n := by omega
    rw [largestPrimeFactor_eq_maxPrimeFac h2]
    have hne : Nat.maxPrimeFac n ≠ 1 :=
      (Nat.prime_maxPrimeFac_of_one_lt h2).ne_one
    simp [hne, hn]

theorem one_lt_largestPrimeFactor {n : ℕ} (h : 2 ≤ n) : 1 < largestPrimeFactor n := by
  rw [largestPrimeFactor_eq_maxPrimeFac h]
  exact (Nat.prime_maxPrimeFac_of_one_lt (by omega)).one_lt

theorem largestPrimeFactor_prime {n : ℕ} (h : 2 ≤ n) :
    Nat.Prime (largestPrimeFactor n) := by
  rw [largestPrimeFactor_eq_maxPrimeFac h]
  exact Nat.prime_maxPrimeFac_of_one_lt (by omega)

theorem largestPrimeFactor_dvd {n : ℕ} (h : 2 ≤ n) : largestPrimeFactor n ∣ n := by
  rw [largestPrimeFactor_eq_maxPrimeFac h]
  exact Nat.maxPrimeFac_dvd

theorem prime_dvd_le_largestPrimeFactor {n p : ℕ} (hn : 2 ≤ n) (hp : Nat.Prime p)
    (h : p ∣ n) : p ≤ largestPrimeFactor n := by
  rw [largestPrimeFactor_eq_maxPrimeFac hn]
  exact Nat.le_maxPrimeFac (by omega) hp h

/-- For `n ≥ 2`, `largestPrimeFactor n` is the greatest element of the finset
`Nat.primeFactors n`. -/
theorem largestPrimeFactor_eq_primeFactors_max' {n : ℕ} (h : 2 ≤ n) :
    largestPrimeFactor n =
      (Nat.primeFactors n).max' (Nat.nonempty_primeFactors.2 (by omega)) := by
  refine le_antisymm (Finset.le_max' _ _ ?_) (Finset.max'_le _ _ _ ?_)
  · rw [Nat.mem_primeFactors]
    exact ⟨largestPrimeFactor_prime h, largestPrimeFactor_dvd h, by omega⟩
  · intro q hq
    obtain ⟨hq1, hq2, -⟩ := Nat.mem_primeFactors.1 hq
    exact prime_dvd_le_largestPrimeFactor h hq1 hq2


theorem largestPrimeFactor_prime_sq_self {p : ℕ} (hp : Nat.Prime p) :
    largestPrimeFactor (p ^ 2) = p := by
  have h2 : 2 ≤ p ^ 2 := hp.two_le.trans (le_self_pow₀ hp.one_lt.le two_ne_zero)
  rw [largestPrimeFactor_eq_maxPrimeFac h2, Nat.maxPrimeFac_pow two_ne_zero,
    Nat.Prime.maxPrimeFac_eq_self hp]

/-- Interval `[u, v]` is bad if `u ≤ v` and, writing `prod` for the product
`∏_{i=u}^{v} i` and `P` for its largest prime factor, `P ≠ 1` and `P² ∣ prod`. -/
def IsBadInterval (u v : ℕ) : Prop :=
  u ≤ v ∧
    let prod := (Finset.Icc u v).prod id
    let P := largestPrimeFactor prod
    P ≠ 1 ∧ P ^ 2 ∣ prod

/-- `B(x)`: the number of `n ≤ x` lying in some bad interval `[u, v]`. -/
noncomputable def B (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n =>
    ∃ u v : ℕ, IsBadInterval u v ∧ u ≤ n ∧ n ≤ v)).card

/-- The number of `n ≤ x` with `1 < n` and `P(n)² ∣ n` (the "bad singletons"). -/
noncomputable def badSingletonCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n =>
    1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n)).card

end JSP314
