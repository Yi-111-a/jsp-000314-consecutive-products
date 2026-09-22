import JSP314.Defs
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.PrimeCounting

/-!
# JSP-000314 — counting lower bounds for `badSingletonCount`

Quantitative lower bounds on the number of "bad singletons" `n ≤ x`,
i.e. `1 < n` with `(largestPrimeFactor n)^2 ∣ n`:

* `badSingletonCount_mono`: monotonicity of the count in `x`.
* `prime_sq_mem_badSingleton`: for prime `p`, the number `p^2` satisfies the
  bad-singleton predicate (key step: `largestPrimeFactor (p^2) = p`).
* `badSingletonCount_ge_primeCounting` / `badSingletonCount_ge`:
  `Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x`, obtained by mapping
  each prime `p ≤ √x` injectively to its square `p^2 ≤ x`.
-/

namespace JSP314

open Nat Finset

/-- For prime `p`, the largest prime factor of `p^2` is `p`.
Local copy (private, to avoid name clashes) built on the `Defs` API. -/
private lemma lpf_prime_sq {p : ℕ} (hp : Nat.Prime p) :
    largestPrimeFactor (p ^ 2) = p := by
  have h2 : 2 ≤ p ^ 2 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left hp.two_le 2)
  apply le_antisymm
  · exact Nat.le_of_dvd hp.pos
      ((largestPrimeFactor_prime h2).dvd_of_dvd_pow (largestPrimeFactor_dvd h2))
  · exact prime_dvd_le_largestPrimeFactor h2 hp (dvd_pow_self p two_ne_zero)

/-- Every prime square satisfies the bad-singleton predicate. -/
theorem prime_sq_mem_badSingleton (p : ℕ) (hp : Nat.Prime p) :
    1 < p ^ 2 ∧ (largestPrimeFactor (p ^ 2)) ^ 2 ∣ p ^ 2 := by
  refine ⟨one_lt_pow₀ hp.one_lt two_ne_zero, ?_⟩
  rw [lpf_prime_sq hp]

/-- `badSingletonCount` is monotone in its argument. -/
theorem badSingletonCount_mono : Monotone badSingletonCount := by
  intro x y hxy
  unfold badSingletonCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- Lower bound: the prime squares `p^2` with `p ≤ √x` all lie in the counted
set, and `p ↦ p^2` is injective, so `π(√x) ≤ badSingletonCount x`. -/
theorem badSingletonCount_ge_primeCounting (x : ℕ) :
    Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x := by
  unfold badSingletonCount
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p ^ 2)
  · intro p hp
    rw [Finset.mem_coe, Nat.mem_primesLE] at hp
    obtain ⟨hple, hpp⟩ := hp
    have hpsq : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by show p ^ 2 < x + 1; omega), ?_⟩)
    exact prime_sq_mem_badSingleton p hpp
  · intro a _ b _ hab
    exact Nat.pow_left_injective two_ne_zero hab

/-- Alias for `badSingletonCount_ge_primeCounting`. -/
theorem badSingletonCount_ge (x : ℕ) :
    badSingletonCount x ≥ Nat.primeCounting (Nat.sqrt x) :=
  badSingletonCount_ge_primeCounting x

end JSP314
