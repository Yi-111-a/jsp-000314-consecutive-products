import JSP314.Squeeze
import JSP314.Type2Run
import JSP314.Main
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Tactic.Push

/-!
# JSP-000314 — the uniform "smooth run" characterization

Every `n` lying in a non-singleton bad interval `[u, v]` is packaged as a
point of a `P`-smooth run: writing `prod = ∏_{i=u}^{v} i` and
`P = largestPrimeFactor prod`, we have

* `u < v` and `u ≤ n ≤ v`;
* `v ≤ 2n - 2` (the dyadic squeeze `bad_interval_v_add_two_le`, so the run
  lies inside `(v/2, v]`);
* `P` is prime and `P² ∣ prod`;
* every element of `[u, v]` is `P`-smooth (`∀ q` prime, `q ∣ i → q ≤ P`);
* the dichotomy: either some `m ∈ [u, v]` is divisible by `P²`, or the run
  is long, `P ≤ v - u`.

The smoothness statement is also restated via `Nat.smoothNumbers`
(`i ∈ Nat.smoothNumbers (P + 1)`).
-/

namespace JSP314

/-- In a bad interval the product is at least `2` (else its largest prime
factor would be `1`). -/
theorem bad_interval_prod_ge_two {u v : ℕ} (hbad : IsBadInterval u v) :
    2 ≤ (Finset.Icc u v).prod id := by
  rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
  · exact absurd
      (largestPrimeFactor_eq_one_iff.mpr
        (show (Finset.Icc u v).prod id ≤ 1 by omega))
      hbad.2.1
  · exact h

/-- In a bad interval, the largest prime factor `P` of the product is a
genuine prime. -/
theorem bad_interval_P_prime {u v : ℕ} (hbad : IsBadInterval u v) :
    Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
  largestPrimeFactor_prime (bad_interval_prod_ge_two hbad)

/-- Uniform smoothness: in a bad interval, every prime dividing an element
of `[u, v]` is at most `P`, the largest prime factor of the product —
i.e. every element is `P`-smooth. -/
theorem bad_interval_forall_prime_dvd_le {u v : ℕ} (hbad : IsBadInterval u v) :
    ∀ i ∈ Finset.Icc u v, ∀ q : ℕ, Nat.Prime q → q ∣ i →
      q ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  intro i hi q hq hqdi
  have hi2 : 2 ≤ i := by
    rcases Nat.lt_or_ge i 2 with h | h
    · rcases Nat.lt_or_ge i 1 with h0 | h1
      · -- `i = 0`: the product vanishes, forcing `P = 1`, contradicting
        -- badness.
        have hi0 : i = 0 := by omega
        subst hi0
        have hprod0 : (Finset.Icc u v).prod id = 0 := Finset.prod_eq_zero hi rfl
        exact absurd
          (largestPrimeFactor_eq_one_iff.mpr (by omega))
          hbad.2.1
      · -- `i = 1`: no prime divides `1`.
        have hi1 : i = 1 := by omega
        subst hi1
        exact absurd hqdi hq.not_dvd_one
    · exact h
  calc q ≤ largestPrimeFactor i := prime_dvd_le_largestPrimeFactor hi2 hq hqdi
    _ ≤ _ := bad_interval_forall_lpf_le hbad i hi

/-- The `P`-smoothness condition repackaged via Mathlib's
`Nat.smoothNumbers`: `i` is `(P + 1)`-smooth iff every prime divisor of `i`
is `≤ P`. -/
theorem forall_prime_dvd_le_iff_mem_smoothNumbers {i P : ℕ} :
    (∀ q : ℕ, Nat.Prime q → q ∣ i → q ≤ P) ↔
      i ∈ Nat.smoothNumbers (P + 1) := by
  rw [Nat.mem_smoothNumbers']
  constructor
  · intro h q hq hqd
    exact Nat.lt_succ_of_le (h q hq hqd)
  · intro h q hq hqd
    exact Nat.le_of_lt_succ (h q hq hqd)

/-- The uniform characterization: if `n` lies in a non-singleton bad
interval `[u, v]`, then `[u, v]` is a `P`-smooth run contained in the
dyadic window `(v/2, v]` with `P²` dividing the interval product, and either
some element of the run is a multiple of `P²` or the run has length `≥ P`. -/
theorem nonSingleton_smooth_run {n : ℕ} (h : InNonSingletonBadInterval n) :
    ∃ u v P : ℕ, u < v ∧ u ≤ n ∧ n ≤ v ∧ v ≤ 2 * n - 2 ∧ Nat.Prime P ∧
      P ^ 2 ∣ (Finset.Icc u v).prod id ∧
      (∀ i ∈ Finset.Icc u v, ∀ q : ℕ, Nat.Prime q → q ∣ i → q ≤ P) ∧
      ((∃ m ∈ Finset.Icc u v, P ^ 2 ∣ m) ∨ P ≤ v - u) := by
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := h
  have hv2 : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  have hvn : v ≤ 2 * n - 2 := by omega
  refine ⟨u, v, largestPrimeFactor ((Finset.Icc u v).prod id), huv, hun, hnv,
    hvn, bad_interval_P_prime hbad, hbad.2.2, ?_, ?_⟩
  · intro i hi q hq hqdi
    exact bad_interval_forall_prime_dvd_le hbad i hi q hq hqdi
  · by_cases hsq : ∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m
    · exact Or.inl hsq
    · right
      push_neg at hsq
      exact bad_interval_largestPrimeFactor_le_sub hbad huv hsq

/-- The same characterization with the smoothness clause stated via
`Nat.smoothNumbers (P + 1)`. -/
theorem nonSingleton_smooth_run' {n : ℕ} (h : InNonSingletonBadInterval n) :
    ∃ u v P : ℕ, u < v ∧ u ≤ n ∧ n ≤ v ∧ v ≤ 2 * n - 2 ∧ Nat.Prime P ∧
      P ^ 2 ∣ (Finset.Icc u v).prod id ∧
      (∀ i ∈ Finset.Icc u v, i ∈ Nat.smoothNumbers (P + 1)) ∧
      ((∃ m ∈ Finset.Icc u v, P ^ 2 ∣ m) ∨ P ≤ v - u) := by
  obtain ⟨u, v, P, huv, hun, hnv, hvn, hPp, hPsq, hsmooth, hd⟩ :=
    nonSingleton_smooth_run h
  exact ⟨u, v, P, huv, hun, hnv, hvn, hPp, hPsq,
    fun i hi => forall_prime_dvd_le_iff_mem_smoothNumbers.mp (hsmooth i hi), hd⟩

end JSP314
