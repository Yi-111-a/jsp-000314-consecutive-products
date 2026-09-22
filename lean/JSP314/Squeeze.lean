import JSP314.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set

/-!
# JSP-000314 — bad intervals lie inside the dyadic window `(v/2, v]`

A non-singleton bad interval `[u, v]` satisfies `v + 2 ≤ 2u`, i.e.
`v ≤ 2u − 2`.  The argument uses Bertrand's postulate: there is a prime `p`
with `v / 2 < p ≤ 2 * (v / 2) ≤ v`.  If `2u ≤ v + 1`, then
`2p ≥ v + 1 ≥ 2u`, so `p ≥ u` and hence `p` lies in `[u, v]` and divides the
interval product.  The largest prime factor `P` of the product therefore
satisfies `P ≥ p > v / 2`, i.e. `v < 2P`, so `P` is the unique multiple of `P`
in `[u, v]` and `P²` cannot divide the product — contradicting badness.
-/

namespace JSP314

/-- Every non-singleton bad interval `[u, v]` satisfies `v + 2 ≤ 2 * u`,
i.e. `v ≤ 2u − 2`: bad intervals lie inside the dyadic window `(v/2, v]`.

Suppose instead `2u ≤ v + 1`.  Bertrand's postulate yields a prime `p` with
`v / 2 < p ≤ 2 * (v / 2)`; then `2p ≥ v + 1 ≥ 2u` gives `u ≤ p ≤ v`, so `p`
divides `prod := ∏_{i=u}^{v} i` and hence `p ≤ P`, the largest prime factor of
`prod`.  Thus `v < 2P`, so every member of `[u, v]` divisible by `P` equals `P`
itself: `P` is the unique multiple of `P` in the interval.  Factoring `P` out,
`P² ∣ prod` forces `P` to divide the product over the erased interval, hence a
member different from `P` — a contradiction. -/
theorem bad_interval_v_add_two_le {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) : v + 2 ≤ 2 * u := by
  obtain ⟨hle, hP1, hP2⟩ := hbad
  set prod := (Finset.Icc u v).prod id with hprod_def
  set P := largestPrimeFactor prod with hP_def
  -- Since `P ≠ 1`, the product is at least `2`.
  have hprod2 : 2 ≤ prod := by
    by_contra hc
    push Not at hc
    exact hP1 (largestPrimeFactor_eq_one_iff.mpr (by omega))
  have hPprime : Nat.Prime P := largestPrimeFactor_prime hprod2
  have hPpos : P ≠ 0 := hPprime.ne_zero
  -- `u ≥ 1`, else `0 ∈ [u, v]` and the product vanishes.
  have hu1 : 1 ≤ u := by
    by_contra hc
    push Not at hc
    have h0mem : (0 : ℕ) ∈ Finset.Icc u v :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h0 : prod = 0 := by
      rw [hprod_def]
      exact Finset.prod_eq_zero h0mem rfl
    omega
  -- Suppose `v + 2 > 2u`, i.e. `2u ≤ v + 1`, and derive a contradiction.
  by_contra hcontra
  push Not at hcontra
  -- Bertrand's postulate on `v / 2`: a prime `p` with `v / 2 < p ≤ 2 * (v / 2)`.
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (v / 2) (by omega)
  -- `2p ≥ v + 1 ≥ 2u` gives `u ≤ p`, and `p ≤ 2 * (v / 2) ≤ v`.
  have hpmem : p ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hp_le_P : p ≤ P :=
    prime_dvd_le_largestPrimeFactor hprod2 hpprime
      (Finset.dvd_prod_of_mem id hpmem)
  have hvlt : v < 2 * P := by omega
  -- The only multiple of `P` in `[u, v]` is `P` itself.
  have huniq : ∀ m' ∈ Finset.Icc u v, P ∣ m' → m' = P := by
    intro m' hm' hPm'
    have hI := Finset.mem_Icc.mp hm'
    exact Nat.eq_of_dvd_of_lt_two_mul (by omega) hPm' (by omega)
  -- `P` divides the product, hence divides some member `m`, hence
  -- `P = m ∈ [u, v]`.
  have hdvd : P ∣ prod := largestPrimeFactor_dvd hprod2
  obtain ⟨m, hm, hPm⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hdvd
  have hPmem : P ∈ Finset.Icc u v := (huniq m hm hPm) ▸ hm
  -- Factor `P` out of the product; `P² ∣ prod` then forces
  -- `P ∣ ∏_{i ∈ [u,v], i ≠ P} i`.
  have hperase : prod = P * ((Finset.Icc u v).erase P).prod id := by
    rw [hprod_def]
    exact (Finset.mul_prod_erase (Finset.Icc u v) id hPmem).symm
  rw [hperase, pow_two, mul_dvd_mul_iff_left hPpos] at hP2
  obtain ⟨m₂, hm₂, hPm₂⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hP2
  obtain ⟨hne, hm₂I⟩ := Finset.mem_erase.mp hm₂
  exact hne (huniq m₂ hm₂I hPm₂)

end JSP314
