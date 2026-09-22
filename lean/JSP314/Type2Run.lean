import JSP314.Defs
import Mathlib.Algebra.BigOperators.Associated

/-!
# JSP-000314 — the "type-2" regime of a bad interval

Let `[u, v]` be a bad interval with product `prod = ∏_{i=u}^{v} i` and
`P = largestPrimeFactor prod`.  In the type-2 branch of the dichotomy no
element of `[u, v]` is divisible by `P ^ 2`.  Since `P ^ 2 ∣ prod`, the factor
`P` must then divide at least two distinct elements `a, b ∈ [u, v]`, so
`P ∣ |b - a|` and hence `P ≤ v - u`.

This file proves:

* `bad_interval_forall_lpf_le`: every element's largest prime factor is
  bounded by `P`;
* `bad_interval_two_mul_le_of_no_sq`: `P` divides two distinct elements;
* `bad_interval_largestPrimeFactor_le_sub`: `P ≤ v - u`.
-/

namespace JSP314

/-- In a bad interval, the largest prime factor of every element is at most the
largest prime factor `P` of the whole product. -/
theorem bad_interval_forall_lpf_le {u v : ℕ} (hbad : IsBadInterval u v) :
    ∀ i ∈ Finset.Icc u v,
      largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  have hPne : largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 := hbad.2.1
  have h2 : 2 ≤ (Finset.Icc u v).prod id := by
    rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
    · exact absurd
        (largestPrimeFactor_eq_one_iff.mpr (show (Finset.Icc u v).prod id ≤ 1 by omega))
        hPne
    · exact h
  intro i hi
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  · rw [largestPrimeFactor_eq_one_iff.mpr (show i ≤ 1 by omega)]
    exact (one_lt_largestPrimeFactor h2).le
  · have hi_dvd : i ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hi
    exact prime_dvd_le_largestPrimeFactor h2 (largestPrimeFactor_prime hi2)
      (dvd_trans (largestPrimeFactor_dvd hi2) hi_dvd)

/-- In the type-2 regime (no element of `[u, v]` divisible by `P ^ 2`), `P`
divides at least two distinct elements of the interval. -/
theorem bad_interval_two_mul_le_of_no_sq {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    ∃ a b : ℕ, a ∈ Finset.Icc u v ∧ b ∈ Finset.Icc u v ∧ a ≠ b ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ b := by
  set P := largestPrimeFactor ((Finset.Icc u v).prod id) with hPdef
  have hPne : P ≠ 1 := hbad.2.1
  have hPsq : P ^ 2 ∣ (Finset.Icc u v).prod id := hbad.2.2
  have h2 : 2 ≤ (Finset.Icc u v).prod id := by
    rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
    · exact absurd
        (largestPrimeFactor_eq_one_iff.mpr (show (Finset.Icc u v).prod id ≤ 1 by omega))
        hPne
    · exact h
  have hPprime : Nat.Prime P := largestPrimeFactor_prime h2
  have hPpos : 0 < P := hPprime.pos
  have hPdvd : P ∣ (Finset.Icc u v).prod id := largestPrimeFactor_dvd h2
  -- Some element `m₁` of the interval is divisible by `P`.
  obtain ⟨m₁, hm₁, hPm₁⟩ := hPprime.prime.exists_mem_finset_dvd hPdvd
  have hPm₁' : P ∣ m₁ := hPm₁
  have hPsqm₁ : ¬ P ^ 2 ∣ m₁ := hnsq m₁ hm₁
  -- Then `P` does not divide `m₁ / P`, otherwise `P ^ 2` would divide `m₁`.
  have hPa : ¬ P ∣ m₁ / P := by
    rintro ⟨k, hk⟩
    apply hPsqm₁
    refine ⟨k, ?_⟩
    rw [← Nat.mul_div_cancel' hPm₁', hk, pow_two, mul_assoc]
  -- Factor the interval product as `m₁ * (product over the rest)`.
  have hprod_eq : (Finset.Icc u v).prod id
      = m₁ * ((Finset.Icc u v).erase m₁).prod id := by
    simpa using (Finset.mul_prod_erase (Finset.Icc u v) id hm₁).symm
  have hP2mr' : P ^ 2 ∣ m₁ * ((Finset.Icc u v).erase m₁).prod id := by
    rw [← hprod_eq]
    exact hPsq
  obtain ⟨k, hk⟩ := hP2mr'
  -- Cancel one factor of `P` to get `P ∣ (m₁ / P) * (rest)`.
  have hPar : P ∣ (m₁ / P) * ((Finset.Icc u v).erase m₁).prod id := by
    have e : P * ((m₁ / P) * ((Finset.Icc u v).erase m₁).prod id) = P * (P * k) := by
      rw [← mul_assoc, Nat.mul_div_cancel' hPm₁', hk, pow_two, mul_assoc]
    exact ⟨k, Nat.eq_of_mul_eq_mul_left hPpos e⟩
  -- Since `P ∤ m₁ / P`, `P` divides the product over the rest.
  have hPr : P ∣ ((Finset.Icc u v).erase m₁).prod id :=
    (hPprime.dvd_mul.mp hPar).resolve_left hPa
  -- Hence a second, distinct element `m₂` of the interval is divisible by `P`.
  obtain ⟨m₂, hm₂, hPm₂⟩ := hPprime.prime.exists_mem_finset_dvd hPr
  have hPm₂' : P ∣ m₂ := hPm₂
  obtain ⟨hne, hm₂'⟩ := Finset.mem_erase.mp hm₂
  exact ⟨m₁, m₂, hm₁, hm₂', hne.symm, hPm₁', hPm₂'⟩

/-- In the type-2 regime, `P ≤ v - u`: `P` divides the difference of two
distinct elements of `[u, v]`, which is a positive integer at most `v - u`. -/
theorem bad_interval_largestPrimeFactor_le_sub {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  obtain ⟨a, b, ha, hb, hab, hPa, hPb⟩ :=
    bad_interval_two_mul_le_of_no_sq hbad huv hnsq
  rw [Finset.mem_Icc] at ha hb
  rcases le_total a b with h | h
  · have hpos : 0 < b - a := by omega
    have hle : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ b - a :=
      Nat.le_of_dvd hpos (Nat.dvd_sub hPb hPa)
    omega
  · have hpos : 0 < a - b := by omega
    have hle : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ a - b :=
      Nat.le_of_dvd hpos (Nat.dvd_sub hPa hPb)
    omega

end JSP314
