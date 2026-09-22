import JSP314.ProdLPF
import Mathlib.NumberTheory.Bertrand

/-!
# JSP-000314 — bad intervals are short

Bertrand's postulate implies that a bad interval `[u, v]` with `u < v` satisfies
`v < 2u`: writing `P` for the largest prime factor of `∏_{i=u}^{v} i`, a prime
strictly between `v / 2` and `v` forces `v < 2P`, so `P` is the *unique*
multiple of `P` in `[u, v]` and `P²` cannot divide the product.

* `bad_interval_v_lt_two_mul_u`: `v < 2 * u` for a bad interval with `u < v`.
* `mem_bad_interval_v_lt_two_mul`: every member `n` of a bad interval satisfies
  `v < 2 * n`.
* `bad_interval_mem_pair_bounds`: two members `m, n` of a bad interval satisfy
  `2m > v`, `m < 2n` and `2n > v`.
* `two_le_u_of_isBadInterval`: `2 ≤ u`.
-/

namespace JSP314

/-- **Theorem 1**: a bad interval `[u, v]` with `u < v` satisfies `v < 2u`.

Suppose `2u ≤ v`.  Bertrand's postulate yields a prime `p` with
`v / 2 < p ≤ 2 * (v / 2) ≤ v`; then `p ∈ [u, v]`, so `p ∣ ∏ i` and hence
`p ≤ P`, where `P` is the largest prime factor of the product.  This forces
`v < 2P`.  Every member of `[u, v]` divisible by `P` is a positive multiple of
`P` strictly below `2P`, hence equals `P` itself.  Therefore `P² ∣ ∏ i` would
give `P ∣ ∏_{i ≠ P} i`, i.e. `P` would divide a member of `[u, v]` different
from `P` — contradiction. -/
theorem bad_interval_v_lt_two_mul_u {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : v < 2 * u := by
  obtain ⟨hle, hP1, hP2⟩ := hbad
  set prod := (Finset.Icc u v).prod id with hprod_def
  set P := largestPrimeFactor prod with hP_def
  -- Since `P ≠ 1`, the product is at least `2`.
  have hprod2 : 2 ≤ prod := by
    by_contra hc
    push_neg at hc
    exact hP1 (largestPrimeFactor_eq_one_iff.mpr (by omega))
  have hPprime : Nat.Prime P := largestPrimeFactor_prime hprod2
  have hPpos : P ≠ 0 := hPprime.ne_zero
  -- `u ≥ 1`, else `0` lies in the interval and the product vanishes.
  have hu1 : 1 ≤ u := by
    by_contra hc
    push_neg at hc
    have h0mem : (0 : ℕ) ∈ Finset.Icc u v :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h0 : prod = 0 := by
      rw [hprod_def]
      exact Finset.prod_eq_zero h0mem rfl
    omega
  -- Suppose `2u ≤ v` and derive a contradiction.
  by_contra hcontra
  push_neg at hcontra
  -- Bertrand's postulate on `v / 2`: a prime `p` with `v / 2 < p ≤ 2 * (v / 2)`.
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (v / 2) (by omega)
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
  obtain ⟨m, hm, hPm⟩ := exists_mem_dvd_of_largestPrimeFactor hprod2
  have hPmem : P ∈ Finset.Icc u v := (huniq m hm hPm) ▸ hm
  -- Factor `P` out of the product; `P² ∣ prod` then forces `P ∣ ∏_{i ≠ P} i`.
  have hperase : prod = P * ((Finset.Icc u v).erase P).prod id := by
    rw [hprod_def]
    exact (Finset.mul_prod_erase (Finset.Icc u v) id hPmem).symm
  rw [hperase, pow_two, mul_dvd_mul_iff_left hPpos] at hP2
  obtain ⟨m₂, hm₂, hPm₂⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hP2
  obtain ⟨hne, hm₂I⟩ := Finset.mem_erase.mp hm₂
  exact hne (huniq m₂ hm₂I hPm₂)

/-- **Theorem 2**: every member `n` of a bad interval `[u, v]` (with `u < v`)
satisfies `v < 2n`. -/
theorem mem_bad_interval_v_lt_two_mul {u v n : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hn : n ∈ Finset.Icc u v) : v < 2 * n := by
  have h1 := bad_interval_v_lt_two_mul_u huv hbad
  have hI := Finset.mem_Icc.mp hn
  omega

/-- **Theorem 3**: two members `m, n` of a bad interval `[u, v]` satisfy
`2m > v`, `m < 2n` and `2n > v` — both lie in `(v / 2, v]`. -/
theorem bad_interval_mem_pair_bounds {u v m n : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    2 * m > v ∧ m < 2 * n ∧ 2 * n > v := by
  have h2m := mem_bad_interval_v_lt_two_mul hbad huv hm
  have h2n := mem_bad_interval_v_lt_two_mul hbad huv hn
  have hmI := Finset.mem_Icc.mp hm
  have hnI := Finset.mem_Icc.mp hn
  omega

/-- **Corollary**: a bad interval `[u, v]` with `u < v` satisfies `2 ≤ u`. -/
theorem two_le_u_of_isBadInterval {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : 2 ≤ u := by
  have h1 := bad_interval_v_lt_two_mul_u huv hbad
  omega

end JSP314
