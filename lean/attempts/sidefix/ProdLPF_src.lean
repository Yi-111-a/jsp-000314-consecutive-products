import JSP314.Bounds
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.MaxPrimeFac

/-!
# JSP-000314 — the largest prime factor of an interval product

For `prod := ∏_{i=u}^{v} i` with `2 ≤ prod`, the largest prime factor of `prod`
is the maximum of the largest prime factors of the individual factors:

* `le_largestPrimeFactor_prod`: `largestPrimeFactor i ≤ largestPrimeFactor prod`
  for `i ∈ [u, v]` (every prime factor of `i` divides `prod`);
* `exists_mem_dvd_of_largestPrimeFactor`: `P(prod)` divides some member of the
  interval (a prime dividing a finite product divides a factor);
* `largestPrimeFactor_prod_eq_max`: `largestPrimeFactor prod` equals the finset
  supremum `sup (largestPrimeFactor)` over `[u, v]`.

These are the algebraic backbone for the analytic core of the argument.
-/

namespace JSP314

/-- Every `i ∈ [u, v]` has `largestPrimeFactor i ≤ largestPrimeFactor prod`,
where `prod = ∏_{j=u}^{v} j`, provided `2 ≤ prod`.  If `i ≤ 1` the bound is
trivial since `largestPrimeFactor i = 1`; otherwise `largestPrimeFactor i` is a
prime dividing `prod`. -/
theorem le_largestPrimeFactor_prod {u v i : ℕ} (hi : i ∈ Finset.Icc u v)
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rcases le_or_lt i 1 with hi1 | hi1
  · rw [largestPrimeFactor_eq_one_iff.mpr hi1]
    exact (one_lt_largestPrimeFactor h).le
  · have hi2 : 2 ≤ i := hi1
    exact prime_dvd_le_largestPrimeFactor h (largestPrimeFactor_prime hi2)
      ((largestPrimeFactor_dvd hi2).trans (Finset.dvd_prod_of_mem id hi))

/-- The largest prime factor of `prod = ∏_{i=u}^{v} i` (with `2 ≤ prod`)
divides some member of the interval: a prime dividing a finite product
divides one of the factors. -/
theorem exists_mem_dvd_of_largestPrimeFactor {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id :=
    largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- The largest prime factor of `prod = ∏_{i=u}^{v} i` (with `2 ≤ prod`) is the
maximum of the largest prime factors of the elements of `[u, v]`. -/
theorem largestPrimeFactor_prod_eq_max {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor ((Finset.Icc u v).prod id) =
      (Finset.Icc u v).sup (fun i => largestPrimeFactor i) := by
  apply le_antisymm
  · -- `P(prod)` divides some `m ∈ [u, v]`, hence `P(prod) ≤ P(m) ≤ sup`.
    obtain ⟨m, hm, hdiv⟩ := exists_mem_dvd_of_largestPrimeFactor h
    have hP := largestPrimeFactor_prime h
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (by omega : (Finset.Icc u v).prod id ≠ 0)
        (eq_zero_of_zero_dvd (Finset.dvd_prod_of_mem id hm))
    have hm2 : 2 ≤ m :=
      (one_lt_largestPrimeFactor h).trans_le
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdiv)
    exact le_trans (prime_dvd_le_largestPrimeFactor hm2 hP hdiv)
      (Finset.le_sup hm)
  · exact Finset.sup_le_iff.mpr fun i hi => le_largestPrimeFactor_prod hi h

end JSP314
