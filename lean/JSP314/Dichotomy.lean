import JSP314.Defs
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Finset.Erase
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# JSP-000314 — the interval dichotomy

The fundamental case split of Tao's argument: every bad interval `[u, v]`
with `u < v` either contains an element divisible by `P²`, where `P` is the
largest prime factor of the interval product `∏_{i=u}^{v} i`, or else
`P ≤ v - u`.

The argument is elementary.  Since `[u, v]` is bad, `P ≠ 1`, so the product
is at least `2` and `P` is genuinely prime.  A prime dividing a finite
product divides one of the factors, so `P ∣ m₁` for some `m₁ ∈ [u, v]`.
If `P² ∤ m₁`, write `m₁ = P · a` with `P ∤ a`.  Factoring the interval
product as `prod = m₁ · r` and cancelling one factor of `P` from
`P² ∣ m₁ · r = P · (a · r)` gives `P ∣ a · r`, hence `P ∣ r`, hence `P ∣ m₂`
for a *different* `m₂ ∈ [u, v]`.  Then `P` divides the nonzero difference
`|m₁ − m₂|`, which is at most `v - u`.
-/

namespace JSP314

/-- TEMPORARY private copy of `isBadInterval_iff` (Localization.lean) for
local checking while dependency oleans are being built. -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- TEMPORARY private copy of `exists_mem_dvd_of_largestPrimeFactor`
(ProdLPF.lean) for local checking while dependency oleans are being
built. -/
private theorem exists_mem_dvd_of_largestPrimeFactor' {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id :=
    largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- The fundamental dichotomy: a bad interval `[u, v]` either contains a
multiple of `P²` (where `P` is the largest prime factor of the interval
product) or satisfies `P ≤ v - u`. -/
theorem bad_interval_sq_multiple_or_long {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) :
    (∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) ∨
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  by_cases hsq : ∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m
  · exact Or.inl hsq
  · -- No element of `[u, v]` is divisible by `P²`.
    right
    push_neg at hsq
    -- `P` divides some `m₁ ∈ [u, v]`.
    obtain ⟨m1, hm1, hdvd1⟩ := exists_mem_dvd_of_largestPrimeFactor' hprod2
    have hnot1 : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m1 :=
      hsq m1 hm1
    obtain ⟨a, ha⟩ := hdvd1
    -- `P ∣ a` would force `P² ∣ m₁`.
    have hPa : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a := by
      rintro ⟨b, hb⟩
      apply hnot1
      exact ⟨b, by rw [ha, hb]; ring⟩
    -- Factor `prod = m₁ * r` where `r` is the product over `[u, v] \ {m₁}`.
    have hprod_eq : (Finset.Icc u v).prod id
        = m1 * ((Finset.Icc u v).erase m1).prod id :=
      (Finset.mul_prod_erase _ _ hm1).symm
    -- `P² ∣ prod = m₁ * r = P * (a * r)`, so `P ∣ a * r` after cancelling.
    have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2
        ∣ m1 * ((Finset.Icc u v).erase m1).prod id := by
      rw [← hprod_eq]
      exact hP2
    have hfact : m1 * ((Finset.Icc u v).erase m1).prod id =
        largestPrimeFactor ((Finset.Icc u v).prod id) *
          (a * ((Finset.Icc u v).erase m1).prod id) := by
      rw [ha]; ring
    rw [hfact, pow_two] at hdvd
    have hPar : largestPrimeFactor ((Finset.Icc u v).prod id)
        ∣ a * ((Finset.Icc u v).erase m1).prod id :=
      (mul_dvd_mul_iff_left hPprime.ne_zero).mp hdvd
    -- `P` prime and `P ∤ a` give `P ∣ r`.
    have hPr : largestPrimeFactor ((Finset.Icc u v).prod id)
        ∣ ((Finset.Icc u v).erase m1).prod id :=
      (hPprime.dvd_mul.mp hPar).resolve_left hPa
    -- Hence a second, distinct element `m₂ ∈ [u, v]` is divisible by `P`.
    obtain ⟨m2, hm2, hdvd2⟩ :=
      ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPr
    obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
    have hdvd2' : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 := hdvd2
    -- `P` divides the nonzero difference of `m₁` and `m₂`.
    have hdvd1' : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 := ⟨a, ha⟩
    have hd12 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 - m2 :=
      Nat.dvd_sub hdvd1' hdvd2'
    have hd21 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 - m1 :=
      Nat.dvd_sub hdvd2' hdvd1'
    rw [Finset.mem_Icc] at hm1 hm2'
    rcases lt_or_gt_of_ne hne with h | h
    · have hpos : 0 < m1 - m2 := by omega
      have hle := Nat.le_of_dvd hpos hd12
      omega
    · have hpos : 0 < m2 - m1 := by omega
      have hle := Nat.le_of_dvd hpos hd21
      omega

end JSP314
