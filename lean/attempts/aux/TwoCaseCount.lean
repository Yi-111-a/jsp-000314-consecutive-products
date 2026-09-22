import JSP314.Main
import JSP314.Dichotomy
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.IntervalCases

/-!
# JSP-000314 — the two-case cover count

The interval dichotomy `bad_interval_sq_multiple_or_long` (JSP314.Dichotomy)
splits the points covered by a non-singleton bad interval `[u, v]` into two
classes:

* **Type I** (`TypeICovered`): `[u, v]` contains an element divisible by
  `P²`, where `P` is the largest prime factor of the interval product.
* **Type II** (`TypeIICovered`): `P ≤ v - u`, i.e. the interval is "long"
  relative to `P`.

This file defines the associated counting functions `typeICount` and
`typeIICount`, proves the counting bound
`badNonSingletonCount x ≤ typeICount x + typeIICount x`, and records two
consequences for Type-II intervals:

* `bad_interval_v_lt_two_mul_u`: every bad interval `[u, v]` with `u < v`
  satisfies `v < 2u` (a Bertrand-postulate argument), hence in a Type-II
  interval `P ≤ v - u < u ≤ n`, so `P < n`
  (`typeIICovered_imp_prime_lt`);
* `typeIICovered_imp_smooth_run`: every element of a Type-II interval is
  `P`-smooth with `P < n`.

All auxiliary lemmas are kept `private` so this file is self-contained.
-/

namespace JSP314

open Classical

/-- `n` is *Type-I covered*: it lies in a non-singleton bad interval
`[u, v]` containing an element `m` divisible by `P²`, where `P` is the
largest prime factor of `∏_{i=u}^{v} i`. -/
def TypeICovered (n : ℕ) : Prop :=
  ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ m ∈ Finset.Icc u v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧ u ≤ n ∧ n ≤ v

/-- `n` is *Type-II covered*: it lies in a non-singleton bad interval
`[u, v]` whose length satisfies `P ≤ v - u`, where `P` is the largest
prime factor of `∏_{i=u}^{v} i`. -/
def TypeIICovered (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u ∧ u ≤ n ∧ n ≤ v

/-- Count of `n ≤ x` that are Type-I covered. -/
noncomputable def typeICount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => TypeICovered n).card

/-- Count of `n ≤ x` that are Type-II covered. -/
noncomputable def typeIICount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => TypeIICovered n).card

/-- Every `n ≤ x` covered by a non-singleton bad interval is Type-I or
Type-II covered, so `N(x)` is bounded by the sum of the two case counts.
The pointwise split is exactly `bad_interval_sq_multiple_or_long`. -/
theorem badNonSingletonCount_le_typeI_add_typeII (x : ℕ) :
    badNonSingletonCount x ≤ typeICount x + typeIICount x := by
  unfold badNonSingletonCount typeICount typeIICount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, u, v, huv, hbad, hun, hnv⟩ := hn
  rcases bad_interval_sq_multiple_or_long huv hbad with ⟨m, hm, hdiv⟩ | hP
  · exact Or.inl ⟨hnx, u, v, m, huv, hbad, hm, hdiv, hun, hnv⟩
  · exact Or.inr ⟨hnx, u, v, huv, hbad, hP, hun, hnv⟩

/-- Private copy of `isBadInterval_iff` (Localization.lean), kept local to
avoid coupling with JSP314.ShortInterval. -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- Private copy of `exists_mem_dvd_of_largestPrimeFactor` (ProdLPF.lean):
the largest prime factor of `prod = ∏_{i=u}^{v} i` (with `2 ≤ prod`)
divides some member of the interval. -/
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

/-- A bad interval `[u, v]` with `u < v` satisfies `v < 2u`.

Suppose `2u ≤ v`.  Bertrand's postulate gives a prime `p ∈ (v/2, v]`;
since `u ≤ v/2 < p` it lies in `[u, v]`, so `p ∣ prod` and `p ≤ P`, whence
`v < 2P`.  Then every `m ∈ [u, v]` divisible by `P` equals `P` itself
(`m = P·k ≤ v < 2P` forces `k = 1`), so `P` is the *unique* element of
`[u, v]` divisible by `P`.  But `P² ∣ prod = P · (erase-product)` gives
`P ∣ erase-product`, hence `P ∣ m₂` for a *different* `m₂ ∈ [u, v]` —
contradiction. -/
private theorem bad_interval_v_lt_two_mul_u {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : v < 2 * u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  -- A bad interval cannot start at `0`: the product would vanish.
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · exfalso
      apply hP1
      apply largestPrimeFactor_eq_one_iff.2
      have hprod0 : (Finset.Icc u v).prod id = 0 := by
        rw [Finset.prod_eq_zero_iff]
        exact ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
      omega
    · exact h0
  by_contra h2u
  push_neg at h2u  -- h2u : 2 * u ≤ v
  -- Bertrand: a prime `p` with `v/2 < p ≤ 2·(v/2) ≤ v`.
  have hv2 : v / 2 ≠ 0 := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ := Nat.bertrand (v / 2) hv2
  have hpmem : p ∈ Finset.Icc u v := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hp_le_P : p ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor hprod2 hpprime
      (Finset.dvd_prod_of_mem id hpmem)
  have hv_lt_2P : v < 2 * largestPrimeFactor ((Finset.Icc u v).prod id) := by
    omega
  -- Uniqueness: every `m' ∈ [u, v]` divisible by `P` equals `P`.
  have huniq : ∀ m' ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m' →
      m' = largestPrimeFactor ((Finset.Icc u v).prod id) := by
    intro m' hm' hdiv
    obtain ⟨k, hk⟩ := hdiv
    rw [Finset.mem_Icc] at hm'
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        rw [h0, mul_zero] at hk
        omega
      · exact h0
    have hk2 : k < 2 := by
      by_contra hk2
      push_neg at hk2
      have hle : largestPrimeFactor ((Finset.Icc u v).prod id) * 2 ≤
          largestPrimeFactor ((Finset.Icc u v).prod id) * k :=
        Nat.mul_le_mul (le_refl _) hk2
      rw [← hk] at hle
      omega
    interval_cases k
    · simpa using hk
  -- `P` itself lies in `[u, v]`.
  have hPmem : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∈ Finset.Icc u v := by
    obtain ⟨m, hm, hd⟩ := exists_mem_dvd_of_largestPrimeFactor' hprod2
    rwa [huniq m hm hd] at hm
  -- `P² ∣ prod = P · (erase-prod)` forces `P ∣ erase-prod`.
  have hprod_eq : (Finset.Icc u v).prod id
      = largestPrimeFactor ((Finset.Icc u v).prod id) *
        ((Finset.Icc u v).erase
          (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id :=
    (Finset.mul_prod_erase _ _ hPmem).symm
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2
      ∣ largestPrimeFactor ((Finset.Icc u v).prod id) *
        ((Finset.Icc u v).erase
          (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id := by
    rw [← hprod_eq]
    exact hP2
  rw [pow_two] at hdvd
  have hPe : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∣ ((Finset.Icc u v).erase
        (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id :=
    (mul_dvd_mul_iff_left hPprime.ne_zero).mp hdvd
  -- So `P` divides a second, distinct element `m₂ ∈ [u, v]` — contradiction.
  obtain ⟨m2, hm2, hdvd2⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPe
  obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
  exact hne (huniq m2 hm2' hdvd2)

/-- In a Type-II cover of `n`, the largest prime factor `P` of the
interval product satisfies `P ≤ v - u < u ≤ n` (using `v < 2u`), hence
`P` is a prime below `n`. -/
theorem typeIICovered_imp_prime_lt {n : ℕ} (h : TypeIICovered n) :
    ∃ u v P : ℕ, Nat.Prime P ∧ P < n ∧ u ≤ n ∧ n ≤ v ∧ v - u ≥ P ∧
      v < 2 * u ∧ IsBadInterval u v := by
  obtain ⟨u, v, huv, hbad, hPle, hun, hnv⟩ := h
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push_neg at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u huv hbad
  exact ⟨u, v, _, hPprime, by omega, hun, hnv, hPle, hlt, hbad⟩

/-- In a Type-II cover of `n`, every element of the interval is
`P`-smooth (all its prime factors divide the product, hence are `≤ P`)
with `P < n` and `P ≤ v - u`. -/
theorem typeIICovered_imp_smooth_run {n : ℕ} (h : TypeIICovered n) :
    ∃ u v P : ℕ, Nat.Prime P ∧ P < n ∧ u ≤ n ∧ n ≤ v ∧
      (∀ m ∈ Finset.Icc u v, ∀ q, Nat.Prime q → q ∣ m → q ≤ P) ∧
      P ≤ v - u := by
  obtain ⟨u, v, huv, hbad, hPle, hun, hnv⟩ := h
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push_neg at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u huv hbad
  refine ⟨u, v, _, hPprime, by omega, hun, hnv, ?_, hPle⟩
  intro m hm q hq hqm
  exact prime_dvd_le_largestPrimeFactor hprod2 hq
    (dvd_trans hqm (Finset.dvd_prod_of_mem id hm))

end JSP314
