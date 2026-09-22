import JSP314.Main
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# JSP-000314 — Assault3: an independent reduction of the analytic core

This file is a fresh assault on `badNonSingleton_interval_bound` (the single
unproved lemma of `JSP314.Main`).  Everything below is fully proved; the file
isolates *exactly* what remains of Tao's Ta26c argument.

## What is proved here (all proofs complete)

* `isBadInterval_v_add_two_le` — the sharpened Bertrand squeeze: a bad
  interval `[u, v]` with `u < v` satisfies `v + 2 ≤ 2 * u`.  (Slightly
  sharper than the `v < 2 * u` proved in sibling files: `v = 2u − 1` is
  excluded by the same Bertrand-prime argument, since the prime
  `p ∈ (v/2, v]` still satisfies `p ≥ u`.)
* `inNonSingletonBadInterval_window` — every point `n` covered by a
  non-singleton bad interval has the whole covering interval inside the
  dyadic window `(n/2, 2n)`: `n + 2 ≤ 2u` and `v + 2 ≤ 2n`.
* `bad_interval_sq_multiple_or_long'` — the dichotomy (re-proved
  self-contained): a bad interval contains a `P²`-multiple or has
  `P ≤ v − u`.
* `TypeICovered`, `TypeIICovered`, `typeICount`, `typeIICount` and
  `badNonSingletonCount_le_typeI_add_typeII` — the two-case split of `N(x)`.
* `typeICovered_imp_near_badSingleton` — a Type-I covered `n` has a bad
  singleton `m` in its dyadic window with `n` `P(m)`-smooth:
  `m + 2 ≤ 2n`, `n + 2 ≤ 2m`, `P(n) ≤ P(m)`.
* `typeICount_le_badSingletonCount_mul` — `I(x) ≤ S(2x)·(2x+1)` (the best
  elementary covering bound; too weak by a factor `≍ x`, see below).
* `typeIICovered_imp_smooth_run` — a Type-II cover yields a run of `P`
  consecutive `P`-smooth integers `u + 1, …, u + P` all exceeding `P`.
* `SylvesterSchurRuns` — the consecutive-integers form of the
  Sylvester–Schur theorem, and `typeIICount_eq_zero` /
  `badNonSingletonCount_eq_typeICount` — **modulo it**, Type-II coverage is
  empty and `N(x) = I(x)` *exactly*.
* `badNonSingleton_interval_bound_iff_typeI` — **modulo** Sylvester–Schur,
  the headline lemma is *equivalent* to the Type-I estimate
  `I(x) ≤ (log x)^{-1+ε} S(x)`.  This is the precise remaining statement.
* `isBadInterval_sq_sub_one` — `[p²−1, p²]` is bad for every prime `p ≥ 3`
  (product `(p²−1)p²`, largest prime factor `p` since `p²−1 = (p−1)(p+1)`
  is `p`-smooth).  This is an infinite family of non-singleton bad
  intervals: `[8,9]`, `[24,25]`, `[48,49]`, `[120,121]`, …
* `two_mul_erase_card_le_typeICount` — `I(x) ≥ 2·(π(√x) − 1)`: Type-I
  coverage (hence `N`) grows at least as fast as `√x / log x`.
* `tendsto_badNonSingletonCount_atTop` — `N(x) → ∞`.  The target bound is
  therefore genuinely a *ratio* statement `N(x)/S(x) → 0`, not a size
  statement.

## What remains unproved, and why

Modulo `SylvesterSchurRuns` (a true 1892 theorem — Erdős's elementary proof
is partially formalized in `attempts/aux/SylvesterSchur.lean`, which leaves
the quadratic regime `38 ≤ k`, `2k+2 ≤ n ≤ k²` open), this file reduces the
headline lemma to the single inequality

  `typeICount x ≤ (Real.log x) ^ (-(1-ε)) * badSingletonCount x`  eventually.

The best elementary bound proved here is `I(x) ≤ S(2x)·(2x+1)`: every
Type-I covered `n` lies within distance `< min(n, m)` of a bad singleton
`m < 2n`, and covering `n` by `[m − x, m + x]` costs the full factor
`2x + 1`.  That factor `≍ x` cannot be removed elementarily, because the
interval length `v − u` is a priori as large as `u − 2 ≍ n`.  What is needed
is an upper bound on the number of `n ≤ x` that are `P(m)`-smooth for a bad
singleton `m` in the dyadic window `(n/2, 2n)` — i.e. a statement that bad
singletons rarely sit inside long smooth runs.  That is the deep content of
Ta26c (smooth-number counts `Ψ(x, y)` at `y ≍ √x` combined with a
Fourier-style decomposition of the condition `P² ∣ ∏_{i=u}^{v} i`); none of
the required inputs exists in Mathlib, and no elementary shortcut is known.
-/

namespace JSP314

open Nat Filter Classical

/-! ## Section 1: basic helpers and the sharpened squeeze `v + 2 ≤ 2u` -/

/-- Local copy of the `IsBadInterval` unfolding (holds by `Iff.rfl`). -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- `P(prod)` divides some member of the interval (a prime dividing a finite
product divides one of the factors). -/
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

/-- Every `i ∈ [u, v]` is `P`-smooth, where `P = largestPrimeFactor` of the
interval product (assumed `≥ 2`). -/
private theorem le_largestPrimeFactor_prod' {u v i : ℕ}
    (hi : i ∈ Finset.Icc u v) (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rcases le_or_gt i 1 with hi1 | hi1
  · rw [largestPrimeFactor_eq_one_iff.mpr hi1]
    exact (one_lt_largestPrimeFactor h).le
  · have hi2 : 2 ≤ i := hi1
    exact prime_dvd_le_largestPrimeFactor h (largestPrimeFactor_prime hi2)
      ((largestPrimeFactor_dvd hi2).trans (Finset.dvd_prod_of_mem id hi))

/-- **Sharpened squeeze**: a bad interval `[u, v]` with `u < v` satisfies
`v + 2 ≤ 2u` (equivalently `v ≤ 2u − 2`; the case `v = 2u − 1` is excluded
by the same argument since the Bertrand prime `p ∈ (v/2, v]` satisfies
`p ≥ u` already when `v ≥ 2u − 1`).

Suppose `v ≥ 2u − 1`.  Bertrand's postulate gives a prime `p` with
`v/2 < p ≤ v`; since `p > v/2 ≥ u − 1` it lies in `[u, v]`, so `p ∣ prod`
and `p ≤ P`.  Hence `2P ≥ 2p > v`: every `m ∈ [u, v]` divisible by `P`
satisfies `0 < m ≤ v < 2P`, so `m = P`.  Therefore `P` is the *unique*
multiple of `P` in `[u, v]`, but `P² ∣ prod = P · (erase-product)` forces
`P ∣ m₂` for a different `m₂` — contradiction. -/
theorem isBadInterval_v_add_two_le {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : v + 2 ≤ 2 * u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push Not at h
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
  push Not at h2u  -- h2u : 2 * u < v + 2, i.e. v ≥ 2u - 1
  -- Bertrand: a prime `p` with `v/2 < p ≤ 2·(v/2) ≤ v`.
  have hv2 : v / 2 ≠ 0 := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (v / 2) hv2
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
      push Not at hk2
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
    (Nat.mul_dvd_mul_iff_left hPprime.pos).mp hdvd
  -- So `P` divides a second, distinct element `m₂ ∈ [u, v]` — contradiction.
  obtain ⟨m2, hm2, hdvd2⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPe
  obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
  exact hne (huniq m2 hm2' hdvd2)

/-- In particular `u ≥ 3` for a non-singleton bad interval (the first example
is `[8, 9]`). -/
theorem three_le_u_of_isBadInterval {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : 3 ≤ u :=
  by have h := isBadInterval_v_add_two_le huv hbad; omega

/-- Every point covered by a non-singleton bad interval sits in the middle of
it: the whole covering interval `[u, v]` lies in the dyadic window
`(n/2, 2n)`, i.e. `n + 2 ≤ 2u` and `v + 2 ≤ 2n`. -/
theorem inNonSingletonBadInterval_window {n : ℕ}
    (h : InNonSingletonBadInterval n) :
    ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
      3 ≤ u ∧ n + 2 ≤ 2 * u ∧ v + 2 ≤ 2 * n := by
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := h
  have h2 := isBadInterval_v_add_two_le huv hbad
  exact ⟨u, v, huv, hbad, hun, hnv, by omega, by omega, by omega⟩

/-! ## Section 2: the dichotomy and the two-case split of `N(x)` -/

/-- The fundamental dichotomy: a bad interval `[u, v]` either contains a
multiple of `P²` (where `P` is the largest prime factor of the interval
product) or satisfies `P ≤ v - u`. -/
theorem bad_interval_sq_multiple_or_long' {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) :
    (∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) ∨
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push Not at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  by_cases hsq : ∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m
  · exact Or.inl hsq
  · right
    push Not at hsq
    obtain ⟨m1, hm1, hdvd1⟩ := exists_mem_dvd_of_largestPrimeFactor' hprod2
    have hnot1 : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m1 :=
      hsq m1 hm1
    obtain ⟨a, ha⟩ := hdvd1
    have hPa : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a := by
      rintro ⟨b, hb⟩
      apply hnot1
      exact ⟨b, by rw [ha, hb]; ring⟩
    have hprod_eq : (Finset.Icc u v).prod id
        = m1 * ((Finset.Icc u v).erase m1).prod id :=
      (Finset.mul_prod_erase _ _ hm1).symm
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
      (Nat.mul_dvd_mul_iff_left hPprime.pos).mp hdvd
    have hPr : largestPrimeFactor ((Finset.Icc u v).prod id)
        ∣ ((Finset.Icc u v).erase m1).prod id :=
      (hPprime.dvd_mul.mp hPar).resolve_left hPa
    obtain ⟨m2, hm2, hdvd2⟩ :=
      ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPr
    obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
    have hdvd1' : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 :=
      ⟨a, ha⟩
    have hd12 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 - m2 :=
      Nat.dvd_sub hdvd1' hdvd2
    have hd21 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 - m1 :=
      Nat.dvd_sub hdvd2 hdvd1'
    rw [Finset.mem_Icc] at hm1 hm2'
    rcases lt_or_gt_of_ne hne with h | h
    · have hpos : 0 < m1 - m2 := by omega
      have hle := Nat.le_of_dvd hpos hd12
      omega
    · have hpos : 0 < m2 - m1 := by omega
      have hle := Nat.le_of_dvd hpos hd21
      omega

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

/-- Type-I coverage implies non-singleton coverage (pointwise), so
`typeICount x ≤ N(x)`. -/
theorem typeICount_le_badNonSingletonCount (x : ℕ) :
    typeICount x ≤ badNonSingletonCount x := by
  unfold typeICount badNonSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  obtain ⟨hnx, u, v, m, huv, hbad, -, -, hun, hnv⟩ := hn
  exact ⟨hnx, u, v, huv, hbad, hun, hnv⟩

/-- The two-case split: `N(x) ≤ I(x) + II(x)`. -/
theorem badNonSingletonCount_le_typeI_add_typeII (x : ℕ) :
    badNonSingletonCount x ≤ typeICount x + typeIICount x := by
  unfold badNonSingletonCount typeICount typeIICount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, u, v, huv, hbad, hun, hnv⟩ := hn
  rcases bad_interval_sq_multiple_or_long' huv hbad with ⟨m, hm, hdiv⟩ | hP
  · exact Or.inl ⟨hnx, u, v, m, huv, hbad, hm, hdiv, hun, hnv⟩
  · exact Or.inr ⟨hnx, u, v, huv, hbad, hP, hun, hnv⟩

/-! ## Section 3: Type-I structure and the elementary counting bound -/

/-- If `m ∈ [u, v]` is divisible by `P²` (`P` the largest prime factor of the
interval product) then `2 ≤ m` and `P(m) = P`. -/
private theorem two_le_and_lpf_eq_of_sq_dvd_mem' {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨_huv, hP1, _hP2⟩ := hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push Not at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hmdvd : m ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [zero_dvd_iff] at hmdvd; omega
    · exact h0
  have hm2 : 2 ≤ m :=
    (one_lt_pow₀ hPprime.one_lt two_ne_zero).trans_le
      (Nat.le_of_dvd hmpos hdvd)
  have hPdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
    (dvd_pow_self _ two_ne_zero).trans hdvd
  have hle1 :
      largestPrimeFactor m ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor hprod2 (largestPrimeFactor_prime hm2)
      ((largestPrimeFactor_dvd hm2).trans hmdvd)
  have hle2 :
      largestPrimeFactor ((Finset.Icc u v).prod id) ≤ largestPrimeFactor m :=
    prime_dvd_le_largestPrimeFactor hm2 hPprime hPdvd
  exact ⟨hm2, le_antisymm hle1 hle2⟩

/-- The `P²`-multiple `m` in a bad interval is a bad singleton. -/
private theorem sq_dvd_mem_isBadSingleton' {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem' hbad hm hdvd
  refine ⟨by omega, ?_⟩
  rw [heq]
  exact hdvd

/-- **Type-I structural statement.**  A Type-I covered `n` lies in the
dyadic window of a bad singleton: there is `m` with `1 < m`, `P(m)² ∣ m`,
`n + 2 ≤ 2m` and `m + 2 ≤ 2n` (equivalently `m ∈ (n/2, 2n)` and
`n ∈ (m/2, 2m)`), and moreover `n` is `P(m)`-smooth:
`P(n) ≤ P(m)`. -/
theorem typeICovered_imp_near_badSingleton {n : ℕ} (h : TypeICovered n) :
    ∃ m : ℕ, 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m ∧
      n + 2 ≤ 2 * m ∧ m + 2 ≤ 2 * n ∧
      largestPrimeFactor n ≤ largestPrimeFactor m := by
  obtain ⟨u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := h
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem' hbad hm hdvd
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push Not at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  have hlt : v + 2 ≤ 2 * u := isBadInterval_v_add_two_le huv hbad
  rw [Finset.mem_Icc] at hm
  have hnle : largestPrimeFactor n ≤ largestPrimeFactor m := by
    have h := le_largestPrimeFactor_prod'
      (Finset.mem_Icc.mpr ⟨hun, hnv⟩) hprod2
    rwa [← heq] at h
  refine ⟨m, by omega, ?_, by omega, by omega, hnle⟩
  rw [heq]
  exact hdvd

/-- **The smoothed-window bound.**  Every Type-I covered `n ≤ x` is a
`P(m)`-smooth integer in the dyadic window of a bad singleton `m`.  This
predicate is exactly what needs to be counted by the missing analytic
input. -/
theorem typeICount_le_smoothWindow (x : ℕ) :
    typeICount x ≤ ((Finset.range (x + 1)).filter fun n =>
      ∃ m : ℕ, 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m ∧
        n + 2 ≤ 2 * m ∧ m + 2 ≤ 2 * n ∧
        largestPrimeFactor n ≤ largestPrimeFactor m).card := by
  unfold typeICount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, typeICovered_imp_near_badSingleton hn.2⟩

/-- **Elementary covering bound.**  `I(x) ≤ S(2x)·(2x + 1)`.

Each Type-I covered `n ≤ x` lies within distance `≤ x` of a bad singleton
`m < 2n ≤ 2x` (in fact `m + 2 ≤ 2n`); covering `n` by `Icc (m − x) (m + x)`
and using `Finset.card_biUnion_le` gives the claim.

This bound is *far too weak*: the RHS exceeds `S(x)` by a factor `≍ x`,
while the target needs a vanishing factor `(log x)^{-1+ε}`.  The reason it
cannot be improved elementarily is that `v − u` (the true covering radius)
can be comparable to `n`; controlling it requires proving that bad
singletons rarely have long `P`-smooth runs of neighbours, which is the
analytic content of Ta26c. -/
theorem typeICount_le_badSingletonCount_mul (x : ℕ) :
    typeICount x ≤ badSingletonCount (2 * x) * (2 * x + 1) := by
  unfold typeICount
  set S := (Finset.range (2 * x + 1)).filter
    (fun m => 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m) with hS
  -- Each counted `n` lies in `[m - x, m + x]` for a bad singleton `m ≤ 2x`.
  have hsub : (Finset.range (x + 1)).filter (fun n => TypeICovered n)
      ⊆ S.biUnion (fun m => Finset.Icc (m - x) (m + x)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := hn
    obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem' hbad hm hdvd
    have hlt : v + 2 ≤ 2 * u := isBadInterval_v_add_two_le huv hbad
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [hS, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ?_⟩
      rw [heq]
      exact hdvd
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hIcc_card : ∀ m : ℕ, (Finset.Icc (m - x) (m + x)).card ≤ 2 * x + 1 := by
    intro m
    rw [Nat.card_Icc]
    omega
  have hS_card : S.card = badSingletonCount (2 * x) := by
    rw [hS]
    rfl
  calc ((Finset.range (x + 1)).filter fun n => TypeICovered n).card
      ≤ (S.biUnion fun m => Finset.Icc (m - x) (m + x)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ m ∈ S, (Finset.Icc (m - x) (m + x)).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ S, (2 * x + 1) := Finset.sum_le_sum fun m _ => hIcc_card m
    _ = S.card * (2 * x + 1) := Finset.sum_const_nat fun _ _ => rfl
    _ = badSingletonCount (2 * x) * (2 * x + 1) := by rw [hS_card]

/-! ## Section 4: Type-II covers produce smooth runs (Sylvester–Schur) -/

/-- A Type-II cover of `n` yields a run of `P` consecutive `P`-smooth
integers `u + 1, …, u + P`, all `> P` (indeed `P + 2 ≤ u` by the sharpened
squeeze `v + 2 ≤ 2u`). -/
theorem typeIICovered_imp_smooth_run {n : ℕ} (h : TypeIICovered n) :
    ∃ u P : ℕ, Nat.Prime P ∧ P + 2 ≤ u ∧
      ∀ m ∈ Finset.Icc (u + 1) (u + P), ∀ q : ℕ, Nat.Prime q → q ∣ m →
        q ≤ P := by
  obtain ⟨u, v, huv, hbad, hPle, hun, hnv⟩ := h
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push Not at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hlt : v + 2 ≤ 2 * u := isBadInterval_v_add_two_le huv hbad
  -- `P ≤ v − u ≤ u − 2` and `u + P ≤ v`.
  refine ⟨u, _, hPprime, by omega, ?_⟩
  intro m hm q hq hqm
  have hmem : m ∈ Finset.Icc u v := by
    rw [Finset.mem_Icc] at hm ⊢
    omega
  exact prime_dvd_le_largestPrimeFactor hprod2 hq
    (dvd_trans hqm (Finset.dvd_prod_of_mem id hmem))

/-- The **Sylvester–Schur hypothesis** in consecutive-integers form: among
any `P` consecutive integers all exceeding `P`, some element has a prime
factor `> P`.  This is a true theorem (Sylvester 1892; elementary proof by
Erdős), not currently available in Mathlib; the sibling file
`attempts/aux/SylvesterSchur.lean` formalizes most of Erdős's argument and
leaves only the quadratic regime open.  We keep it as a hypothesis so this
file stays fully proved. -/
def SylvesterSchurRuns : Prop :=
  ∀ P u : ℕ, Nat.Prime P → P < u →
    ∃ m ∈ Finset.Icc (u + 1) (u + P), ∃ q : ℕ, Nat.Prime q ∧ P < q ∧ q ∣ m

/-- Modulo Sylvester–Schur, no `n` is Type-II covered: the cover produces a
run of `P` consecutive `P`-smooth integers all `> P`, contradicting the
existence of a prime factor `> P` in the run. -/
theorem not_typeIICovered (hss : SylvesterSchurRuns) {n : ℕ}
    (h : TypeIICovered n) : False := by
  obtain ⟨u, P, hPp, hPu, hsm⟩ := typeIICovered_imp_smooth_run h
  obtain ⟨m, hm, q, hq, hPq, hqm⟩ := hss P u hPp (by omega)
  exact absurd (hsm m hm q hq hqm) (not_le_of_gt hPq)

/-- Modulo Sylvester–Schur, `typeIICount x = 0` for every `x`. -/
theorem typeIICount_eq_zero (hss : SylvesterSchurRuns) (x : ℕ) :
    typeIICount x = 0 := by
  unfold typeIICount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  exact not_typeIICovered hss

/-- Modulo Sylvester–Schur, `N(x) ≤ I(x)`; combined with the pointwise
`I(x) ≤ N(x)` this gives `N(x) = I(x)` exactly. -/
theorem badNonSingletonCount_le_typeICount (hss : SylvesterSchurRuns)
    (x : ℕ) : badNonSingletonCount x ≤ typeICount x := by
  have h := badNonSingletonCount_le_typeI_add_typeII x
  rw [typeIICount_eq_zero hss x] at h
  omega

/-- Modulo Sylvester–Schur, non-singleton coverage is *exactly* Type-I
coverage: `N(x) = I(x)`. -/
theorem badNonSingletonCount_eq_typeICount (hss : SylvesterSchurRuns)
    (x : ℕ) : badNonSingletonCount x = typeICount x :=
  le_antisymm (badNonSingletonCount_le_typeICount hss x)
    (typeICount_le_badNonSingletonCount x)

/-- Modulo Sylvester–Schur, the best unconditional bound on `N` available:
`N(x) ≤ S(2x)·(2x + 1)`.  The factor `2x + 1` is the obstacle: the target
demands a vanishing factor of polylogarithmic size. -/
theorem badNonSingletonCount_le_badSingletonCount_mul
    (hss : SylvesterSchurRuns) (x : ℕ) :
    badNonSingletonCount x ≤ badSingletonCount (2 * x) * (2 * x + 1) :=
  (badNonSingletonCount_le_typeICount hss x).trans
    (typeICount_le_badSingletonCount_mul x)

/-! ## Section 5: the exact reduction of the headline bound -/

/-- **The reduction theorem.**  Modulo Sylvester–Schur, the headline
estimate `badNonSingleton_interval_bound` is *equivalent* to the Type-I
estimate

    `typeICount x ≤ (log x) ^ (-(1-ε)) * badSingletonCount x`  eventually.

This isolates the entire remaining analytic content of Ta26c: Sylvester–Schur
is a known theorem (its full formalization reduces to Erdős's quadratic
regime), while the Type-I bound is the genuinely deep input. -/
theorem badNonSingleton_interval_bound_iff_typeI (hss : SylvesterSchurRuns) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) ↔
    (∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (typeICount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) := by
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with x hx
    have hI : (typeICount x : ℝ) ≤ badNonSingletonCount x := by
      exact_mod_cast typeICount_le_badNonSingletonCount x
    linarith
  · intro h ε hε
    filter_upwards [h ε hε] with x hx
    have hN : (badNonSingletonCount x : ℝ) ≤ typeICount x := by
      exact_mod_cast badNonSingletonCount_le_typeICount hss x
    linarith

/-! ## Section 6: an infinite family of bad intervals; `N(x) → ∞` -/

/-- The interval `[p²−1, p²]` has exactly two elements; the product is
`(p²−1)·p²`. -/
private theorem prod_Icc_sq_sub_one {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Icc (p ^ 2 - 1) (p ^ 2)).prod id = (p ^ 2 - 1) * p ^ 2 := by
  have hpp : 0 < p ^ 2 := pow_pos hp.pos 2
  have hIcc : Finset.Icc (p ^ 2 - 1) (p ^ 2) = {p ^ 2 - 1, p ^ 2} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with rfl | hlt
      · exact Or.inr rfl
      · exact Or.inl (by omega)
    · rintro (rfl | rfl) <;> omega
  rw [hIcc, Finset.prod_pair (show p ^ 2 - 1 ≠ p ^ 2 by omega)]
  simp only [id_eq]

/-- For a prime `p ≥ 3`, the largest prime factor of `(p²−1)·p²` is `p`:
every prime divisor `q` of `p²−1 = (p+1)(p−1)` satisfies `q ≤ p` (a divisor
of `p−1` is `< p`; a prime divisor `q` of `p+1` satisfies `q ≤ p` too,
because `q = p + 1` would make the even number `p + 1 > 2` prime), and
`p ∣ p²`. -/
theorem largestPrimeFactor_Icc_sq_sub_one {p : ℕ} (hp : Nat.Prime p)
    (h3 : 3 ≤ p) :
    largestPrimeFactor ((Finset.Icc (p ^ 2 - 1) (p ^ 2)).prod id) = p := by
  have hpp : 0 < p ^ 2 := pow_pos hp.pos 2
  have hprod := prod_Icc_sq_sub_one hp
  have hprod2 : 2 ≤ (Finset.Icc (p ^ 2 - 1) (p ^ 2)).prod id := by
    rw [hprod]
    have h9 : 9 ≤ p ^ 2 := by
      have h := Nat.pow_le_pow_left h3 2
      norm_num at h
      exact h
    have := Nat.mul_le_mul (show 8 ≤ p ^ 2 - 1 by omega)
      (show 9 ≤ p ^ 2 by omega)
    omega
  -- Every prime divisor of the product is `≤ p`.
  have hP_le : ∀ q : ℕ, Nat.Prime q →
      q ∣ (Finset.Icc (p ^ 2 - 1) (p ^ 2)).prod id → q ≤ p := by
    intro q hq hqd
    rw [hprod] at hqd
    rcases hq.dvd_mul.mp hqd with h1 | h1
    · -- `q ∣ p²−1 = (p+1)(p−1)`.
      have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := Nat.sq_sub_sq p 1
      rw [hfac] at h1
      rcases hq.dvd_mul.mp h1 with h2 | h2
      · have hqle : q ≤ p + 1 := Nat.le_of_dvd (by omega) h2
        rcases lt_or_eq_of_le hqle with hlt | heq
        · omega
        · -- `q = p + 1` is prime, but `p + 1` is even and `> 2`.
          exfalso
          rcases hp.eq_two_or_odd' with hpp2 | ⟨j, hj⟩
          · omega
          · obtain ⟨c, hc⟩ : (2 : ℕ) ∣ p + 1 := ⟨j + 1, by omega⟩
            have hq2 : (2 : ℕ) = q :=
              (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp ⟨c, by omega⟩
            omega
      · have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) h2
        omega
    · -- `q ∣ p²` forces `q = p`.
      have hqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h1)
      exact hqp.le
  have hpdvd : p ∣ (Finset.Icc (p ^ 2 - 1) (p ^ 2)).prod id := by
    rw [hprod]
    exact Dvd.dvd.mul_left (dvd_pow_self p two_ne_zero) (p ^ 2 - 1)
  exact le_antisymm
    (hP_le _ (largestPrimeFactor_prime hprod2) (largestPrimeFactor_dvd hprod2))
    (prime_dvd_le_largestPrimeFactor hprod2 hp hpdvd)

/-- The interval `[p²−1, p²]` is bad for every prime `p ≥ 3`: its product is
`(p²−1)p²` with largest prime factor `p`, and `p²` divides the product.
This yields an infinite family of non-singleton bad intervals,
e.g. `[8,9]`, `[24,25]`, `[48,49]`, `[120,121]`, `[168,169]`, `[288,289]`. -/
theorem isBadInterval_sq_sub_one {p : ℕ} (hp : Nat.Prime p) (h3 : 3 ≤ p) :
    IsBadInterval (p ^ 2 - 1) (p ^ 2) := by
  have hprod := prod_Icc_sq_sub_one hp
  refine isBadInterval_iff'.mpr ⟨by omega, ?_, ?_⟩
  · rw [largestPrimeFactor_Icc_sq_sub_one hp h3]
    omega
  · rw [largestPrimeFactor_Icc_sq_sub_one hp h3, hprod]
    exact Dvd.dvd.mul_left (dvd_refl (p ^ 2)) (p ^ 2 - 1)

/-- The squares of primes `p ≥ 3` are Type-I covered by `[p²−1, p²]`. -/
theorem typeICovered_sq {p : ℕ} (hp : Nat.Prime p) (h3 : 3 ≤ p) :
    TypeICovered (p ^ 2) := by
  have hpp : 0 < p ^ 2 := pow_pos hp.pos 2
  refine ⟨p ^ 2 - 1, p ^ 2, p ^ 2, by omega, isBadInterval_sq_sub_one hp h3,
    Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩, ?_, by omega, le_refl _⟩
  rw [largestPrimeFactor_Icc_sq_sub_one hp h3]

/-- The predecessors `p²−1` of prime squares (`p ≥ 3`) are Type-I covered. -/
theorem typeICovered_sq_sub_one {p : ℕ} (hp : Nat.Prime p) (h3 : 3 ≤ p) :
    TypeICovered (p ^ 2 - 1) := by
  have hpp : 0 < p ^ 2 := pow_pos hp.pos 2
  refine ⟨p ^ 2 - 1, p ^ 2, p ^ 2, by omega, isBadInterval_sq_sub_one hp h3,
    Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩, ?_, le_refl _, by omega⟩
  rw [largestPrimeFactor_Icc_sq_sub_one hp h3]

/-- **Lower bound for Type-I coverage**: `I(x) ≥ 2·(π(√x) − 1)`.

Every prime `p ∈ [3, √x]` contributes two distinct Type-I covered points
`p² − 1` and `p²` via the bad interval `[p²−1, p²]`.  The images
`{p²}` and `{p²−1}` are disjoint (a nontrivial square minus one is never a
square). -/
theorem two_mul_erase_card_le_typeICount (x : ℕ) :
    2 * (((Nat.sqrt x).primesLE.erase 2).card) ≤ typeICount x := by
  classical
  set s := (Nat.sqrt x).primesLE.erase 2 with hs
  -- Elements of `s`: primes `p` with `3 ≤ p` and `p ≤ √x`.
  have h3 : ∀ p ∈ s, Nat.Prime p ∧ 3 ≤ p ∧ p ≤ Nat.sqrt x := by
    intro p hp
    rw [hs, Finset.mem_erase, Nat.mem_primesLE] at hp
    obtain ⟨hpne, hple, hpp⟩ := hp
    exact ⟨hpp, by have := hpp.two_le; omega, hple⟩
  have hT1sub : s.image (fun p => p ^ 2) ⊆
      (Finset.range (x + 1)).filter (fun n => TypeICovered n) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨hpp, hp3, hple⟩ := h3 p hp
    have hpx : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, typeICovered_sq hpp hp3⟩
  have hT2sub : s.image (fun p => p ^ 2 - 1) ⊆
      (Finset.range (x + 1)).filter (fun n => TypeICovered n) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨hpp, hp3, hple⟩ := h3 p hp
    have hpx : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, typeICovered_sq_sub_one hpp hp3⟩
  -- The two images are disjoint: `q² − 1 = p²` has no solutions.
  have hdis : Disjoint (s.image (fun p => p ^ 2))
      (s.image (fun p => p ^ 2 - 1)) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_image] at ha1 ha2
    obtain ⟨p, hp, rfl⟩ := ha1
    obtain ⟨q, hq, haq⟩ := ha2
    obtain ⟨hpp, hp3, hple⟩ := h3 p hp
    obtain ⟨hqp, hq3, hqle⟩ := h3 q hq
    -- `haq : q ^ 2 - 1 = p ^ 2`, i.e. `q² = p² + 1`
    have hsq : q ^ 2 = p ^ 2 + 1 := by
      have hq2 : 0 < q ^ 2 := pow_pos hqp.pos 2
      omega
    have hpg : p < q := by
      by_contra hcon
      push Not at hcon
      have hle : q ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hcon 2
      omega
    have hle : (p + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hpg 2
    have hexp : (p + 1) ^ 2 = p ^ 2 + (2 * p + 1) := by ring
    omega
  have hinj1 : Set.InjOn (fun p : ℕ => p ^ 2) s :=
    fun a _ b _ hab => Nat.pow_left_injective two_ne_zero hab
  have hinj2 : Set.InjOn (fun p : ℕ => p ^ 2 - 1) s := by
    intro a ha b hb hab
    obtain ⟨haP, ha3, -⟩ := h3 a (Finset.mem_coe.mp ha)
    obtain ⟨hbP, hb3, -⟩ := h3 b (Finset.mem_coe.mp hb)
    have hab' : a ^ 2 - 1 = b ^ 2 - 1 := hab
    have hsq : a ^ 2 = b ^ 2 := by
      have ha2 : 0 < a ^ 2 := pow_pos haP.pos 2
      have hb2 : 0 < b ^ 2 := pow_pos hbP.pos 2
      omega
    exact Nat.pow_left_injective two_ne_zero hsq
  unfold typeICount
  calc 2 * s.card
      = (s.image (fun p => p ^ 2) ∪ s.image (fun p => p ^ 2 - 1)).card := by
        rw [Finset.card_union_of_disjoint hdis,
          Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2,
          two_mul]
    _ ≤ ((Finset.range (x + 1)).filter fun n => TypeICovered n).card :=
        Finset.card_le_card (Finset.union_subset hT1sub hT2sub)

/-- `N(x) ≥ 2·(π(√x) − 1)`: non-singleton coverage grows at least at the
`√x / log x` rate, via `typeICount ≤ badNonSingletonCount`. -/
theorem badNonSingletonCount_ge_two_mul_erase (x : ℕ) :
    2 * (((Nat.sqrt x).primesLE.erase 2).card) ≤ badNonSingletonCount x :=
  (two_mul_erase_card_le_typeICount x).trans
    (typeICount_le_badNonSingletonCount x)

/-- Cleaner form: `N(x) ≥ π(√x) − 1`. -/
theorem badNonSingletonCount_ge_primeCounting_sub_one (x : ℕ) :
    Nat.primeCounting (Nat.sqrt x) - 1 ≤ badNonSingletonCount x := by
  have h := badNonSingletonCount_ge_two_mul_erase x
  have hcard : (Nat.sqrt x).primesLE.card - 1 ≤
      ((Nat.sqrt x).primesLE.erase 2).card := by
    by_cases h2 : 2 ∈ (Nat.sqrt x).primesLE
    · have e := Finset.card_erase_of_mem h2
      omega
    · have e := congrArg Finset.card (Finset.erase_eq_of_notMem h2)
      omega
  have hπ : (Nat.sqrt x).primesLE.card = Nat.primeCounting (Nat.sqrt x) :=
    Nat.primesLE_card_eq_primeCounting _
  omega

/-- `Nat.sqrt` tends to `atTop`. -/
private theorem tendsto_nat_sqrt_atTop' :
    Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨b ^ 2, fun _ hn => Nat.le_sqrt'.2 hn⟩

/-- `x ↦ π(√x) − 1` tends to `atTop`. -/
private theorem tendsto_primeCounting_sqrt_sub_one :
    Tendsto (fun x : ℕ => Nat.primeCounting (Nat.sqrt x) - 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  have h : Tendsto (fun x : ℕ => Nat.primeCounting (Nat.sqrt x)) atTop atTop :=
    Nat.tendsto_primeCounting.comp tendsto_nat_sqrt_atTop'
  rw [tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h (K + 1)
  exact ⟨N, fun x hx => by
    have h2 : K + 1 ≤ Nat.primeCounting (Nat.sqrt x) := hN x hx
    omega⟩

/-- **`N(x) → ∞`** (at least at the `√x / log x` rate).  Hence the target
bound `N(x) ≤ (log x)^{-1+ε} · S(x)` is a genuine ratio statement between
two diverging counts: it asserts `N(x)/S(x) → 0` at a polylogarithmic
rate. -/
theorem tendsto_badNonSingletonCount_atTop :
    Tendsto badNonSingletonCount atTop atTop :=
  tendsto_atTop_mono badNonSingletonCount_ge_primeCounting_sub_one
    tendsto_primeCounting_sqrt_sub_one

end JSP314
