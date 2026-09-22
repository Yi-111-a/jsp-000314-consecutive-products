import JSP314.TwoCaseCount
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Union
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push

/-!
# JSP-000314 — Type-I covers: bad-singleton localization and a counting bound

In a Type-I cover of `n` (see `JSP314.TwoCaseCount.TypeICovered`), the
covering interval `[u, v]` is a non-singleton bad interval containing an
element `m` divisible by `P²`, where `P` is the largest prime factor of
`prod = ∏_{i=u}^{v} i`.  This file proves:

* `typeI_mem_imp_badSingleton`: that `P²`-multiple `m` is itself a *bad
  singleton* — `1 < m` and `P(m)² ∣ m` (in fact `P(m) = P`, since `P ∣ m`
  and every prime factor of `m` is `≤ P` because `m ∣ prod`).
* `typeI_mem_imp_near_smooth_singleton`: the full smoothness package —
  `P` is prime, `n` and `m` both lie in `[u, v]`, every `i ∈ [u, v]` is
  `P`-smooth in the sense `P(i) ≤ P`, `P² ∣ m`, and `P(m) = P`.
* `typeICovered_imp_near_badSingleton`: the proximity statement — `m` is a
  bad singleton with `m < 2n` and `n < 2m` (via `v < 2u`, the
  Bertrand-postulate bound for non-singleton bad intervals).
* `typeICount_le_badSingletonCount_two_mul`: the counting bound
  `typeICount x ≤ badSingletonCount (2 * x) * (2 * x + 1)`.

## What is and is not provable here

A `√x`-scale bound of the shape
`typeICount x ≤ badSingletonCount (x + √x) · (2√x + 1)` would require
`v - u < P` for Type-I intervals (each covered `n` within distance `< P(m)`
of `m`).  That is **not** available elementarily: the dichotomy
`bad_interval_sq_multiple_or_long` is a non-exclusive disjunction, so a
Type-I interval may still satisfy `P ≤ v - u`; badness alone does not bound
the interval length by `P`.  The sharp localization that *is* provable is
`v < 2u` (copied below from `JSP314.TwoCaseCount`, where it is `private`),
which places each covered `n` within distance `< min(n, m)` of the bad
singleton `m < 2n`.  Covering `n` by `Icc (m - x) (m + x)` then yields the
`badSingletonCount (2x) · (2x + 1)` bound above — the same covering-bound
quality as `covered_by_short_type1_interval_card_le`, but now applied to
*all* Type-I covers (no length hypothesis), at the cost of radius `x` and
the factor-2 enlargement of the singleton range.

All auxiliary lemmas are `private` (copied from `JSP314.Covering`,
`JSP314.TwoCaseCount`, and `attempts/aux/ProdLPF.lean`) so this file is
self-contained modulo the compiled `JSP314` library.
-/

namespace JSP314

open Classical

/-- Local copy of `isBadInterval_iff` (`IsBadInterval` is a `let`-free
unfolding of its definition). -/
private theorem isBadInterval_iff_local {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- Local copy of `le_largestPrimeFactor_prod` (attempts/aux/ProdLPF.lean):
every `i ∈ [u, v]` is `P`-smooth, where `P` is the largest prime factor of
the interval product (assumed `≥ 2`). -/
private theorem le_largestPrimeFactor_prod_local {u v i : ℕ}
    (hi : i ∈ Finset.Icc u v) (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rcases le_or_lt i 1 with hi1 | hi1
  · rw [largestPrimeFactor_eq_one_iff.mpr hi1]
    exact (one_lt_largestPrimeFactor h).le
  · have hi2 : 2 ≤ i := hi1
    exact prime_dvd_le_largestPrimeFactor h (largestPrimeFactor_prime hi2)
      ((largestPrimeFactor_dvd hi2).trans (Finset.dvd_prod_of_mem id hi))

/-- Local copy of `exists_mem_dvd_of_largestPrimeFactor`
(attempts/aux/ProdLPF.lean): `P(prod)` divides some member of `[u, v]`. -/
private theorem exists_mem_dvd_of_largestPrimeFactor_local {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id :=
    largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- Local copy of `two_le_and_lpf_eq_of_sq_dvd_mem` (JSP314.Covering):
if `m ∈ [u, v]` is divisible by `P²` with `P` the largest prime factor of
the interval product, then `2 ≤ m` and `P(m) = P`. -/
private theorem two_le_and_lpf_eq_of_sq_dvd_mem_local {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨_huv, hP1, _hP2⟩ := hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  -- `m` divides the product, which is positive, so `m` is positive.
  have hmdvd : m ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [zero_dvd_iff] at hmdvd; omega
    · exact h0
  -- `m ≥ P² ≥ 2`.
  have hm2 : 2 ≤ m :=
    (one_lt_pow₀ hPprime.one_lt two_ne_zero).trans_le
      (Nat.le_of_dvd hmpos hdvd)
  -- `P ∣ m` since `P ∣ P² ∣ m`.
  have hPdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
    (dvd_pow_self _ two_ne_zero).trans hdvd
  -- `P(m) ≤ P`: `P(m)` is a prime dividing `prod`.
  have hle1 :
      largestPrimeFactor m ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor hprod2 (largestPrimeFactor_prime hm2)
      ((largestPrimeFactor_dvd hm2).trans hmdvd)
  -- `P ≤ P(m)`: `P` is a prime dividing `m`.
  have hle2 :
      largestPrimeFactor ((Finset.Icc u v).prod id) ≤ largestPrimeFactor m :=
    prime_dvd_le_largestPrimeFactor hm2 hPprime hPdvd
  exact ⟨hm2, le_antisymm hle1 hle2⟩

/-- Local copy of `sq_dvd_mem_isBadSingleton` (JSP314.Covering): the `P²`
multiple `m` in a bad interval is a bad singleton. -/
private theorem sq_dvd_mem_isBadSingleton_local {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem_local hbad hm hdvd
  refine ⟨hm2, ?_⟩
  rw [heq]
  exact hdvd

/-- Local copy of `bad_interval_v_lt_two_mul_u` (JSP314.TwoCaseCount, where
it is `private`): a bad interval `[u, v]` with `u < v` satisfies `v < 2u`.

Suppose `2u ≤ v`.  Bertrand's postulate gives a prime `p ∈ (v/2, v]`; since
`u ≤ v/2 < p` it lies in `[u, v]`, so `p ∣ prod` and `p ≤ P`, whence
`v < 2P`.  Then every `m' ∈ [u, v]` divisible by `P` equals `P` itself
(`m' = P·k ≤ v < 2P` forces `k = 1`), so `P` is the *unique* element of
`[u, v]` divisible by `P`.  But `P² ∣ prod = P · (erase-product)` gives
`P ∣ erase-product`, hence `P ∣ m₂` for a *different* `m₂ ∈ [u, v]` —
contradiction. -/
private theorem bad_interval_v_lt_two_mul_u_local {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : v < 2 * u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff_local.1 hbad
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
    obtain ⟨m, hm, hd⟩ := exists_mem_dvd_of_largestPrimeFactor_local hprod2
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

/-- **Task 1.** In a Type-I cover of `n`, the `P²`-multiple `m` furnished by
the cover is itself a bad singleton: `1 < m` and `P(m)² ∣ m` (indeed
`P(m) = P`, since `P ∣ m` and `m ∣ prod` is `P`-smooth). -/
theorem typeI_mem_imp_badSingleton {n : ℕ} (h : TypeICovered n) :
    ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ m ∈ Finset.Icc u v ∧
      u ≤ n ∧ n ≤ v ∧ 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := h
  obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton_local hbad hm hdvd
  exact ⟨u, v, m, huv, hbad, hm, hun, hnv, hm1, hm2⟩

/-- **Task 2.** In a Type-I cover of `n`, writing `P` for the largest prime
factor of the interval product: `P` is prime, `n` and the `P²`-multiple `m`
both lie in `[u, v]`, every `i ∈ [u, v]` is `P`-smooth (`P(i) ≤ P`),
`P² ∣ m`, and `P(m) = P` — so `m` is a bad singleton and `n` is a
`P`-smooth number within distance `v - u` of it. -/
theorem typeI_mem_imp_near_smooth_singleton {n : ℕ} (h : TypeICovered n) :
    ∃ u v m P : ℕ, Nat.Prime P ∧ m ∈ Finset.Icc u v ∧ n ∈ Finset.Icc u v ∧
      (∀ i ∈ Finset.Icc u v, largestPrimeFactor i ≤ P) ∧
      P ^ 2 ∣ m ∧ largestPrimeFactor m = P := by
  obtain ⟨u, v, m, _huv, hbad, hm, hdvd, hun, hnv⟩ := h
  obtain ⟨_, hP1, _⟩ := isBadInterval_iff_local.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push_neg at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  obtain ⟨_hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem_local hbad hm hdvd
  exact ⟨u, v, m, _, largestPrimeFactor_prime hprod2, hm,
    Finset.mem_Icc.mpr ⟨hun, hnv⟩,
    fun i hi => le_largestPrimeFactor_prod_local hi hprod2, hdvd, heq⟩

/-- The proximity form of the Type-I picture: a Type-I covered `n` lies
within a factor of `2` of a bad singleton `m` (concretely `m < 2n` and
`n < 2m`), because `m ∈ [u, v]`, `u ≤ n ≤ v`, and `v < 2u`. -/
theorem typeICovered_imp_near_badSingleton {n : ℕ} (h : TypeICovered n) :
    ∃ m : ℕ, 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m ∧ m < 2 * n ∧ n < 2 * m := by
  obtain ⟨u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := h
  obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton_local hbad hm hdvd
  have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u_local huv hbad
  rw [Finset.mem_Icc] at hm
  exact ⟨m, hm1, hm2, by omega, by omega⟩

/-- The distance form of the Type-I picture: a Type-I covered `n` is within
distance `v - u` of the bad singleton `m`, and `v - u < min(n, m)` (since
`v < 2u` gives `v - u < u ≤ n, m`). -/
theorem typeICovered_imp_dist_lt {n : ℕ} (h : TypeICovered n) :
    ∃ u v m : ℕ, m ∈ Finset.Icc u v ∧ 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m ∧
      n ≤ m + (v - u) ∧ m ≤ n + (v - u) ∧ v - u < n ∧ v - u < m := by
  obtain ⟨u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := h
  obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton_local hbad hm hdvd
  have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u_local huv hbad
  rw [Finset.mem_Icc] at hm
  exact ⟨u, v, m, Finset.mem_Icc.mpr hm, hm1, hm2, by omega, by omega,
    by omega, by omega⟩

/-- **Task 3 — counting bound.**  `typeICount x ≤ S(2x) · (2x + 1)`, where
`S` is `badSingletonCount`.

Proof: each Type-I covered `n ≤ x` comes with a bad singleton `m ∈ [u, v]`
(`sq_dvd_mem_isBadSingleton_local`), and `v < 2u` (the Bertrand bound) gives
`m < 2n ≤ 2x` and `|n - m| ≤ v - u < u ≤ x`, so `n ∈ Icc (m - x) (m + x)`
with `m` ranging over the bad singletons below `2x`.  Each covering interval
has at most `2x + 1` elements and `Finset.card_biUnion_le` gives the claim.

This is the strongest elementary shape available: a `√x`-radius cover would
need `v - u < P`, which badness does not imply for Type-I intervals (the
dichotomy is non-exclusive). -/
theorem typeICount_le_badSingletonCount_two_mul (x : ℕ) :
    typeICount x ≤ badSingletonCount (2 * x) * (2 * x + 1) := by
  unfold typeICount
  set S := (Finset.range (2 * x + 1)).filter
    (fun m => 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m) with hS
  -- Each counted `n` lies in `[m - x, m + x]` for a bad singleton `m < 2x`.
  have hsub : (Finset.range (x + 1)).filter (fun n => TypeICovered n)
      ⊆ S.biUnion (fun m => Finset.Icc (m - x) (m + x)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, u, v, m, huv, hbad, hm, hdvd, hun, hnv⟩ := hn
    obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton_local hbad hm hdvd
    have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u_local huv hbad
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · -- `m ∈ S`: `m < 2n ≤ 2x`, and `m` is a bad singleton.
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hm2⟩
    · -- `n ∈ [m - x, m + x]`: `m < 2n ≤ n + x` and `n ≤ x ≤ m + x`.
      rw [Finset.mem_Icc]
      omega
  -- Each covering interval has at most `2x + 1` elements.
  have hIcc_card : ∀ m : ℕ, (Finset.Icc (m - x) (m + x)).card ≤ 2 * x + 1 := by
    intro m
    rw [Nat.card_Icc]
    omega
  -- `S.card` is exactly `badSingletonCount (2 * x)`.
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

end JSP314
