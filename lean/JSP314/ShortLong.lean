import JSP314.Defs
import JSP314.Bounds
import JSP314.Squeeze
import JSP314.Type2Run
import JSP314.Main
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

/-!
# JSP-000314 — short/long decomposition of non-singleton bad intervals

Every non-singleton bad interval `[u, v]` (with product `prod` and largest
prime factor `P = largestPrimeFactor prod`) falls into exactly one of two
regimes:

* **short**: `v - u < P` — then the interval contains a `P²`-multiple `m`
  (contrapositive of `bad_interval_largestPrimeFactor_le_sub`), `m` is a bad
  singleton with `largestPrimeFactor m = P`, and every covered point lies
  within `< P ≤ √m` of `m`.  Union over bad singletons gives
  `shortBadCount x ≤ badSingletonCount (2x) · (2√(2x) + 1)`.
* **long**: `P ≤ v - u` — then every element of `[u, v]` is `P`-smooth, so
  the interval is a "smooth run" of `v - u + 1` consecutive
  `(v - u)`-smooth integers, and Mathlib's squareful-kernel bound gives
  `v + 1 - u ≤ 2 ^ π'(v - u + 1) · √v`.

The residual analytic content of Ta26c (`badNonSingleton_interval_bound` in
`JSP314.Main`) is thereby reduced to bounding `shortBadCount` and
`smoothRunCoveredCount` by `(log x)^{-1+ε} · S(x)`.
-/

namespace JSP314

open Classical

section Basics

/-- In a bad interval the product is at least `2`. -/
theorem bad_interval_prod_ge_two {u v : ℕ} (hbad : IsBadInterval u v) :
    2 ≤ (Finset.Icc u v).prod id := by
  rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
  · exact absurd
      (largestPrimeFactor_eq_one_iff.mpr
        (show (Finset.Icc u v).prod id ≤ 1 by omega))
      hbad.2.1
  · exact h

/-- In a bad interval, the largest prime factor of the product is prime. -/
theorem bad_interval_P_prime {u v : ℕ} (hbad : IsBadInterval u v) :
    Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
  largestPrimeFactor_prime (bad_interval_prod_ge_two hbad)

/-- A bad interval starts at `u ≥ 1`: otherwise `0 ∈ [u, v]` and the product
vanishes, contradicting `P ≠ 1`. -/
theorem bad_interval_one_le_left {u v : ℕ} (hbad : IsBadInterval u v) :
    1 ≤ u := by
  by_contra hc
  push Not at hc
  have h0mem : (0 : ℕ) ∈ Finset.Icc u v :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h0 : (Finset.Icc u v).prod id = 0 := Finset.prod_eq_zero h0mem rfl
  have h2 := bad_interval_prod_ge_two hbad
  omega

/-- Every element of a bad interval is positive. -/
theorem bad_interval_mem_pos {u v i : ℕ} (hbad : IsBadInterval u v)
    (hi : i ∈ Finset.Icc u v) : 1 ≤ i :=
  le_trans (bad_interval_one_le_left hbad) (Finset.mem_Icc.mp hi).1

/-- The right endpoint of a non-singleton bad interval covering `n` is at most
`2n` (the dyadic squeeze `v + 2 ≤ 2u` with `u ≤ n`). -/
theorem bad_interval_v_le_two_mul {u v n : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hun : u ≤ n) (_hnv : n ≤ v) : v ≤ 2 * n := by
  have hs := bad_interval_v_add_two_le hbad huv
  have hu1 := bad_interval_one_le_left hbad
  omega

end Basics

section SqDvd

/-- An element of a bad interval divisible by `P²` is at least `4`. -/
theorem sq_dvd_mem_ge {u v m : ℕ} (hbad : IsBadInterval u v)
    (hm : m ∈ Finset.Icc u v)
    (hdvd : (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m) :
    4 ≤ m := by
  obtain ⟨k, hk⟩ := hdvd
  have hP2 : (2 : ℕ) ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    (bad_interval_P_prime hbad).two_le
  have hk0 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, mul_zero] at hk
      have := bad_interval_mem_pos hbad hm
      omega
    · exact h0
  have e := Nat.mul_le_mul (Nat.pow_le_pow_left hP2 2) hk0
  have h4 : (4 : ℕ) ≤ (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 * k := by
    calc (4 : ℕ) = (2 : ℕ) ^ 2 * 1 := by norm_num
      _ ≤ _ := e
  omega

/-- A `P²`-multiple in a bad interval has largest prime factor exactly `P`. -/
theorem sq_dvd_mem_lpf_eq {u v m : ℕ} (hbad : IsBadInterval u v)
    (hm : m ∈ Finset.Icc u v)
    (hdvd : (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m) :
    largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  have hm2 : 2 ≤ m := le_trans (by norm_num) (sq_dvd_mem_ge hbad hm hdvd)
  refine le_antisymm (bad_interval_forall_lpf_le hbad m hm) ?_
  exact prime_dvd_le_largestPrimeFactor hm2 (bad_interval_P_prime hbad)
    ((dvd_pow_self _ two_ne_zero).trans hdvd)

/-- A `P²`-multiple in a bad interval is a bad singleton. -/
theorem sq_dvd_mem_is_bad_singleton' {u v m : ℕ} (hbad : IsBadInterval u v)
    (hm : m ∈ Finset.Icc u v)
    (hdvd : (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m) :
    1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m := by
  have hm4 := sq_dvd_mem_ge hbad hm hdvd
  have hP := sq_dvd_mem_lpf_eq hbad hm hdvd
  refine ⟨by omega, ?_⟩
  rw [hP]
  exact hdvd

/-- A short bad interval (`v - u < P`) contains a `P²`-multiple. -/
theorem bad_interval_sq_multiple_of_short {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id)) :
    ∃ m ∈ Finset.Icc u v,
      (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m := by
  by_contra h
  push Not at h
  have := bad_interval_largestPrimeFactor_le_sub hbad huv h
  omega

/-- Two points of `[u, v]` cover each other within `v - u`. -/
theorem mem_Icc_cover {u v n m : ℕ} (hn : n ∈ Finset.Icc u v)
    (hm : m ∈ Finset.Icc u v) : n ≤ m + (v - u) ∧ m ≤ n + (v - u) := by
  have h1 := Finset.mem_Icc.mp hn
  have h2 := Finset.mem_Icc.mp hm
  omega

/-- In a short bad interval, every covered point `n` lies strictly within `P`
of any `P²`-multiple `m` of the interval. -/
theorem short_bad_interval_cover {u v n m : ℕ}
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id))
    (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    n < m + largestPrimeFactor ((Finset.Icc u v).prod id) ∧
      m < n + largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨h1, h2⟩ := mem_Icc_cover hn hm
  omega

/-- If `(lpf m)² ∣ m` (and `m > 1`) then `lpf m ≤ √m`. -/
theorem lpf_le_sqrt_of_sq_dvd {m : ℕ} (hm : 1 < m)
    (hdvd : (largestPrimeFactor m) ^ 2 ∣ m) :
    largestPrimeFactor m ≤ Nat.sqrt m := by
  have hle : largestPrimeFactor m * largestPrimeFactor m ≤ m := by
    have h := Nat.le_of_dvd (show 0 < m by omega) hdvd
    rwa [pow_two] at h
  exact Nat.le_sqrt.mpr hle

end SqDvd

section SmoothRun

/-- `largestPrimeFactor` is always at least `1`. -/
theorem largestPrimeFactor_pos (i : ℕ) : 1 ≤ largestPrimeFactor i := by
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  · rw [largestPrimeFactor_eq_one_iff.mpr (show i ≤ 1 by omega)]
  · exact (one_lt_largestPrimeFactor hi2).le

/-- For `i ≥ 1` and `k ≥ 1`, `lpf i ≤ k` iff every prime divisor of `i` is
`≤ k`. -/
theorem lpf_le_iff_forall_prime_dvd_le {i k : ℕ} (hi : 1 ≤ i) (hk : 1 ≤ k) :
    largestPrimeFactor i ≤ k ↔ ∀ p : ℕ, p.Prime → p ∣ i → p ≤ k := by
  constructor
  · intro h p hp hpi
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · have h1 : i = 1 := by omega
      subst h1
      exfalso
      have h2 := hp.two_le
      have h3 := Nat.dvd_one.mp hpi
      omega
    · exact (prime_dvd_le_largestPrimeFactor hi2 hp hpi).trans h
  · intro h
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · have h1 : i = 1 := by omega
      subst h1
      rw [largestPrimeFactor_eq_one_iff.mpr (le_refl 1)]
      exact hk
    · exact h _ (largestPrimeFactor_prime hi2) (largestPrimeFactor_dvd hi2)

/-- An integer `i ≥ 1` with `lpf i ≤ k` is `(k+1)`-smooth in Mathlib's
(strict) sense. -/
theorem mem_smoothNumbers_of_lpf_le {i k : ℕ} (hi : 1 ≤ i)
    (h : largestPrimeFactor i ≤ k) : i ∈ Nat.smoothNumbers (k + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpi
  have hk : 1 ≤ k := le_trans (largestPrimeFactor_pos i) h
  have hle := (lpf_le_iff_forall_prime_dvd_le hi hk).mp h p hp hpi
  omega

/-- A "smooth run": a non-degenerate interval `[u, v]` all of whose elements
have largest prime factor at most `v - u`. -/
def IsSmoothRun (u v : ℕ) : Prop :=
  u < v ∧ ∀ i ∈ Finset.Icc u v, largestPrimeFactor i ≤ v - u

/-- A *long* bad interval (`P ≤ v - u`) is a smooth run. -/
theorem bad_interval_isSmoothRun_of_long {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hlong : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u) :
    IsSmoothRun u v := by
  refine ⟨huv, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  · rw [largestPrimeFactor_eq_one_iff.mpr (show i ≤ 1 by omega)]
    omega
  · exact (bad_interval_forall_lpf_le hbad i hi).trans hlong

/-- Every element of a smooth run `[u, v]` lies in
`Nat.smoothNumbersUpTo v (v - u + 1)`. -/
theorem smoothRun_Icc_subset_smoothNumbersUpTo {u v : ℕ} (hu : 1 ≤ u)
    (h : IsSmoothRun u v) :
    Finset.Icc u v ⊆ Nat.smoothNumbersUpTo v (v - u + 1) := by
  intro i hi
  rw [Nat.mem_smoothNumbersUpTo]
  have hiI := Finset.mem_Icc.mp hi
  exact ⟨hiI.2, mem_smoothNumbers_of_lpf_le (le_trans hu hiI.1) (h.2 i hi)⟩

/-- **Smooth-run length bound**: a smooth run `[u, v]` starting at `u ≥ 1`
satisfies `v + 1 - u ≤ 2 ^ π'(v - u + 1) · √v`. -/
theorem smoothRun_length_le {u v : ℕ} (hu : 1 ≤ u) (h : IsSmoothRun u v) :
    v + 1 - u ≤ 2 ^ Nat.primeCounting' (v - u + 1) * Nat.sqrt v := by
  have hcard := Finset.card_le_card (smoothRun_Icc_subset_smoothNumbersUpTo hu h)
  rw [Nat.card_Icc] at hcard
  have hbound := Nat.smoothNumbersUpTo_card_le v (v - u + 1)
  rw [Nat.primesBelow_card_eq_primeCounting'] at hbound
  exact hcard.trans hbound

/-- Variant with the right endpoint bounded by `B`. -/
theorem smoothRun_length_le_of_le {u v B : ℕ} (hu : 1 ≤ u)
    (h : IsSmoothRun u v) (hv : v ≤ B) :
    v + 1 - u ≤ 2 ^ Nat.primeCounting' (v - u + 1) * Nat.sqrt B :=
  (smoothRun_length_le hu h).trans
    (Nat.mul_le_mul le_rfl (Nat.sqrt_le_sqrt hv))

end SmoothRun

section Counts

/-- `n` is covered by a *short* non-singleton bad interval (`v - u < P`). -/
def InShortBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
    v - u < largestPrimeFactor ((Finset.Icc u v).prod id)

/-- `n` is covered by a *long* non-singleton bad interval (`P ≤ v - u`). -/
def InLongBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u

/-- `n` is covered by a smooth run whose right endpoint is at most `2n`. -/
def smoothRunCovered (n : ℕ) : Prop :=
  ∃ u v : ℕ, IsSmoothRun u v ∧ u ≤ n ∧ n ≤ v ∧ v ≤ 2 * n

/-- Count of `n ≤ x` covered by a short bad interval. -/
noncomputable def shortBadCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InShortBadInterval n).card

/-- Count of `n ≤ x` covered by a bounded smooth run. -/
noncomputable def smoothRunCoveredCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => smoothRunCovered n).card

/-- Pointwise dichotomy: a point covered by a non-singleton bad interval is
covered by a short one or by a long one. -/
theorem inNonSingletonBadInterval_iff_short_or_long {n : ℕ} :
    InNonSingletonBadInterval n ↔
      InShortBadInterval n ∨ InLongBadInterval n := by
  constructor
  · rintro ⟨u, v, huv, hbad, hun, hnv⟩
    rcases Nat.lt_or_ge (v - u)
        (largestPrimeFactor ((Finset.Icc u v).prod id)) with h | h
    · exact Or.inl ⟨u, v, huv, hbad, hun, hnv, h⟩
    · exact Or.inr ⟨u, v, huv, hbad, hun, hnv, h⟩
  · rintro (⟨u, v, huv, hbad, hun, hnv, -⟩ | ⟨u, v, huv, hbad, hun, hnv, -⟩)
    · exact ⟨u, v, huv, hbad, hun, hnv⟩
    · exact ⟨u, v, huv, hbad, hun, hnv⟩

/-- A point covered by a long bad interval is covered by a bounded smooth
run. -/
theorem inLongBadInterval_smoothRunCovered {n : ℕ} (h : InLongBadInterval n) :
    smoothRunCovered n := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hlong⟩ := h
  exact ⟨u, v, bad_interval_isSmoothRun_of_long hbad huv hlong, hun, hnv,
    bad_interval_v_le_two_mul hbad huv hun hnv⟩

/-- **Decomposition bound**: `N(x) ≤ T_short(x) + T_run(x)`. -/
theorem badNonSingletonCount_le_short_add_smooth (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + smoothRunCoveredCount x := by
  unfold badNonSingletonCount shortBadCount smoothRunCoveredCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, hnbad⟩ := hn
  rcases inNonSingletonBadInterval_iff_short_or_long.mp hnbad with h | h
  · exact Or.inl ⟨hnx, h⟩
  · exact Or.inr ⟨hnx, inLongBadInterval_smoothRunCovered h⟩

/-- A short-covered point `n ≤ x` lies within `√(2x)` of a bad singleton
`m ≤ 2x`. -/
theorem shortBadCovered_exists_singleton {n x : ℕ} (hn : InShortBadInterval n)
    (hx : n ≤ x) :
    ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ m ≤ 2 * x ∧
      n ≤ m + Nat.sqrt (2 * x) ∧ m ≤ n + Nat.sqrt (2 * x) := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := hn
  obtain ⟨m, hm, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf := sq_dvd_mem_lpf_eq hbad hm hdvd
  have hbs := sq_dvd_mem_is_bad_singleton' hbad hm hdvd
  have hmv : m ≤ v := (Finset.mem_Icc.mp hm).2
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  have hm2x : m ≤ 2 * x := by omega
  have hsqrt1 : largestPrimeFactor m ≤ Nat.sqrt m :=
    lpf_le_sqrt_of_sq_dvd hbs.1 hbs.2
  have hsqrt2 : Nat.sqrt m ≤ Nat.sqrt (2 * x) := Nat.sqrt_le_sqrt hm2x
  have hR : v - u ≤ Nat.sqrt (2 * x) := by omega
  obtain ⟨h1, h2⟩ := mem_Icc_cover (Finset.mem_Icc.mpr ⟨hun, hnv⟩) hm
  exact ⟨m, hbs.1, hbs.2, hm2x, by omega, by omega⟩

/-- **Short-interval covering bound**:
`T_short(x) ≤ S(2x) · (2√(2x) + 1)`. -/
theorem shortBadCount_le (x : ℕ) :
    shortBadCount x ≤
      badSingletonCount (2 * x) * (2 * Nat.sqrt (2 * x) + 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      ((Finset.range (2 * x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)).biUnion
        (fun m => Finset.Icc (m - Nat.sqrt (2 * x)) (m + Nat.sqrt (2 * x))) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hsh⟩ := hn
    obtain ⟨m, hm1, hmsq, hm2x, hnR, hmR⟩ :=
      shortBadCovered_exists_singleton hsh (Nat.lt_add_one_iff.mp hnx)
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hmsq⟩
    · rw [Finset.mem_Icc]
      exact ⟨by omega, by omega⟩
  have hcard : (((Finset.range (2 * x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)).biUnion
        (fun m => Finset.Icc (m - Nat.sqrt (2 * x)) (m + Nat.sqrt (2 * x)))).card ≤
      ((Finset.range (2 * x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)).card *
        (2 * Nat.sqrt (2 * x) + 1) :=
    Finset.card_biUnion_le_card_mul _ _ _
      (fun m _ => by rw [Nat.card_Icc]; omega)
  unfold shortBadCount badSingletonCount
  exact (Finset.card_le_card hsub).trans hcard

/-- The **Sylvester–Schur property** at `(a, L)`: some element of the `L`
consecutive integers `[a, a + L - 1]` is divisible by a prime `> L`.

This is a classical theorem (Sylvester 1892, Schur 1929, Erdős 1934): the
product of `L` consecutive integers all exceeding `L` has a prime factor
exceeding `L`.  It is **not** currently in Mathlib; it is stated here as the
precise hypothesis under which the *long* case of the dichotomy collapses. -/
def SylvesterSchur (a L : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ L < p ∧
    ∃ i ∈ Finset.Icc a (a + L - 1), p ∣ i

/-- **Conditional elimination of the long case**: under Sylvester–Schur,
every non-singleton bad interval is *short* (`v - u < P`).

The squeeze bound `v + 2 ≤ 2u` says exactly `L < u` and `v ≥ 2L` for the
length `L = v - u + 1` — the exact Sylvester–Schur threshold.  A prime
`p > L` dividing the interval product forces `P ≥ p > v - u`. -/
theorem bad_interval_short_of_sylvesterSchur {u v : ℕ}
    (hss : ∀ a L : ℕ, L < a → SylvesterSchur a L)
    (hbad : IsBadInterval u v) (huv : u < v) :
    v - u < largestPrimeFactor ((Finset.Icc u v).prod id) := by
  have hL : v - u + 1 < u := by
    have hs := bad_interval_v_add_two_le hbad huv
    omega
  obtain ⟨p, hp, hpL, i, hi, hpi⟩ := hss u (v - u + 1) hL
  have hiv : i ∈ Finset.Icc u v := by
    have hmem := Finset.mem_Icc.mp hi
    refine Finset.mem_Icc.mpr ⟨hmem.1, ?_⟩
    have : u + (v - u + 1) - 1 = v := by omega
    omega
  have hprod : p ∣ (Finset.Icc u v).prod id :=
    dvd_trans hpi (Finset.dvd_prod_of_mem id hiv)
  have hple : p ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor (bad_interval_prod_ge_two hbad) hp hprod
  omega

/-- Under Sylvester–Schur, no point is covered by a long bad interval. -/
theorem not_inLongBadInterval_of_sylvesterSchur
    (hss : ∀ a L : ℕ, L < a → SylvesterSchur a L) {n : ℕ} :
    ¬ InLongBadInterval n := by
  rintro ⟨u, v, huv, hbad, hun, hnv, hlong⟩
  have := bad_interval_short_of_sylvesterSchur hss hbad huv
  omega

/-- Under Sylvester–Schur, the non-singleton bad count is bounded by the
short component alone: `N(x) ≤ T_short(x)`. -/
theorem badNonSingletonCount_le_short_of_sylvesterSchur
    (hss : ∀ a L : ℕ, L < a → SylvesterSchur a L) (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x := by
  unfold badNonSingletonCount shortBadCount
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  obtain ⟨hnx, hnbad⟩ := hn
  refine ⟨hnx, ?_⟩
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := hnbad
  exact ⟨u, v, huv, hbad, hun, hnv,
    bad_interval_short_of_sylvesterSchur hss hbad huv⟩

/-- **Master conditional reduction**: the Sylvester–Schur theorem plus the
short-interval estimate `T_short(x) ≤ (log x)^{-1+ε} · S(x)` imply the
residual analytic bound `badNonSingleton_interval_bound`. -/
theorem badNonSingleton_interval_bound_of_sylvesterSchur_short
    (hss : ∀ a L : ℕ, L < a → SylvesterSchur a L)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (shortBadCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [h ε hε] with x hx
  have hN : (badNonSingletonCount x : ℝ) ≤ (shortBadCount x : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_short_of_sylvesterSchur hss x
  linarith

/-- The residual analytic bound of Ta26c follows from the same bound on the
two components: if `T_short(x) + T_run(x) ≤ (log x)^{-1+ε} · S(x)`
eventually for every `ε > 0`, then `N(x) ≤ (log x)^{-1+ε} · S(x)`
eventually, via `badNonSingletonCount_le_short_add_smooth`. -/
theorem badNonSingleton_interval_bound_of_components
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (shortBadCount x : ℝ) + (smoothRunCoveredCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [h ε hε] with x hx
  have hN : (badNonSingletonCount x : ℝ) ≤
      (shortBadCount x : ℝ) + (smoothRunCoveredCount x : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_short_add_smooth x
  linarith

end Counts

end JSP314
