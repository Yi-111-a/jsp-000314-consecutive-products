import JSP314.Main
import JSP314.Squeeze
import JSP314.Type2Run
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# JSP-000314 — Assault4: the short/long split and smooth-neighbour reduction

A fresh angle on `badNonSingleton_interval_bound` (the single unproved lemma
of `JSP314.Main`), complementary to `Assault3.lean`.  Where Assault3 split by
the dichotomy "contains a `P²`-multiple vs `P ≤ v - u`", this file splits by
**interval length versus `P`**:

* `ShortBadPoint n`: `n` lies in a bad interval `[u, v]`, `u < v`, with
  `v - u < P` (short), where `P` is the largest prime factor of `∏_{i=u}^v i`.
* `LongBadPoint n`: same but `P ≤ v - u` (long).

The gains over the type-1/type-2 split are:

1. **Short intervals are automatically type-1.**  If `v - u < P`, the
   dichotomy's second branch is excluded, so a `P²`-multiple `m ∈ [u, v]`
   exists (`short_bad_interval_sq_multiple`); and `m` is the *unique*
   `P`-multiple of the interval (`short_bad_interval_unique_P_multiple` —
   two `P`-multiples differ by `≥ P`, the `two_P_multiples_imply_long`
   contrapositive).  Every other element is strictly `(P−1)`-smooth:
   `P(n) < P` (`short_bad_interval_lpf_lt`).

2. **Long intervals die by the *same* Sylvester–Schur input** — no separate
   dichotomy branch needed: `P ≤ v - u` puts the `P` consecutive integers
   `u+1,…,u+P ⊆ [u,v]` (all `> P` by the squeeze `v + 2 ≤ 2u`), all
   `P`-smooth (`longBadPoint_imp_smooth_run`).  This also kills "long
   type-1" intervals (a `P²`-multiple *and* `P ≤ v-u`), which the type
   split leaves on the type-1 side.

3. **The central points have an elementary characterization**
   (`centralCovered_iff`): `n` is the `P²`-witness of a short bad interval
   iff `n` is a bad singleton with a `P(n)`-smooth neighbour —
   `P(n-1) ≤ P(n)` or `P(n+1) ≤ P(n)`.  (If `P(n-1) ≤ P`, the product
   `(n-1)·n` has largest prime factor `P` and `P² ∣ n ∣ prod`, so `[n-1,n]`
   is short and bad; conversely any short bad interval containing `n`
   extends at least one step past `n`.)  So the "diagonal" part of `N` —
   bad singletons covered by a non-singleton bad interval — is counted by
   `nbrdSingletonCount`, an *explicit elementary predicate*.

## The proved decomposition

`badNonSingletonCount x ≤ nbrdSingletonCount x + smoothNbrCount x + longBadCount x`

unconditionally (`badNonSingletonCount_le_add`), where `SmoothNbr n` is the
pointwise relaxation "∃ bad singleton `m` with `P(n) < P(m)` and
`|n - m| < P(m)`".  Modulo the Sylvester–Schur hypothesis `SylvesterSchurRuns`
(the same known 1892 theorem used in Assault3; `TypeIIEmpty.lean` reduces it
to a finite check plus the quadratic regime `38 ≤ P`, `P+2 ≤ u`, `u+P ≤ P²`),

`badNonSingletonCount x ≤ nbrdSingletonCount x + smoothNbrCount x`

(`badNonSingletonCount_le_add_of_sylvesterSchur`), and every non-singleton
bad interval is short with a unique `P`-multiple
(`bad_interval_short_unique_of_sylvesterSchur`).  Since
`nbrdSingletonCount x ≤ badNonSingletonCount x`
(`nbrdSingletonCount_le_badNonSingletonCount`), the *central* part of the
residual is also **necessary**: the headline bound implies
`nbrdSingletonCount x ≤ (log x)^{-1+ε}·S(x)`
(`nbrdSingleton_interval_bound_of_headline`) — i.e. almost all bad
singletons must be "smooth-isolated".

## Sharp residual facts proved here

* `smoothNbr_m_lt_two_mul`: the witness of `SmoothNbr n` satisfies `m < 2n`
  (from `P² ≤ m < n + P`), so it ranges over bad singletons `≤ 2x`.
* `smoothNbr_lpf_sq_lt`: `P(n)² < 2n` — covered points are `√(2n)`-smooth.
* `smoothNbrCount_le_sum_window`: `smoothNbrCount x` is at most the sum over
  bad singletons `m ≤ 2x` of the number of strictly-`P(m)`-smooth integers
  in `(m - P(m), m + P(m))` — the exact smooth-window quantity Tao's
  analysis must bound.
* `smoothNbrCount_le`: the crude version
  `smoothNbrCount x ≤ badSingletonCount (2x) · 2√(2x)` — the window has
  `2P(m) - 1 ≤ 2√(2x)` points.  This improves the covering radius from
  `≍ x` (Assault3's `2x+1` factor) to `≍ √x`, but is still far too weak:
  `S(2x)·√x ≍ x` already saturates the trivial bound.  Beating it needs the
  smoothness constraint inside the windows — the deep `Ψ`-type input.

## Remaining gap (exact)

Modulo Sylvester–Schur, the headline estimate follows from

  `(nbrdSingletonCount x + smoothNbrCount x : ℝ) ≤ (log x)^{-1+ε} · S(x)`
  eventually  — `badNonSingleton_interval_bound_of_residual`,

and conversely the headline implies the `nbrdSingletonCount` half.  Both
summands are genuine relaxations/necessities of the problem; bounding them
is equivalent to the assertion that bad singletons are typically isolated
from `P`-smooth runs — the analytic core of Ta26c.
-/

namespace JSP314

open Classical

/-! ## Section 0: local helpers (private copies — `attempts/` files cannot
import each other) -/

/-- Zeta-reduced unfolding of `IsBadInterval`. -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- A bad interval product is at least `2` (since `P ≠ 1`). -/
private theorem bad_interval_prod_ge_two {u v : ℕ} (hbad : IsBadInterval u v) :
    2 ≤ (Finset.Icc u v).prod id := by
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  by_contra h
  push Not at h
  exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))

/-- `P(prod)` divides some member of the interval. -/
private theorem exists_mem_dvd_of_largestPrimeFactor' {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id := largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- The dichotomy (verbatim copy of `Dichotomy.lean`'s
`bad_interval_sq_multiple_or_long`). -/
private theorem sq_multiple_or_P_le_sub {u v : ℕ} (huv : u < v)
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

/-- A `P²`-multiple `m` of a bad interval has `2 ≤ m` and `P(m) = P(prod)`. -/
private theorem two_le_and_lpf_eq_of_sq_dvd_mem {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨_huv, hP1, _hP2⟩ := isBadInterval_iff'.1 hbad
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

/-- The `P²`-multiple in a bad interval is a bad singleton. -/
private theorem sq_dvd_mem_isBadSingleton {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem hbad hm hdvd
  refine ⟨by omega, ?_⟩
  rw [heq]
  exact hdvd

/-- `P(m) = P(prod)` for a `P²`-multiple `m` of a bad interval. -/
private theorem sq_dvd_mem_largestPrimeFactor_eq {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) :=
  (two_le_and_lpf_eq_of_sq_dvd_mem hbad hm hdvd).2

/-- Two points of `[u, v]` are within `v - u` of each other. -/
private theorem dist_le_of_mem_Icc {u v m n : ℕ}
    (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    n ≤ m + (v - u) ∧ m ≤ n + (v - u) := by
  rw [Finset.mem_Icc] at hm hn
  omega

/-! ## Section 1: the short/long split -/

/-- `n` is covered by a *short* non-singleton bad interval: `v - u < P`,
where `P` is the largest prime factor of the interval product. -/
def ShortBadPoint (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧
    v - u < largestPrimeFactor ((Finset.Icc u v).prod id) ∧ u ≤ n ∧ n ≤ v

/-- `n` is covered by a *long* non-singleton bad interval: `P ≤ v - u`. -/
def LongBadPoint (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u ∧ u ≤ n ∧ n ≤ v

/-- `n` is *centrally covered*: it is itself the `P²`-multiple of a short
bad interval. -/
def CentralCovered (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧
    v - u < largestPrimeFactor ((Finset.Icc u v).prod id) ∧ u ≤ n ∧ n ≤ v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ n

/-- `n` is a *smooth neighbour* of a bad singleton: some bad singleton `m`
satisfies `P(n) < P(m)` and `|n - m| < P(m)` (equivalently
`n < m + P(m)` and `m < n + P(m)`). -/
def SmoothNbr (n : ℕ) : Prop :=
  ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
    largestPrimeFactor n < largestPrimeFactor m ∧
    n < m + largestPrimeFactor m ∧ m < n + largestPrimeFactor m

/-- A bad singleton with a `P(n)`-smooth neighbour:
`P(n-1) ≤ P(n)` or `P(n+1) ≤ P(n)`.  By `centralCovered_iff` this is
exactly "the bad singleton `n` is covered by a non-singleton bad interval". -/
def NbrdSingleton (n : ℕ) : Prop :=
  1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n ∧
    (largestPrimeFactor (n - 1) ≤ largestPrimeFactor n ∨
      largestPrimeFactor (n + 1) ≤ largestPrimeFactor n)

/-- Count of `n ≤ x` covered by a short bad interval. -/
noncomputable def shortBadCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => ShortBadPoint n).card

/-- Count of `n ≤ x` covered by a long bad interval. -/
noncomputable def longBadCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => LongBadPoint n).card

/-- Count of `n ≤ x` that are smooth neighbours of a bad singleton. -/
noncomputable def smoothNbrCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => SmoothNbr n).card

/-- Count of bad singletons `n ≤ x` with a `P(n)`-smooth neighbour. -/
noncomputable def nbrdSingletonCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => NbrdSingleton n).card

/-- Every non-singleton bad interval is short or long. -/
theorem nonSingletonBadPoint_short_or_long {n : ℕ}
    (h : InNonSingletonBadInterval n) : ShortBadPoint n ∨ LongBadPoint n := by
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := h
  rcases Nat.lt_or_ge (v - u) (largestPrimeFactor ((Finset.Icc u v).prod id))
    with hlt | hge
  · exact Or.inl ⟨u, v, huv, hbad, hlt, hun, hnv⟩
  · exact Or.inr ⟨u, v, huv, hbad, hge, hun, hnv⟩

/-- `N(x) ≤ short(x) + long(x)`. -/
theorem badNonSingletonCount_le_short_add_long (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + longBadCount x := by
  unfold badNonSingletonCount shortBadCount longBadCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  rcases nonSingletonBadPoint_short_or_long hn.2 with h | h
  · exact Or.inl ⟨hn.1, h⟩
  · exact Or.inr ⟨hn.1, h⟩

/-- Short coverage implies non-singleton coverage. -/
theorem shortBadPoint_imp_inNonSingleton {n : ℕ} (h : ShortBadPoint n) :
    InNonSingletonBadInterval n := by
  obtain ⟨u, v, huv, hbad, -, hun, hnv⟩ := h
  exact ⟨u, v, huv, hbad, hun, hnv⟩

/-- Long coverage implies non-singleton coverage. -/
theorem longBadPoint_imp_inNonSingleton {n : ℕ} (h : LongBadPoint n) :
    InNonSingletonBadInterval n := by
  obtain ⟨u, v, huv, hbad, -, hun, hnv⟩ := h
  exact ⟨u, v, huv, hbad, hun, hnv⟩

theorem shortBadCount_le_badNonSingletonCount (x : ℕ) :
    shortBadCount x ≤ badNonSingletonCount x := by
  unfold shortBadCount badNonSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, shortBadPoint_imp_inNonSingleton hn.2⟩

theorem longBadCount_le_badNonSingletonCount (x : ℕ) :
    longBadCount x ≤ badNonSingletonCount x := by
  unfold longBadCount badNonSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, longBadPoint_imp_inNonSingleton hn.2⟩

/-! ## Section 2: short-interval structure -/

/-- If `P` divides two distinct elements of `[u, v]`, then `P ≤ v - u`:
the interval is long.  (`P` divides the nonzero difference `|a - b|`.) -/
theorem two_P_multiples_imply_long {u v a b : ℕ}
    (ha : a ∈ Finset.Icc u v) (hb : b ∈ Finset.Icc u v) (hab : a ≠ b)
    (hPa : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a)
    (hPb : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ b) :
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  rw [Finset.mem_Icc] at ha hb
  rcases le_total a b with hle | hle
  · rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd heq hab
    · have hle' := Nat.le_of_dvd (show 0 < b - a by omega)
        (Nat.dvd_sub hPb hPa)
      omega
  · rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd heq.symm hab
    · have hle' := Nat.le_of_dvd (show 0 < a - b by omega)
        (Nat.dvd_sub hPa hPb)
      omega

/-- A short bad interval contains a `P²`-multiple (the dichotomy's second
branch `P ≤ v - u` is excluded by shortness). -/
theorem short_bad_interval_sq_multiple {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id)) :
    ∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m :=
  (sq_multiple_or_P_le_sub huv hbad).resolve_right (not_le_of_gt hshort)

/-- **Uniqueness of the `P`-multiple in a short bad interval**: there is a
`P²`-multiple `m`, and every element of `[u, v]` divisible by `P` equals
`m`.  (Two distinct `P`-multiples would force `P ≤ v - u`.) -/
theorem short_bad_interval_unique_P_multiple {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id)) :
    ∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
        ∀ m' ∈ Finset.Icc u v,
          largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m' → m' = m := by
  obtain ⟨m, hm, hdvd⟩ := short_bad_interval_sq_multiple huv hbad hshort
  refine ⟨m, hm, hdvd, fun m' hm' hPm' => ?_⟩
  by_contra hne
  have hPm : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
    (dvd_pow_self _ two_ne_zero).trans hdvd
  have hle := two_P_multiples_imply_long hm' hm hne hPm' hPm
  omega

/-- If `[u, v]` contains a `P`-multiple `a` and the next one `a + P`, every
element strictly between them is *strictly* `P`-smooth: `P(c) < P` (it is
`P`-smooth like every interval element, and cannot be divisible by `P`). -/
theorem between_P_multiples_lpf_lt {u v a : ℕ} (hbad : IsBadInterval u v)
    (hPa : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a)
    (ha : a ∈ Finset.Icc u v)
    (haP : a + largestPrimeFactor ((Finset.Icc u v).prod id)
        ∈ Finset.Icc u v)
    {c : ℕ}
    (hc : c ∈ Finset.Icc (a + 1)
        (a + largestPrimeFactor ((Finset.Icc u v).prod id) - 1)) :
    largestPrimeFactor c <
      largestPrimeFactor ((Finset.Icc u v).prod id) := by
  have hprod2 := bad_interval_prod_ge_two hbad
  have hPp : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hc' : c ∈ Finset.Icc u v := by
    rw [Finset.mem_Icc] at haP hc ⊢
    omega
  have hle := bad_interval_forall_lpf_le hbad c hc'
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    -- `P(c) = P`, so `P ∣ c`; also `P ∣ a`, hence `P ∣ c - a` with
    -- `0 < c - a < P`, contradiction.
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with h | h
      · exfalso
        rw [largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h)] at heq
        exact hPp.ne_one heq.symm
      · exact h
    have hPc : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ c :=
      heq ▸ largestPrimeFactor_dvd hc2
    have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ c - a :=
      Nat.dvd_sub hPc hPa
    rw [Finset.mem_Icc] at hc
    have hpos : 0 < c - a := by omega
    have hge := Nat.le_of_dvd hpos hdvd
    omega
  · exact hlt

/-- In a short bad interval, every element `n` other than the `P²`-multiple
`m` satisfies `P(n) < P` (strictly `(P-1)`-smooth). -/
theorem short_bad_interval_lpf_lt {u v m n : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id))
    (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)
    (hn : n ∈ Finset.Icc u v) (hne : n ≠ m) :
    largestPrimeFactor n < largestPrimeFactor ((Finset.Icc u v).prod id) := by
  have hprod2 := bad_interval_prod_ge_two hbad
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hle := bad_interval_forall_lpf_le hbad n hn
  rcases eq_or_lt_of_le hle with heq | hlt
  · exfalso
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · exfalso
        rw [largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h)] at heq
        exact hPprime.ne_one heq.symm
      · exact h
    have hPn : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ n :=
      heq ▸ largestPrimeFactor_dvd hn2
    obtain ⟨m₀, hm₀, hdvd₀, huniq⟩ :=
      short_bad_interval_unique_P_multiple huv hbad hshort
    have hPm : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
      (dvd_pow_self _ two_ne_zero).trans hdvd
    exact hne ((huniq n hn hPn).trans (huniq m hm hPm).symm)
  · exact hlt

/-- A short bad interval has at most `P` elements. -/
theorem short_bad_interval_card_le {u v : ℕ}
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id)) :
    (Finset.Icc u v).card ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rw [Nat.card_Icc]
  omega

/-- **Pointwise Angle-A statement (unconditional).**  A point of a
non-singleton bad interval `[u, v]` either lies within distance `v - u` of
a bad singleton `m ∈ [u, v]` (the `P²`-multiple), or the interval is long. -/
theorem nonSingletonBadPoint_structure {n : ℕ}
    (h : InNonSingletonBadInterval n) :
    (∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
        m ∈ Finset.Icc u v ∧ 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
        n ≤ m + (v - u) ∧ m ≤ n + (v - u)) ∨
      LongBadPoint n := by
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := h
  rcases Nat.lt_or_ge (v - u) (largestPrimeFactor ((Finset.Icc u v).prod id))
    with hs | hl
  · left
    obtain ⟨m, hm, hdvd, -⟩ :=
      short_bad_interval_unique_P_multiple huv hbad hs
    obtain ⟨hm1, hmsq⟩ := sq_dvd_mem_isBadSingleton hbad hm hdvd
    obtain ⟨hd1, hd2⟩ := dist_le_of_mem_Icc hm (Finset.mem_Icc.mpr ⟨hun, hnv⟩)
    exact ⟨u, v, m, huv, hbad, hun, hnv, hm, hm1, hmsq, hd1, hd2⟩
  · exact Or.inr ⟨u, v, huv, hbad, hl, hun, hnv⟩

/-- **Sharpened short-case statement**: a point of a short bad interval is
either the `P²`-multiple itself (centrally covered) or a smooth neighbour
of it (`P(n) < P(m)`, `|n - m| < P(m)`). -/
theorem shortBadPoint_imp {n : ℕ} (h : ShortBadPoint n) :
    CentralCovered n ∨ SmoothNbr n := by
  obtain ⟨u, v, huv, hbad, hshort, hun, hnv⟩ := h
  obtain ⟨m, hm, hdvd, huniq⟩ :=
    short_bad_interval_unique_P_multiple huv hbad hshort
  have hnIcc : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
  obtain ⟨hm1, hmsq⟩ := sq_dvd_mem_isBadSingleton hbad hm hdvd
  have heq : largestPrimeFactor m =
      largestPrimeFactor ((Finset.Icc u v).prod id) :=
    sq_dvd_mem_largestPrimeFactor_eq hbad hm hdvd
  rcases eq_or_ne n m with rfl | hne
  · exact Or.inl ⟨u, v, huv, hbad, hshort, hun, hnv, hdvd⟩
  · right
    have hlt := short_bad_interval_lpf_lt huv hbad hshort hm hdvd hnIcc hne
    rw [← heq] at hlt hshort
    rw [Finset.mem_Icc] at hm
    exact ⟨m, hm1, hmsq, hlt, by omega, by omega⟩

/-! ## Section 3: the central-point characterization -/

/-- A centrally covered point is a bad singleton. -/
theorem centralCovered_imp_badSingleton {n : ℕ} (h : CentralCovered n) :
    1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n := by
  obtain ⟨u, v, -, hbad, -, hun, hnv, hdvd⟩ := h
  exact sq_dvd_mem_isBadSingleton hbad (Finset.mem_Icc.mpr ⟨hun, hnv⟩) hdvd

/-- A centrally covered point lies in a non-singleton bad interval. -/
theorem centralCovered_imp_inNonSingleton {n : ℕ} (h : CentralCovered n) :
    InNonSingletonBadInterval n := by
  obtain ⟨u, v, huv, hbad, -, hun, hnv, -⟩ := h
  exact ⟨u, v, huv, hbad, hun, hnv⟩

/-- **The elementary characterization of central coverage.**  `n` is the
`P²`-multiple of a short bad interval iff `n` is a bad singleton and one of
its neighbours is `P(n)`-smooth.

Forward: a short bad interval containing `n` has `u < v`, so it extends at
least one step past `n`; that neighbour lies in the interval, hence is
`P`-smooth.  Backward: if `P(n-1) ≤ P(n) =: P` (the `n+1` case is
symmetric), the product `(n-1)·n` has largest prime factor `P` — every
prime divisor is `≤ P`, and `P ∣ n ∣ prod` — and `P² ∣ n ∣ prod`, so
`[n-1, n]` is a short bad interval centred at `n`. -/
theorem centralCovered_iff {n : ℕ} :
    CentralCovered n ↔ NbrdSingleton n := by
  constructor
  · rintro ⟨u, v, huv, hbad, hshort, hun, hnv, hdvd⟩
    obtain ⟨hn1, hnsq⟩ := centralCovered_imp_badSingleton
      ⟨u, v, huv, hbad, hshort, hun, hnv, hdvd⟩
    have heq : largestPrimeFactor n =
        largestPrimeFactor ((Finset.Icc u v).prod id) :=
      sq_dvd_mem_largestPrimeFactor_eq hbad (Finset.mem_Icc.mpr ⟨hun, hnv⟩) hdvd
    refine ⟨hn1, hnsq, ?_⟩
    rcases Nat.lt_or_ge u n with h | h
    · left
      have hmem : n - 1 ∈ Finset.Icc u v :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have := bad_interval_forall_lpf_le hbad (n - 1) hmem
      omega
    · right
      have hmem : n + 1 ∈ Finset.Icc u v :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have := bad_interval_forall_lpf_le hbad (n + 1) hmem
      omega
  · rintro ⟨hn1, hnsq, hnbr⟩
    have hn2 : 2 ≤ n := hn1
    have hPprime : Nat.Prime (largestPrimeFactor n) :=
      largestPrimeFactor_prime hn2
    have hP2le : (largestPrimeFactor n) ^ 2 ≤ n :=
      Nat.le_of_dvd (by omega) hnsq
    have h4P : 4 ≤ (largestPrimeFactor n) ^ 2 :=
      Nat.pow_le_pow_left hPprime.two_le 2
    have hn4 : 4 ≤ n := h4P.trans hP2le
    rcases hnbr with h | h
    · -- `P(n-1) ≤ P(n)`: the two-element interval `[n-1, n]` is short and bad.
      have hIcc : Finset.Icc (n - 1) n = {n - 1, n} := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hprod : (Finset.Icc (n - 1) n).prod id = (n - 1) * n := by
        rw [hIcc, Finset.prod_pair (show n - 1 ≠ n by omega)]
        simp only [id_eq]
      have hprod2 : 2 ≤ (Finset.Icc (n - 1) n).prod id := by
        rw [hprod]
        have e : 3 * 4 ≤ (n - 1) * n :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have hlpf : largestPrimeFactor ((Finset.Icc (n - 1) n).prod id) =
          largestPrimeFactor n := by
        apply le_antisymm
        · have hprime : Nat.Prime
              (largestPrimeFactor ((Finset.Icc (n - 1) n).prod id)) :=
            largestPrimeFactor_prime hprod2
          have hdvdp := largestPrimeFactor_dvd hprod2
          rw [hprod] at hdvdp
          rcases hprime.dvd_mul.mp hdvdp with hd | hd
          · exact (prime_dvd_le_largestPrimeFactor (by omega) hprime hd).trans h
          · exact prime_dvd_le_largestPrimeFactor hn2 hprime hd
        · have hndvd : n ∣ (Finset.Icc (n - 1) n).prod id := by
            rw [hprod]
            exact ⟨n - 1, mul_comm (n - 1) n⟩
          exact prime_dvd_le_largestPrimeFactor hprod2 hPprime
            (dvd_trans (largestPrimeFactor_dvd hn2) hndvd)
      refine ⟨n - 1, n, by omega, ?_, ?_, by omega, le_refl n, ?_⟩
      · exact isBadInterval_iff'.mpr ⟨by omega,
          by rw [hlpf]; exact hPprime.ne_one,
          by rw [hlpf, hprod]; exact dvd_trans hnsq ⟨n - 1, mul_comm (n - 1) n⟩⟩
      · rw [hlpf]
        have := one_lt_largestPrimeFactor hn2
        omega
      · rw [hlpf]
        exact hnsq
    · -- `P(n+1) ≤ P(n)`: the two-element interval `[n, n+1]` is short and bad.
      have hIcc : Finset.Icc n (n + 1) = {n, n + 1} := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        omega
      have hprod : (Finset.Icc n (n + 1)).prod id = n * (n + 1) := by
        rw [hIcc, Finset.prod_pair (show n ≠ n + 1 by omega)]
        simp only [id_eq]
      have hprod2 : 2 ≤ (Finset.Icc n (n + 1)).prod id := by
        rw [hprod]
        have e : 4 * 5 ≤ n * (n + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have hlpf : largestPrimeFactor ((Finset.Icc n (n + 1)).prod id) =
          largestPrimeFactor n := by
        apply le_antisymm
        · have hprime : Nat.Prime
              (largestPrimeFactor ((Finset.Icc n (n + 1)).prod id)) :=
            largestPrimeFactor_prime hprod2
          have hdvdp := largestPrimeFactor_dvd hprod2
          rw [hprod] at hdvdp
          rcases hprime.dvd_mul.mp hdvdp with hd | hd
          · exact prime_dvd_le_largestPrimeFactor hn2 hprime hd
          · exact (prime_dvd_le_largestPrimeFactor (by omega) hprime hd).trans h
        · have hndvd : n ∣ (Finset.Icc n (n + 1)).prod id := by
            rw [hprod]
            exact ⟨n + 1, rfl⟩
          exact prime_dvd_le_largestPrimeFactor hprod2 hPprime
            (dvd_trans (largestPrimeFactor_dvd hn2) hndvd)
      refine ⟨n, n + 1, by omega, ?_, ?_, by omega, by omega, ?_⟩
      · exact isBadInterval_iff'.mpr ⟨by omega,
          by rw [hlpf]; exact hPprime.ne_one,
          by rw [hlpf, hprod]; exact dvd_trans hnsq ⟨n + 1, rfl⟩⟩
      · rw [hlpf]
        have := one_lt_largestPrimeFactor hn2
        omega
      · rw [hlpf]
        exact hnsq

/-- `nbrdSingletonCount` is the "diagonal" of `N`: it sits inside
`badNonSingletonCount`, so bounding it by `(log x)^{-1+ε}·S` is *necessary*
for the headline estimate. -/
theorem nbrdSingletonCount_le_badNonSingletonCount (x : ℕ) :
    nbrdSingletonCount x ≤ badNonSingletonCount x := by
  unfold nbrdSingletonCount badNonSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  obtain ⟨hnx, hb⟩ := hn
  exact ⟨hnx, centralCovered_imp_inNonSingleton (centralCovered_iff.2 hb)⟩

/-- Trivially `nbrdSingletonCount ≤ S`. -/
theorem nbrdSingletonCount_le_badSingletonCount (x : ℕ) :
    nbrdSingletonCount x ≤ badSingletonCount x := by
  unfold nbrdSingletonCount badSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.1⟩

/-- `short(x) ≤ nbrdSingleton(x) + smoothNbr(x)`. -/
theorem shortBadCount_le (x : ℕ) :
    shortBadCount x ≤ nbrdSingletonCount x + smoothNbrCount x := by
  unfold shortBadCount nbrdSingletonCount smoothNbrCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  rcases shortBadPoint_imp hn.2 with h | h
  · exact Or.inl ⟨hn.1, centralCovered_iff.1 h⟩
  · exact Or.inr ⟨hn.1, h⟩

/-- **The unconditional three-term decomposition**:
`N(x) ≤ nbrdSingleton(x) + smoothNbr(x) + long(x)`. -/
theorem badNonSingletonCount_le_add (x : ℕ) :
    badNonSingletonCount x ≤
      nbrdSingletonCount x + smoothNbrCount x + longBadCount x := by
  have h1 := badNonSingletonCount_le_short_add_long x
  have h2 := shortBadCount_le x
  omega

/-! ## Section 4: the long case and the Sylvester–Schur input -/

/-- A long bad interval (`P ≤ v - u`) contains the run `u+1, …, u+P` of `P`
consecutive integers, all `> P` (since `P ≤ v - u ≤ u - 2` by the squeeze)
and all `P`-smooth (every prime divisor divides the interval product). -/
theorem longBadPoint_imp_smooth_run {n : ℕ} (h : LongBadPoint n) :
    ∃ u P : ℕ, Nat.Prime P ∧ P + 2 ≤ u ∧
      ∀ m ∈ Finset.Icc (u + 1) (u + P), ∀ q : ℕ, Nat.Prime q → q ∣ m →
        q ≤ P := by
  obtain ⟨u, v, huv, hbad, hPle, hun, hnv⟩ := h
  have hprod2 := bad_interval_prod_ge_two hbad
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hlt : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  refine ⟨u, _, hPprime, by omega, ?_⟩
  intro m hm q hq hqm
  have hmem : m ∈ Finset.Icc u v := by
    rw [Finset.mem_Icc] at hm ⊢
    omega
  exact prime_dvd_le_largestPrimeFactor hprod2 hq
    (dvd_trans hqm (Finset.dvd_prod_of_mem id hmem))

/-- The Sylvester–Schur hypothesis in consecutive-integers form: among any
`P` consecutive integers all exceeding `P`, some element has a prime factor
`> P`.  A true 1892 theorem (Sylvester; elementary proof by Erdős); the
sibling files `attempts/aux/SylvesterSchur.lean` and
`attempts/aux/TypeIIEmpty.lean` formalize it modulo a finite check and the
quadratic regime `38 ≤ P`, `P + 2 ≤ u`, `u + P ≤ P²`.  Kept as a hypothesis
so this file stays fully proved. -/
def SylvesterSchurRuns : Prop :=
  ∀ P u : ℕ, Nat.Prime P → P < u →
    ∃ m ∈ Finset.Icc (u + 1) (u + P), ∃ q : ℕ, Nat.Prime q ∧ P < q ∧ q ∣ m

/-- Modulo Sylvester–Schur, no `n` is covered by a long bad interval: the
smooth run `u+1,…,u+P` contradicts the existence of a prime factor `> P`. -/
theorem not_longBadPoint (hss : SylvesterSchurRuns) {n : ℕ}
    (h : LongBadPoint n) : False := by
  obtain ⟨u, P, hPp, hPu, hsm⟩ := longBadPoint_imp_smooth_run h
  obtain ⟨m, hm, q, hq, hPq, hqm⟩ := hss P u hPp (by omega)
  exact absurd (hsm m hm q hq hqm) (not_le_of_gt hPq)

/-- Modulo Sylvester–Schur, `longBadCount x = 0`. -/
theorem longBadCount_eq_zero (hss : SylvesterSchurRuns) (x : ℕ) :
    longBadCount x = 0 := by
  unfold longBadCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  exact not_longBadPoint hss

/-- **Shape theorem (modulo Sylvester–Schur).**  Every non-singleton bad
interval is *short* (`v - u < P`) and contains a *unique* `P`-multiple —
necessarily its `P²`-multiple, a bad singleton.  All other elements are
strictly `(P-1)`-smooth and within distance `< P` of that singleton. -/
theorem bad_interval_short_unique_of_sylvesterSchur
    (hss : SylvesterSchurRuns) {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) :
    v - u < largestPrimeFactor ((Finset.Icc u v).prod id) ∧
      ∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
          ∀ m' ∈ Finset.Icc u v,
            largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m' → m' = m := by
  have hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id) := by
    by_contra h
    push Not at h
    exact not_longBadPoint hss ⟨u, v, huv, hbad, h, le_refl u, hbad.1⟩
  exact ⟨hshort, short_bad_interval_unique_P_multiple huv hbad hshort⟩

/-- **The conditional two-term decomposition** (modulo Sylvester–Schur):
`N(x) ≤ nbrdSingleton(x) + smoothNbr(x)`. -/
theorem badNonSingletonCount_le_add_of_sylvesterSchur
    (hss : SylvesterSchurRuns) (x : ℕ) :
    badNonSingletonCount x ≤ nbrdSingletonCount x + smoothNbrCount x := by
  have h := badNonSingletonCount_le_add x
  rw [longBadCount_eq_zero hss x] at h
  omega

/-! ## Section 5: quantitative facts about `SmoothNbr` -/

/-- The `SmoothNbr` witness is dyadically close: `m < 2n`.  Indeed
`P² ≤ m < n + P` gives `P < n` (as `2P ≤ P²`), hence `m < n + P < 2n`. -/
theorem smoothNbr_m_lt_two_mul {n m : ℕ} (hm1 : 1 < m)
    (hmsq : (largestPrimeFactor m) ^ 2 ∣ m)
    (hdist : m < n + largestPrimeFactor m) : m < 2 * n := by
  have hPp : Nat.Prime (largestPrimeFactor m) :=
    largestPrimeFactor_prime (by omega)
  have hP2 : largestPrimeFactor m * largestPrimeFactor m ≤ m := by
    rw [← pow_two]
    exact Nat.le_of_dvd (by omega) hmsq
  have h2P : 2 * largestPrimeFactor m ≤
      largestPrimeFactor m * largestPrimeFactor m :=
    Nat.mul_le_mul hPp.two_le (le_refl _)
  omega

/-- A smooth neighbour `n` is `√(2n)`-smooth: `P(n)² < 2n`.  Indeed
`P(n) + 1 ≤ P(m)`, so `P(n)² < P(m)² ≤ m < 2n`. -/
theorem smoothNbr_lpf_sq_lt {n m : ℕ} (hm1 : 1 < m)
    (hmsq : (largestPrimeFactor m) ^ 2 ∣ m)
    (hlt : largestPrimeFactor n < largestPrimeFactor m)
    (hdist : m < n + largestPrimeFactor m) :
    (largestPrimeFactor n) ^ 2 < 2 * n := by
  have h1 : largestPrimeFactor n + 1 ≤ largestPrimeFactor m := hlt
  have h2 : (largestPrimeFactor n + 1) ^ 2 ≤ (largestPrimeFactor m) ^ 2 :=
    Nat.pow_le_pow_left h1 2
  have h3 : (largestPrimeFactor m) ^ 2 ≤ m := Nat.le_of_dvd (by omega) hmsq
  have h4 : m < 2 * n := smoothNbr_m_lt_two_mul hm1 hmsq hdist
  have h5 : (largestPrimeFactor n) ^ 2 < (largestPrimeFactor n + 1) ^ 2 :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self _) two_ne_zero
  omega

/-- **The exact smooth-window bound.**  `smoothNbrCount x` is at most the
sum over bad singletons `m ≤ 2x` of the number of strictly-`P(m)`-smooth
integers within distance `< P(m)` of `m`.  This is the quantity Tao's
`Ψ`-type analysis must control. -/
theorem smoothNbrCount_le_sum_window (x : ℕ) :
    smoothNbrCount x ≤
      ∑ m ∈ (Finset.range (2 * x + 1)).filter
          (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m),
        ((Finset.Icc (m + 1 - largestPrimeFactor m)
              (m + largestPrimeFactor m - 1)).filter
          (fun j => largestPrimeFactor j < largestPrimeFactor m)).card := by
  unfold smoothNbrCount
  set S := (Finset.range (2 * x + 1)).filter
    (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m) with hS
  have hsub : (Finset.range (x + 1)).filter (fun n => SmoothNbr n)
      ⊆ S.biUnion (fun m =>
        (Finset.Icc (m + 1 - largestPrimeFactor m)
            (m + largestPrimeFactor m - 1)).filter
          (fun j => largestPrimeFactor j < largestPrimeFactor m)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, m, hm1, hmsq, hlt, hd1, hd2⟩ := hn
    have hmlt : m < 2 * n := smoothNbr_m_lt_two_mul hm1 hmsq hd2
    have hPpos : 1 ≤ largestPrimeFactor m :=
      (one_lt_largestPrimeFactor (by omega)).le
    have hPm : largestPrimeFactor m ≤ m :=
      Nat.le_of_dvd (by omega) ((dvd_pow_self _ two_ne_zero).trans hmsq)
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hmsq⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hlt⟩ <;> omega
  exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le

/-- **The crude quantitative bound**: `smoothNbrCount x ≤ S(2x)·2√(2x)`.
Each window has `2P(m) − 1 ≤ 2·P(m) ≤ 2·√m ≤ 2·√(2x)` elements.  This
improves the covering radius from `≍ x` (Assault3) to `≍ √x`, but since
`S(2x)` itself grows like `√x` the bound is still `≍ x` — no better than
the trivial bound.  The smoothness constraint inside the windows (kept in
`smoothNbrCount_le_sum_window`) is where the real saving must come from. -/
theorem smoothNbrCount_le (x : ℕ) :
    smoothNbrCount x ≤ badSingletonCount (2 * x) * (2 * Nat.sqrt (2 * x)) := by
  set S := (Finset.range (2 * x + 1)).filter
    (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m) with hS
  have hwin : ∀ m ∈ S,
      ((Finset.Icc (m + 1 - largestPrimeFactor m)
            (m + largestPrimeFactor m - 1)).filter
        (fun j => largestPrimeFactor j < largestPrimeFactor m)).card ≤
        2 * Nat.sqrt (2 * x) := by
    intro m hm
    rw [hS, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmx, hm1, hmsq⟩ := hm
    have hP2 : (largestPrimeFactor m) ^ 2 ≤ m :=
      Nat.le_of_dvd (by omega) hmsq
    have hPsq : largestPrimeFactor m ≤ Nat.sqrt m := Nat.le_sqrt'.2 hP2
    have hsqrt : Nat.sqrt m ≤ Nat.sqrt (2 * x) := Nat.sqrt_le_sqrt (by omega)
    have hPm : largestPrimeFactor m ≤ m :=
      Nat.le_of_dvd (by omega) ((dvd_pow_self _ two_ne_zero).trans hmsq)
    have hcard : ((Finset.Icc (m + 1 - largestPrimeFactor m)
          (m + largestPrimeFactor m - 1)).filter
        (fun j => largestPrimeFactor j < largestPrimeFactor m)).card ≤
        2 * largestPrimeFactor m := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Icc]
      omega
    omega
  have hScard : S.card = badSingletonCount (2 * x) := by
    rw [hS]
    rfl
  calc smoothNbrCount x
      ≤ ∑ m ∈ S,
          ((Finset.Icc (m + 1 - largestPrimeFactor m)
                (m + largestPrimeFactor m - 1)).filter
            (fun j => largestPrimeFactor j < largestPrimeFactor m)).card :=
        smoothNbrCount_le_sum_window x
    _ ≤ ∑ _m ∈ S, 2 * Nat.sqrt (2 * x) := Finset.sum_le_sum hwin
    _ = S.card * (2 * Nat.sqrt (2 * x)) := Finset.sum_const_nat fun _ _ => rfl
    _ = badSingletonCount (2 * x) * (2 * Nat.sqrt (2 * x)) := by rw [hScard]

/-! ## Section 6: reduction of the headline bound -/

/-- **Sufficient reduction (unconditional form).**  If the sum of the three
proved pieces is `≤ (log x)^{-1+ε}·S(x)` eventually, the headline bound
`badNonSingleton_interval_bound` follows. -/
theorem badNonSingleton_interval_bound_of_residual_uncond
    (hres : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (nbrdSingletonCount x : ℝ) + smoothNbrCount x + longBadCount x ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [hres ε hε] with x hx
  have h0 := badNonSingletonCount_le_add x
  have h : (badNonSingletonCount x : ℝ) ≤
      (nbrdSingletonCount x : ℝ) + smoothNbrCount x + longBadCount x := by
    exact_mod_cast h0
  linarith

/-- **Sufficient reduction (modulo Sylvester–Schur).**  If
`nbrdSingleton + smoothNbr ≤ (log x)^{-1+ε}·S` eventually, the headline
bound follows. -/
theorem badNonSingleton_interval_bound_of_residual
    (hss : SylvesterSchurRuns)
    (hres : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (nbrdSingletonCount x : ℝ) + smoothNbrCount x ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [hres ε hε] with x hx
  have h0 := badNonSingletonCount_le_add_of_sylvesterSchur hss x
  have h : (badNonSingletonCount x : ℝ) ≤
      (nbrdSingletonCount x : ℝ) + smoothNbrCount x := by
    exact_mod_cast h0
  linarith

/-- **Necessary part.**  The headline bound implies
`nbrdSingletonCount x ≤ (log x)^{-1+ε}·S(x)` eventually — i.e. almost all
bad singletons are "smooth-isolated" (no `P(n)`-smooth neighbour).  Any
counterexample-family of centrally-covered bad singletons of density
`≍ S(x)` would refute the conjectured asymptotic. -/
theorem nbrdSingleton_interval_bound_of_headline
    (hh : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (nbrdSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [hh ε hε] with x hx
  have h : (nbrdSingletonCount x : ℝ) ≤ badNonSingletonCount x := by
    exact_mod_cast nbrdSingletonCount_le_badNonSingletonCount x
  linarith

end JSP314
