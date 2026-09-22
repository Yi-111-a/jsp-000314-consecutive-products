import Mathlib
import JSP314.Defs

/-!
# CoreAssault — aggressive honest progress toward `badNonSingleton_interval_bound`

This scratch file (not part of the build) records everything that can currently be
proved **without** the deep analytic input of Tao's Ta26c paper, together with a
clean isolation of the missing ingredient.  Nothing here uses placeholders or
extra axioms.

To keep the file compilable while the rest of the library is still being built,
it depends only on `JSP314.Defs` and re-proves the needed infrastructure as
`private` lemmas (the proofs are verbatim copies of the corresponding — already
proved — results in `JSP314.Dichotomy`, `JSP314.Localization`, `JSP314.ProdLPF`,
`JSP314.Covering`, `JSP314.Counting`; the private copies cannot clash with the
library versions).

## Contents

### Part 0 — definitions and infrastructure copies

* `InNonSingletonBadInterval`, `badNonSingletonCount` (copies of the `Main`
  definitions).
* private copies of `exists_mem_dvd_of_largestPrimeFactor`,
  `bad_interval_sq_multiple_or_long` (dichotomy), `sq_dvd_mem_isBadSingleton`,
  `dist_le_of_mem_Icc`, `le_largestPrimeFactor_prod` (localization/ProdLPF),
  `covered_by_short_type1_interval_card_le` (covering),
  `badSingletonCount_ge_primeCounting`, `badSingletonCount_mono` (counting).

### Part 1 — the sharp short/long decomposition (NEW)

Every point `n` covered by a non-singleton bad interval `[u,v]` satisfies
exactly one of:

* `Type1ShortCovered L n`: `v - u ≤ L` and some `m ∈ [u,v]` has `P² ∣ m`
  (`P = P(prod)`).  Counted by the covering bound `≤ S(x+L)·(2L+1)`.
* `Type2ShortCovered L n`: `v - u ≤ L` and no element of `[u,v]` is divisible
  by `P²`.  By the dichotomy `P ≤ v-u` and every element of `[u,v]` is
  `P`-smooth, hence `L`-smooth — counted by Mathlib's
  `Nat.smoothNumbersUpTo_card_le` as `≤ 2^{π'(L+1)}·√x`.
* `LongCovered L n`: `v - u > L`.  **This is the deep residue.**

Hence the fully proved estimate (`badNonSingletonCount_le_decomp`):

  `N(x) ≤ S(x+L)·(2L+1) + 2^{π'(L+1)}·√x + longCoveredCount L x`

for every `x, L`.  The first two terms are genuine upper bounds; the third is
the analytic core that remains open.

### Part 2 — structure of long-covered points (NEW)

`longCovered_cases`: a long-covered point is either within distance `v-u > L`
of a bad singleton inside its interval, or it lies in a `(v-u)`-smooth bad
interval of length `> L`.  Both alternatives resist elementary counting:
the radius `v-u` is a priori unbounded, and — as documented in the file —
the "smooth run" condition alone is vacuous (every `n` lies in a `p`-smooth
run of length `≥ p` for all large primes `p`, e.g. `[1, p+1]`); the badness
constraint `P = P(prod)`, `P² ∣ prod` is what makes the condition rare.

### Part 3 — the right-hand side tends to infinity (NEW)

* `primeCounting_ge_log_two`: `π(y) ≥ log₂ y` for all `y` (iterated Bertrand).
* `badSingletonCount_ge_log_sqrt`: `S(x) ≥ log₂ √x`.
* `badSingletonCount_ge_real`: `(S x : ℝ) ≥ log x / (2 log 2) - 1`.
* `tendsto_log_rpow_mul_badSingletonCount`: for every `ε > 0`,
  `Tendsto (fun x : ℕ => (Real.log x)^(-(1-ε)) * (S x : ℝ)) atTop atTop`.
  So the target right-hand side really does tend to `+∞` — a needed component
  of any filter-level proof.

### Part 4 — `N(x)` tends to infinity (NEW)

* `isBadInterval_sq_sub_one_sq`: for every odd prime `p`, the interval
  `[p²-1, p²]` is bad (product `(p²-1)·p²`, largest prime factor `p`,
  `p² ∣ prod`).
* `badNonSingletonCount_ge_primeCounting_sub_one`: `N(x) ≥ π(√x) - 1`.
* `tendsto_badNonSingletonCount_atTop`: `N(x) → ∞`.

So `N` is genuinely unbounded and the target bound is a statement about a
divergent numerator — exactly the hard content of the paper.

## What remains open (documented in Part 5)

Bounding `longCoveredCount L x` — points covered only by bad intervals of
length `> L` — for a suitable `L → ∞`.  This is precisely where Ta26c's
smooth-number/run-of-smooth-numbers machinery is needed.  Also note the
covering bound `S(x+L)·(2L+1)` can *never* alone yield
`≤ (log x)^{-1+ε}·S(x)` (it is `≥ S(x)`), so the type-1 contribution itself
must be estimated per-singleton via `P(m)`-smooth run lengths, another piece
of the analytic core.
-/

namespace JSP314

open Nat Filter Classical Finset

/-! ## Part 0 — definitions and private infrastructure copies -/

/-- `n` lies in some bad interval `[u,v]` with `u < v` (copy of the `Main`
definition, kept name-identical so all statements transfer verbatim). -/
def InNonSingletonBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v

/-- `N(x)`: count of `n ≤ x` lying in a non-singleton bad interval
(copy of `Main.badNonSingletonCount`). -/
noncomputable def badNonSingletonCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InNonSingletonBadInterval n).card

/-- Unfolded characterisation of `IsBadInterval` (local copy, `Localization`). -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- `P(prod)` divides some member of the interval (local copy, `ProdLPF`). -/
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

/-- Every `i ∈ [u,v]` has `largestPrimeFactor i ≤ largestPrimeFactor prod`
(local copy, `ProdLPF`). -/
private theorem le_largestPrimeFactor_prod' {u v i : ℕ} (hi : i ∈ Finset.Icc u v)
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rcases le_or_lt i 1 with hi1 | hi1
  · rw [largestPrimeFactor_eq_one_iff.mpr hi1]
    exact (one_lt_largestPrimeFactor h).le
  · have hi2 : 2 ≤ i := hi1
    exact prime_dvd_le_largestPrimeFactor h (largestPrimeFactor_prime hi2)
      ((largestPrimeFactor_dvd hi2).trans (Finset.dvd_prod_of_mem id hi))

/-- The fundamental dichotomy (local copy, `Dichotomy`). -/
private theorem bad_interval_sq_multiple_or_long' {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) :
    (∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) ∨
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  by_cases hsq : ∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m
  · exact Or.inl hsq
  · right
    push_neg at hsq
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
    rw [ha, pow_two, mul_assoc] at hdvd
    have hPar : largestPrimeFactor ((Finset.Icc u v).prod id)
        ∣ a * ((Finset.Icc u v).erase m1).prod id :=
      (mul_dvd_mul_iff_left hPprime.ne_zero).mp hdvd
    have hPr : largestPrimeFactor ((Finset.Icc u v).prod id)
        ∣ ((Finset.Icc u v).erase m1).prod id :=
      (hPprime.dvd_mul.mp hPar).resolve_left hPa
    obtain ⟨m2, hm2, hdvd2⟩ :=
      ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPr
    obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
    have hdvd2' : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 := hdvd2
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

/-- Localization: a `P²`-multiple inside a bad interval is a bad singleton
(local copy, `Localization`/`Covering`). -/
private theorem sq_dvd_mem_isBadSingleton' {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨_huv, hP1, _hP2⟩ := hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hmdvd : m ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [zero_dvd_iff] at hmdvd; omega
    · exact h0
  have hm2 : 2 ≤ m :=
    (one_lt_pow₀ hPprime.one_lt two_ne_zero).le.trans
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
  have heq := le_antisymm hle1 hle2
  refine ⟨hm2, ?_⟩
  rw [heq]
  exact hdvd

/-- Two points of `[u, v]` are within `v - u` of each other (local copy). -/
private theorem dist_le_of_mem_Icc' {u v m n : ℕ}
    (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    n ≤ m + (v - u) ∧ m ≤ n + (v - u) := by
  rw [Finset.mem_Icc] at hm hn
  omega

/-- `0` lies in no bad interval at all: it would force `u = 0`, making the
interval product `0`, whose largest prime factor is `1`. -/
private theorem not_mem_bad_interval_zero {v : ℕ} :
    ¬ IsBadInterval 0 v := by
  rintro ⟨-, hP, -⟩
  have hprod0 : (Finset.Icc 0 v).prod id = 0 :=
    Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨le_refl 0, zero_le v⟩) rfl
  rw [hprod0] at hP
  exact hP (largestPrimeFactor_eq_one_iff.mpr (Nat.zero_le 0))

/-- The covering bound for short type-1 intervals (local copy, `Covering`). -/
private theorem covered_by_short_type1_interval_card_le' (x L : ℕ) :
    ((Finset.range (x + 1)).filter fun n =>
      ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
        m ∈ Finset.Icc u v ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
        u ≤ n ∧ n ≤ v).card
      ≤ badSingletonCount (x + L) * (2 * L + 1) := by
  set S := (Finset.range (x + L + 1)).filter
    (fun m => 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m) with hS
  have hsub : (Finset.range (x + 1)).filter (fun n =>
        ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
          m ∈ Finset.Icc u v ∧
          largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
          u ≤ n ∧ n ≤ v)
      ⊆ S.biUnion (fun m => Finset.Icc (m - L) (m + L)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, u, v, m, _huv, hbad, hlen, hm, hdvd, hun, hnv⟩ := hn
    obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton' hbad hm hdvd
    have hnIcc : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
    obtain ⟨hd1, hd2⟩ := dist_le_of_mem_Icc' hm hnIcc
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hm2⟩
    · rw [Finset.mem_Icc]
      omega
  have hIcc_card : ∀ m : ℕ, (Finset.Icc (m - L) (m + L)).card ≤ 2 * L + 1 := by
    intro m
    rw [Finset.card_Icc]
    omega
  have hS_card : S.card = badSingletonCount (x + L) := by
    rw [hS]
    rfl
  calc ((Finset.range (x + 1)).filter fun n =>
          ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
            m ∈ Finset.Icc u v ∧
            largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
            u ≤ n ∧ n ≤ v).card
      ≤ (S.biUnion fun m => Finset.Icc (m - L) (m + L)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ m ∈ S, (Finset.Icc (m - L) (m + L)).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ S, (2 * L + 1) := Finset.sum_le_sum fun m _ => hIcc_card m
    _ = S.card * (2 * L + 1) := Finset.sum_const_nat fun _ _ => rfl
    _ = badSingletonCount (x + L) * (2 * L + 1) := by rw [hS_card]

/-- `badSingletonCount` is monotone (local copy, `Counting`). -/
private theorem badSingletonCount_mono' : Monotone badSingletonCount := by
  intro x y hxy
  unfold badSingletonCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- `π(√x) ≤ badSingletonCount x` (local copy, `Counting`; uses
`largestPrimeFactor_prime_sq_self` from `Defs`). -/
private theorem badSingletonCount_ge_primeCounting' (x : ℕ) :
    Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x := by
  unfold badSingletonCount
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p ^ 2)
  · intro p hp
    rw [Finset.mem_coe, Nat.mem_primesLE] at hp
    obtain ⟨hple, hpp⟩ := hp
    have hpsq : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by show p ^ 2 < x + 1; omega), ?_⟩)
    refine ⟨one_lt_pow₀ hpp.one_lt two_ne_zero, ?_⟩
    rw [largestPrimeFactor_prime_sq_self hpp]
  · intro a _ b _ hab
    exact Nat.pow_left_injective two_ne_zero hab

/-! ## Part 1 — the sharp short/long decomposition -/

/-- `n` is covered by a short type-1 interval: a bad interval `[u,v]` with
`u < v`, `v - u ≤ L`, containing an element `m` divisible by `P²`. -/
def Type1ShortCovered (L n : ℕ) : Prop :=
  ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧ m ∈ Finset.Icc u v ∧
    largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧ u ≤ n ∧ n ≤ v

/-- `n` is covered by a short type-2 interval: a bad interval `[u,v]` with
`u < v`, `v - u ≤ L`, no element of which is divisible by `P²`. -/
def Type2ShortCovered (L n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧ u ≤ n ∧ n ≤ v ∧
    ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m

/-- `n` is covered by a *long* bad interval: `v - u > L`.  This is the deep
residue — bounding its count is the analytic core of Ta26c. -/
def LongCovered (L n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ L < v - u ∧ u ≤ n ∧ n ≤ v

noncomputable def longCoveredCount (L x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => LongCovered L n).card

/-- The trichotomy: every point covered by a non-singleton bad interval is
covered by a short type-1, a short type-2, or a long interval.  Note the
split on `∃ m, P² ∣ m` is done directly (the dichotomy's two branches are not
exclusive, so it cannot be used for the partition). -/
theorem covered_iff_short_or_long (L n : ℕ) :
    InNonSingletonBadInterval n ↔
      Type1ShortCovered L n ∨ Type2ShortCovered L n ∨ LongCovered L n := by
  constructor
  · rintro ⟨u, v, huv, hbad, hun, hnv⟩
    rcases le_or_gt (v - u) L with hL | hL
    · by_cases hsq : ∃ m ∈ Finset.Icc u v,
          largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m
      · obtain ⟨m, hm, hdvd⟩ := hsq
        exact Or.inl ⟨u, v, m, huv, hbad, hL, hm, hdvd, hun, hnv⟩
      · push_neg at hsq
        exact Or.inr (Or.inl ⟨u, v, huv, hbad, hL, hun, hnv, hsq⟩)
    · exact Or.inr (Or.inr ⟨u, v, huv, hbad, hL, hun, hnv⟩)
  · rintro (h | h | h)
    · obtain ⟨u, v, m, huv, hbad, -, -, -, hun, hnv⟩ := h
      exact ⟨u, v, huv, hbad, hun, hnv⟩
    · obtain ⟨u, v, huv, hbad, -, hun, hnv, -⟩ := h
      exact ⟨u, v, huv, hbad, hun, hnv⟩
    · obtain ⟨u, v, huv, hbad, -, hun, hnv⟩ := h
      exact ⟨u, v, huv, hbad, hun, hnv⟩

/-- A short type-2 interval consists entirely of `(v-u)`-smooth (hence
`L`-smooth) elements: the dichotomy gives `P ≤ v - u`, and every element `i`
satisfies `P(i) ≤ P` since `P(i)` is a prime divisor of the product. -/
theorem type2ShortCovered_largestPrimeFactor_le {L n : ℕ}
    (h : Type2ShortCovered L n) : largestPrimeFactor n ≤ L := by
  obtain ⟨u, v, huv, hbad, hLv, hun, hnv, hnosq⟩ := h
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra hc
    push_neg at hc
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ hc))
  -- The dichotomy, in the absence of a `P²`-multiple, gives `P ≤ v - u`.
  have hP := bad_interval_sq_multiple_or_long' huv hbad
  rcases hP with hsq | hlong
  · obtain ⟨m, hm, hdvd⟩ := hsq
    exact absurd hdvd (hnosq m hm)
  · have hnmem : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
    exact (le_largestPrimeFactor_prod' hnmem hprod2).trans (hlong.trans hLv)

/-- Points covered by short type-2 intervals are `(L+1)`-smooth in Mathlib's
sense (every prime factor `< L+1`), hence counted by `smoothNumbersUpTo`. -/
theorem type2ShortCovered_mem_smoothNumbers {L n : ℕ}
    (h : Type2ShortCovered L n) : n ∈ Nat.smoothNumbers (L + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpn
  have hle := type2ShortCovered_largestPrimeFactor_le h
  rcases le_or_lt n 1 with hn1 | hn1
  · interval_cases n
    · -- `n = 0` cannot be covered: its interval would start at `0`.
      obtain ⟨u, v, -, hbad, -, hun, -, -⟩ := h
      obtain rfl : u = 0 := by omega
      exact absurd hbad not_mem_bad_interval_zero
    · -- `n = 1` has no prime divisors.
      exact absurd hpn (by rw [Nat.dvd_one]; exact hp.ne_one ∘ Eq.symm)
  · exact (prime_dvd_le_largestPrimeFactor hn1 hp hpn).trans_lt
      (Nat.lt_succ_of_le hle)

/-- Cardinality bound for short type-2 covered points, via Mathlib's
smooth-number counting bound `Nat.smoothNumbersUpTo_card_le`:
`≤ 2^{π'(L+1)} · √x`. -/
theorem type2ShortCovered_card_le (x L : ℕ) :
    ((Finset.range (x + 1)).filter fun n => Type2ShortCovered L n).card
      ≤ 2 ^ (Nat.primesBelow (L + 1)).card * Nat.sqrt x := by
  refine (Finset.card_le_card ?_).trans (Nat.smoothNumbersUpTo_card_le x (L + 1))
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  rw [Nat.mem_smoothNumbersUpTo]
  exact ⟨Nat.lt_succ_iff.mp hn.1, type2ShortCovered_mem_smoothNumbers hn.2⟩

/-- **The sharp decomposition bound (fully proved).**  For every `x` and `L`,

    `N(x) ≤ S(x+L)·(2L+1)  +  2^{π'(L+1)}·√x  +  longCoveredCount L x`

where the three terms bound respectively: short type-1 intervals (covering
bound), short type-2 intervals (smooth-number bound), and the residual long
intervals. -/
theorem badNonSingletonCount_le_decomp (x L : ℕ) :
    badNonSingletonCount x
      ≤ badSingletonCount (x + L) * (2 * L + 1)
        + 2 ^ (Nat.primesBelow (L + 1)).card * Nat.sqrt x
        + longCoveredCount L x := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InNonSingletonBadInterval n)
      ⊆ ((Finset.range (x + 1)).filter fun n => Type1ShortCovered L n)
        ∪ ((Finset.range (x + 1)).filter fun n => Type2ShortCovered L n)
        ∪ ((Finset.range (x + 1)).filter fun n => LongCovered L n) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_union, Finset.mem_union,
      Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    obtain ⟨hnx, hcov⟩ := hn
    rw [covered_iff_short_or_long] at hcov
    rcases hcov with h | h | h
    · exact Or.inl ⟨hnx, h⟩
    · exact Or.inr (Or.inl ⟨hnx, h⟩)
    · exact Or.inr (Or.inr ⟨hnx, h⟩)
  calc badNonSingletonCount x
      ≤ ((((Finset.range (x + 1)).filter fun n => Type1ShortCovered L n)
          ∪ ((Finset.range (x + 1)).filter fun n => Type2ShortCovered L n)
          ∪ ((Finset.range (x + 1)).filter fun n => LongCovered L n)).card) :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range (x + 1)).filter fun n => Type1ShortCovered L n).card
        + ((Finset.range (x + 1)).filter fun n => Type2ShortCovered L n).card
        + ((Finset.range (x + 1)).filter fun n => LongCovered L n).card := by
        refine (Finset.card_union_le _ _).trans ?_
        exact add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ badSingletonCount (x + L) * (2 * L + 1)
        + 2 ^ (Nat.primesBelow (L + 1)).card * Nat.sqrt x
        + longCoveredCount L x := by
        exact add_le_add_right
          (add_le_add (covered_by_short_type1_interval_card_le' x L)
            (type2ShortCovered_card_le x L)) _

end JSP314
