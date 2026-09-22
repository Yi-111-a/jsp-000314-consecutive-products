import JSP314.Defs
import JSP314.Main
import JSP314.ShortLong
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Prod

/-!
# JSP-000314 — Assault: fresh-eyes results around the residual bound

This file collects a fresh direct attack on the analytic core
`badNonSingleton_interval_bound`.  The full bound remains the deep content of
Tao's Ta26c; what is delivered here is a collection of **fully proved**
structural and quantitative lemmas:

## The `[p² − 1, p²]` family (angle (a))

* `prod_Icc_pred`: the product over `[m − 1, m]` is `(m − 1) · m`.
* `prime_dvd_pred_sq_lt`, `largestPrimeFactor_pred_sq_lt`: for an *odd* prime
  `p`, every prime factor of `p² − 1 = (p − 1)(p + 1)` is strictly `< p`
  (prime factors of `p + 1` are `≤ (p + 1)/2 < p` since `p + 1` is even and
  composite, and `p ∤ p² − 1`).
* `isBadInterval_pred_self`: the general criterion — a bad singleton `m` whose
  predecessor has smaller largest prime factor yields the bad interval
  `[m − 1, m]`.
* `isBadInterval_pred_sq`: **`[p² − 1, p²]` is a non-singleton bad interval for
  every odd prime `p`** (e.g. `[8, 9]`, `[24, 25]`, `[48, 49]`, …).  This shows
  `N(x)` is genuinely large, not just nonzero.

## Quantitative lower bounds

* `card_primesLE_sqrt_erase_two_le` and the strengthened
  `two_mul_card_primesLE_sqrt_erase_two_le`: both endpoints of `[p² − 1, p²]`
  are covered, and the pairs `{p² − 1, p²}` are pairwise disjoint across primes
  (consecutive squares differ by `> 1`), so
  `2 · (π(√x) − 1) ≤ N(x)`, i.e. `2·π(√x) − 2 ≤ N(x)`.
* `tendsto_badNonSingletonCount_atTop`: `N(x) → ∞` along `atTop`, an honest
  strengthening of the old "eventually ≥ 2" sanity check.

## Witness uniqueness (angle (b))

* `mul_sq_near_unique`: for `p ≥ 3` and fixed `n`, **at most one** multiple of
  `p²` can lie within distance `< p` of `n` (two would differ by a multiple of
  `p²` smaller than `2p < p²`).  Hence the "number of `p`-witnesses of `n`" in
  the short-interval covering is at most the number of primes `p` such that
  `n mod p²` lands within `p` of `0` — the multiplicity per `n` is a prime
  count, not a divisor count.

## Refined short-case union bound

* `shortBadCovered_exists_singleton_near`, `shortBadCount_le_sum_sqrt`: the
  per-singleton radius is `√m`, not the global `√(2x)`, giving
  `T_short(x) ≤ ∑_{m ≤ 2x, m bad singleton} (2√m + 1)`,
  a strict sharpening of `T_short(x) ≤ S(2x) · (2√(2x) + 1)` from
  `JSP314.ShortLong` (still a union bound — documented dead end for the
  asymptotic, but the sharpest clean reformulation currently available).

This file is fully proved; no placeholders or `native_decide` are used.
-/

namespace JSP314

open Nat Filter Classical

section PredInterval

/-- The product over a two-element interval `[m − 1, m]` (`1 ≤ m`). -/
theorem prod_Icc_pred {m : ℕ} (hm : 1 ≤ m) :
    (Finset.Icc (m - 1) m).prod id = (m - 1) * m := by
  have h : Finset.Icc (m - 1) m = {m - 1, m} := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [h, Finset.prod_pair (by omega : m - 1 ≠ m)]
  rfl

/-- If `1 ≤ a`, `2 ≤ b` and `largestPrimeFactor a < largestPrimeFactor b`, then
`largestPrimeFactor (a * b) = largestPrimeFactor b`: every prime factor of the
product divides `a` (hence is `< lpf b`) or `b`. -/
theorem largestPrimeFactor_mul_eq_right {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b)
    (hlt : largestPrimeFactor a < largestPrimeFactor b) :
    largestPrimeFactor (a * b) = largestPrimeFactor b := by
  have hab : 2 ≤ a * b := by
    have h := Nat.mul_le_mul ha hb
    omega
  apply le_antisymm
  · -- `lpf (a*b)` is a prime dividing `a*b`.
    have hq := largestPrimeFactor_prime hab
    have hd := largestPrimeFactor_dvd hab
    rcases (Nat.Prime.dvd_mul hq).mp hd with ha' | hb'
    · rcases Nat.lt_or_ge a 2 with ha1 | ha2
      · -- `a = 1` has no prime divisors.
        obtain rfl : a = 1 := by omega
        exact absurd (Nat.dvd_one.mp ha') hq.ne_one
      · exact (prime_dvd_le_largestPrimeFactor ha2 hq ha').trans hlt.le
    · exact prime_dvd_le_largestPrimeFactor hb hq hb'
  · exact prime_dvd_le_largestPrimeFactor hab (largestPrimeFactor_prime hb)
      ((largestPrimeFactor_dvd hb).trans (dvd_mul_left b a))

/-- **Bad-singleton extension criterion**: if `m ≥ 2` is a bad singleton
(`P(m)² ∣ m`) and `P(m − 1) < P(m)`, then `[m − 1, m]` is a bad interval. -/
theorem isBadInterval_pred_self {m : ℕ} (hm : 2 ≤ m)
    (hsq : (largestPrimeFactor m) ^ 2 ∣ m)
    (hlt : largestPrimeFactor (m - 1) < largestPrimeFactor m) :
    IsBadInterval (m - 1) m := by
  have hprod := prod_Icc_pred (by omega : 1 ≤ m)
  show m - 1 ≤ m ∧
      largestPrimeFactor ((Finset.Icc (m - 1) m).prod id) ≠ 1 ∧
      largestPrimeFactor ((Finset.Icc (m - 1) m).prod id) ^ 2 ∣
        (Finset.Icc (m - 1) m).prod id
  rw [hprod, largestPrimeFactor_mul_eq_right (by omega : 1 ≤ m - 1) hm hlt]
  have h1 := one_lt_largestPrimeFactor hm
  exact ⟨by omega, by omega, hsq.trans (dvd_mul_left m (m - 1))⟩

/-- For an odd prime `p`, every prime factor `q` of `p² − 1 = (p−1)(p+1)` is
strictly less than `p`: if `q ∣ p − 1` then `q ≤ p − 1`; if `q ∣ p + 1` then
`q ≤ p + 1`, `q ≠ p + 1` (since `p + 1` is even and `≥ 4`, hence composite) and
`q ≠ p` (since `p ∤ p² − 1`). -/
theorem prime_dvd_pred_sq_lt {p q : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hq : Nat.Prime q) (h : q ∣ p ^ 2 - 1) : q < p := by
  have hp2 := hp.two_le
  have hne2 : p ≠ 2 := by rintro rfl; simp at hodd
  have hp3 : 3 ≤ p := by omega
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have e := Nat.sq_sub_sq p 1
    simpa using e
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · -- `q ∣ p + 1`.
    have hqle : q ≤ p + 1 := Nat.le_of_dvd (by omega) h1
    have hne : q ≠ p + 1 := by
      rintro rfl
      -- `p + 1` is prime, even, and `≥ 4`: contradiction.
      have h2dvd : (2 : ℕ) ∣ p + 1 := by omega
      have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2dvd
      omega
    have hqle' : q ≤ p := by omega
    have hnp : q ≠ p := by
      intro hqp
      rw [hqp] at h1
      have hsub : p ∣ (p + 1) - p := Nat.dvd_sub h1 (dvd_refl p)
      rw [show p + 1 - p = 1 by omega] at hsub
      exact hp.ne_one (Nat.dvd_one.mp hsub)
    omega
  · -- `q ∣ p − 1`.
    have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) h1
    omega

/-- For an odd prime `p`, `largestPrimeFactor (p² − 1) < p`. -/
theorem largestPrimeFactor_pred_sq_lt {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) :
    largestPrimeFactor (p ^ 2 - 1) < p := by
  have hp2 := hp.two_le
  have hne2 : p ≠ 2 := by rintro rfl; simp at hodd
  have hp3 : 3 ≤ p := by omega
  have h2 : 2 ≤ p ^ 2 - 1 := by
    have h := Nat.pow_le_pow_left hp3 2
    omega
  exact prime_dvd_pred_sq_lt hp hodd (largestPrimeFactor_prime h2)
    (largestPrimeFactor_dvd h2)

/-- **[p² − 1, p²] is bad for every odd prime `p`.**  The product is
`(p² − 1) · p²`; all prime factors of `p² − 1` are `< p`, so the largest prime
factor of the product is `p`, and `p²` divides it trivially. -/
theorem isBadInterval_pred_sq {p : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1) :
    IsBadInterval (p ^ 2 - 1) (p ^ 2) := by
  have hp2 : 2 ≤ p ^ 2 := by
    have h := Nat.pow_le_pow_left hp.two_le 2
    omega
  refine isBadInterval_pred_self hp2 ?_ ?_
  · rw [largestPrimeFactor_prime_sq_self hp]
  · rw [largestPrimeFactor_prime_sq_self hp]
    exact largestPrimeFactor_pred_sq_lt hp hodd

/-- The left endpoint `p² − 1` is covered by the non-singleton bad interval
`[p² − 1, p²]`. -/
theorem inNonSingletonBadInterval_pred_sq {p : ℕ} (hp : Nat.Prime p)
    (hodd : p % 2 = 1) : InNonSingletonBadInterval (p ^ 2 - 1) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
  exact ⟨p ^ 2 - 1, p ^ 2, by omega, isBadInterval_pred_sq hp hodd,
    le_refl _, Nat.sub_le _ _⟩

/-- The right endpoint `p²` is covered by the non-singleton bad interval
`[p² − 1, p²]`. -/
theorem inNonSingletonBadInterval_sq {p : ℕ} (hp : Nat.Prime p)
    (hodd : p % 2 = 1) : InNonSingletonBadInterval (p ^ 2) := by
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
  exact ⟨p ^ 2 - 1, p ^ 2, by omega, isBadInterval_pred_sq hp hodd,
    Nat.sub_le _ _, le_refl _⟩

/-- The even prime fails: `[3, 4]` is *not* bad (product `12`, `P = 3`,
`3² ∤ 12`), so the oddness hypothesis in `isBadInterval_pred_sq` is needed. -/
theorem not_isBadInterval_three_four : ¬ IsBadInterval 3 4 := by
  have hprod : (Finset.Icc 3 4).prod id = 12 := by decide
  have hlpf : largestPrimeFactor 12 = 3 := by
    have hP : Nat.Prime (largestPrimeFactor 12) :=
      largestPrimeFactor_prime (by norm_num)
    have hdvd : largestPrimeFactor 12 ∣ 12 := largestPrimeFactor_dvd (by norm_num)
    apply le_antisymm
    · have hdvd' : largestPrimeFactor 12 ∣ 4 * 3 := hdvd.trans (dvd_of_eq (by norm_num))
      rcases hP.dvd_mul.mp hdvd' with h4 | h3
      · have h : largestPrimeFactor 12 = 2 :=
          (Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).mp
            (hP.dvd_of_dvd_pow (h4.trans (dvd_of_eq (show (4 : ℕ) = 2 ^ 2 by norm_num))))
        omega
      · have h : largestPrimeFactor 12 = 3 :=
          (Nat.prime_dvd_prime_iff_eq hP Nat.prime_three).mp h3
        omega
    · exact prime_dvd_le_largestPrimeFactor (by norm_num) Nat.prime_three (by norm_num)
  rintro ⟨-, -, hP2⟩
  rw [hprod, hlpf] at hP2
  norm_num at hP2

end PredInterval

section LowerBounds

/-- Consecutive squares differ by more than `1`: `m² ≠ k² + 1` for `k ≥ 1`. -/
theorem sq_ne_sq_add_one {m k : ℕ} (hk : 1 ≤ k) : m ^ 2 ≠ k ^ 2 + 1 := by
  intro h
  have hmk : k < m := by
    by_contra hc
    push Not at hc
    have hle := Nat.pow_le_pow_left hc 2
    omega
  have h2 : (k + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hmk 2
  have h3 : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by
    rw [pow_two, pow_two, Nat.add_mul, Nat.mul_succ, one_mul]
    omega
  omega

/-- Injecting odd primes `p ≤ √x` to the covered point `p² − 1`:
`#({p ≤ √x : p prime, p ≠ 2}) ≤ N(x)`. -/
theorem card_primesLE_sqrt_erase_two_le (x : ℕ) :
    ((Nat.primesLE (Nat.sqrt x)).erase 2).card ≤ badNonSingletonCount x := by
  unfold badNonSingletonCount
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p ^ 2 - 1)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_erase, Nat.mem_primesLE] at hp
    obtain ⟨hp2, hple, hpp⟩ := hp
    have hpsq : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hpp.pos
    have hodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩)
    · show p ^ 2 - 1 < x + 1
      omega
    · exact inNonSingletonBadInterval_pred_sq hpp hodd
  · intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have ha1 : 1 ≤ a ^ 2 :=
      Nat.one_le_pow 2 a (Nat.prime_of_mem_primesLE (Finset.mem_erase.mp ha).2).pos
    have hb1 : 1 ≤ b ^ 2 :=
      Nat.one_le_pow 2 b (Nat.prime_of_mem_primesLE (Finset.mem_erase.mp hb).2).pos
    have hab' : a ^ 2 - 1 = b ^ 2 - 1 := hab
    have hsq : a ^ 2 = b ^ 2 := by omega
    exact Nat.pow_left_injective two_ne_zero hsq

/-- **Quantitative non-vacuity**: `2·(π(√x) − 1) ≤ N(x)`.

Both `p² − 1` and `p²` are covered by `[p² − 1, p²]` for each odd prime
`p ≤ √x`, and the pairs `{p² − 1, p²}` are disjoint across primes since two
squares cannot differ by `1` (`sq_ne_sq_add_one`).  Inject the product
`(odd primes ≤ √x) × {0, 1}` via `(p, i) ↦ p² − 1 + i`. -/
theorem two_mul_card_primesLE_sqrt_erase_two_le (x : ℕ) :
    2 * ((Nat.primesLE (Nat.sqrt x)).erase 2).card ≤ badNonSingletonCount x := by
  unfold badNonSingletonCount
  have h := Finset.card_le_card_of_injOn
    (fun (pi : ℕ × ℕ) => pi.1 ^ 2 - 1 + pi.2)
    (s := (Nat.primesLE (Nat.sqrt x)).erase 2 ×ˢ {0, 1})
    (t := (Finset.range (x + 1)).filter fun n => InNonSingletonBadInterval n)
    ?_ ?_
  · rw [Finset.card_product, Finset.card_pair (by norm_num : (0 : ℕ) ≠ 1)] at h
    omega
  · -- MapsTo
    rintro ⟨p, i⟩ hp
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_erase,
      Nat.mem_primesLE, Finset.mem_insert, Finset.mem_singleton] at hp
    obtain ⟨⟨hp2, hple, hpp⟩, hi⟩ := hp
    have hpsq : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hpp.pos
    have hodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    have hi1 : i ≤ 1 := by rcases hi with rfl | rfl <;> norm_num
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩)
    · show p ^ 2 - 1 + i < x + 1
      omega
    · rcases hi with rfl | rfl
      · exact inNonSingletonBadInterval_pred_sq hpp hodd
      · show InNonSingletonBadInterval (p ^ 2 - 1 + 1)
        rw [Nat.sub_add_cancel hp1]
        exact inNonSingletonBadInterval_sq hpp hodd
  · -- InjOn
    rintro ⟨a, i⟩ ha ⟨b, j⟩ hb hab
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_erase,
      Nat.mem_primesLE, Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain ⟨⟨-, -, hap⟩, hi⟩ := ha
    obtain ⟨⟨-, -, hbp⟩, hj⟩ := hb
    have ha1 : 1 ≤ a ^ 2 := Nat.one_le_pow 2 a hap.pos
    have hb1 : 1 ≤ b ^ 2 := Nat.one_le_pow 2 b hbp.pos
    have hi1 : i ≤ 1 := by rcases hi with rfl | rfl <;> norm_num
    have hj1 : j ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
    -- `hab : a² − 1 + i = b² − 1 + j`, so `a² + i = b² + j` with `i, j ≤ 1`.
    have hab' : a ^ 2 - 1 + i = b ^ 2 - 1 + j := hab
    have hA : a ^ 2 + i = b ^ 2 + j := by omega
    have habp : a = b := by
      by_contra hne
      have hsq : a ^ 2 ≠ b ^ 2 :=
        fun e => hne (Nat.pow_left_injective two_ne_zero e)
      rcases Nat.lt_or_gt_of_ne hsq with hlt | hgt
      · have e : b ^ 2 = a ^ 2 + 1 := by omega
        exact sq_ne_sq_add_one hap.pos e
      · have e : a ^ 2 = b ^ 2 + 1 := by omega
        exact sq_ne_sq_add_one hbp.pos e
    subst habp
    have hij : i = j := by omega
    subst hij
    rfl

/-- Corollary in terms of `Nat.primeCounting`:
`2·π(√x) − 2 ≤ N(x)` for all `x`. -/
theorem two_mul_primeCounting_sqrt_sub_two_le (x : ℕ) :
    2 * Nat.primeCounting (Nat.sqrt x) - 2 ≤ badNonSingletonCount x := by
  have h := two_mul_card_primesLE_sqrt_erase_two_le x
  have e := Nat.primesLE_card_eq_primeCounting (Nat.sqrt x)
  by_cases h2 : 2 ∈ Nat.primesLE (Nat.sqrt x)
  · rw [Finset.card_erase_of_mem h2] at h
    omega
  · rw [Finset.erase_eq_of_notMem h2] at h
    omega

/-- `Nat.sqrt` tends to infinity along `atTop`. -/
theorem tendsto_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun b => ⟨b ^ 2, fun n hn => Nat.le_sqrt'.mpr hn⟩

/-- **N(x) → ∞**: the non-singleton bad count diverges (at rate at least
`2·π(√x) − 2`).  Strengthens the earlier "eventually `≥ 2`" check and confirms
the residual bound compares two genuinely diverging quantities. -/
theorem tendsto_badNonSingletonCount_atTop :
    Tendsto badNonSingletonCount atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp
    (Nat.tendsto_primeCounting.comp tendsto_sqrt_atTop)) (b + 1)
  exact ⟨N, fun x hx => by
    have h1 : b + 1 ≤ Nat.primeCounting (Nat.sqrt x) := hN x hx
    have h2 := two_mul_primeCounting_sqrt_sub_two_le x
    omega⟩

end LowerBounds

section WitnessUniqueness

/-- **Witness uniqueness (per prime)**: for `p ≥ 3` and fixed `n`, at most one
multiple `p² · s` of `p²` can lie within distance `< p` of `n` — two such
multiples would differ by a positive multiple of `p²` that is `< 2p < p²`.

This is the per-`p` control behind angle (b): the multiplicity of `n` in the
short-interval covering, as a function of the witnessing prime `p`, is bounded
by the number of primes `p` for which `n mod p²` lies within `p` of `0`. -/
theorem mul_sq_near_unique {p n s t : ℕ} (hp : 3 ≤ p)
    (hs₁ : p ^ 2 * s < n + p) (hs₂ : n < p ^ 2 * s + p)
    (ht₁ : p ^ 2 * t < n + p) (ht₂ : n < p ^ 2 * t + p) :
    s = t := by
  have h2p : 2 * p < p ^ 2 := by
    have e : p * 3 ≤ p * p := Nat.mul_le_mul le_rfl hp
    have e2 : p * p = p ^ 2 := (pow_two p).symm
    omega
  have key : ∀ s t : ℕ, s < t → p ^ 2 * s < n + p → n < p ^ 2 * s + p →
      p ^ 2 * t < n + p → n < p ^ 2 * t + p → False := by
    intro s t hst hs₁ hs₂ ht₁ ht₂
    have hle : p ^ 2 * s + p ^ 2 ≤ p ^ 2 * t := by
      have hst' : s + 1 ≤ t := hst
      calc p ^ 2 * s + p ^ 2 = p ^ 2 * (s + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
        _ ≤ p ^ 2 * t := Nat.mul_le_mul le_rfl hst'
    omega
  rcases lt_trichotomy s t with h | h | h
  · exact (key s t h hs₁ hs₂ ht₁ ht₂).elim
  · exact h
  · exact (key t s h ht₁ ht₂ hs₁ hs₂).elim

end WitnessUniqueness

section RefinedShortBound

/-- Per-singleton refinement of `shortBadCovered_exists_singleton`: the covered
point `n` lies within `√m` (not just `√(2x)`) of the bad singleton `m`, since
the distance is `< P = lpf m ≤ √m`. -/
theorem shortBadCovered_exists_singleton_near {n x : ℕ} (hn : InShortBadInterval n)
    (hx : n ≤ x) :
    ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ m ≤ 2 * x ∧
      m - Nat.sqrt m ≤ n ∧ n ≤ m + Nat.sqrt m := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := hn
  obtain ⟨m, hm, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf := sq_dvd_mem_lpf_eq hbad hm hdvd
  have hbs := sq_dvd_mem_is_bad_singleton' hbad hm hdvd
  have hmv : m ≤ v := (Finset.mem_Icc.mp hm).2
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  have hsqrt : largestPrimeFactor m ≤ Nat.sqrt m :=
    lpf_le_sqrt_of_sq_dvd hbs.1 hbs.2
  obtain ⟨h1, h2⟩ := mem_Icc_cover (Finset.mem_Icc.mpr ⟨hun, hnv⟩) hm
  exact ⟨m, hbs.1, hbs.2, by omega, by omega, by omega⟩

/-- **Sharpest clean reformulation of the short case**:
`T_short(x) ≤ ∑_{m ≤ 2x, m bad singleton} (2√m + 1)`.

Strictly sharper than `shortBadCount_le` (`S(2x)·(2√(2x)+1)`) since each
singleton only covers `2√m + 1` points.  It remains a union bound — the total
is still `≈ S(2x)·√x`-sized — so it does not by itself yield the asymptotic,
but it is the faithful counting statement for the short branch. -/
theorem shortBadCount_le_sum_sqrt (x : ℕ) :
    shortBadCount x ≤
      ∑ m ∈ (Finset.range (2 * x + 1)).filter
          (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m),
        (2 * Nat.sqrt m + 1) := by
  unfold shortBadCount
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      ((Finset.range (2 * x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)).biUnion
        (fun m => Finset.Icc (m - Nat.sqrt m) (m + Nat.sqrt m)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hsh⟩ := hn
    obtain ⟨m, hm1, hmsq, hm2x, hlo, hhi⟩ :=
      shortBadCovered_exists_singleton_near hsh (Nat.lt_add_one_iff.mp hnx)
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hmsq⟩
    · rw [Finset.mem_Icc]
      exact ⟨hlo, hhi⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro m hm
  rw [Nat.card_Icc]
  have hs := Nat.sqrt_le_self m
  omega

end RefinedShortBound

end JSP314
