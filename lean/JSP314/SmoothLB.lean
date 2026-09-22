import JSP314.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# A stronger lower bound for `badSingletonCount`: `x^{83/100}/(log x)^5`

We prove that `S(x) = badSingletonCount x`, the number of `n ≤ x` with
`1 < n` and `P(n)² ∣ n`, satisfies the eventual lower bound

  `S(x) ≥ (1/32768) · x^{83/100} / (log x)^5`,

improving the `x^{2/3}/log x` bound of `SingletonLB.lean`.

## Proof outline

Consider `n = p²·q₁·q₂·q₃·q₄`, where `p` is a prime in `(P0, 2P0]` with
`P0 ≈ x^{17/100}` and each `qᵢ` is a prime in the disjoint dyadic shell
`(2^{i-1}Q0, 2^iQ0]` with `Q0 ≈ x^{33/200}`.

* Since `qᵢ ≤ 16·Q0 ≤ P0 < p`, the largest prime factor of `n` is `p`,
  so `p² ∣ n` and `n` is a bad singleton.
* `n ≤ (2P0)²·(2Q0)(4Q0)(8Q0)(16Q0) ≤ x` eventually (the product is
  `≤ t^{200}/4 = x/4` for `t = x^{1/200}`).
* The tuple map is injective: `p = P(n)`, and the `qᵢ` are recovered by
  repeatedly taking the least prime factor (`Nat.minFac`), because the
  disjoint shells force `q₁ < q₂ < q₃ < q₄`.
* Each shell contributes `≥ shell/(8·log shell)` primes
  (`eventually_dyadicPrimes_card_ge`), giving
  `S(x) ≥ t^{166}/(26136·(log x)^5) = x^{83/100}/(26136·(log x)^5)`.

The dyadic-prime Chebyshev bound is restated inside the `SmoothLB` namespace
so that this file is self-contained.
-/

namespace JSP314

namespace SmoothLB

open Finset Filter

/-- The primes in the dyadic interval `(n, 2n]`. -/
def dyadicPrimes (n : ℕ) : Finset ℕ := (Nat.primesLE (2 * n)).filter fun p => n < p

theorem mem_dyadicPrimes {n p : ℕ} :
    p ∈ dyadicPrimes n ↔ p.Prime ∧ n < p ∧ p ≤ 2 * n := by
  simp only [dyadicPrimes, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, h3, h1⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h3, h1⟩, h2⟩

/-!
### The central binomial coefficient bound

`C(2n,n) ≤ (2n)^{Δ(n)} · (2n)^{√(2n)} · 4^{2n/3}` where `Δ(n)` is the number of
primes in `(n, 2n]`.
-/

theorem centralBinom_le_dyadic (n : ℕ) (hn : 2 < n) :
    Nat.centralBinom n ≤
      (2 * n) ^ (dyadicPrimes n).card *
        ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) := by
  have h2n0 : 0 < 2 * n := by omega
  -- `C(2n,n)` as a product over the primes `≤ 2n`
  have hprod : (∏ p ∈ Nat.primesLE (2 * n), p ^ (Nat.centralBinom n).factorization p)
      = Nat.centralBinom n := by
    rw [Nat.primesLE_eq_filter_range]
    refine (Finset.prod_filter_of_ne ?_).trans
      (Nat.prod_pow_factorization_centralBinom n)
    intro p _ hne
    by_contra hp
    exact hne (by rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero])
  rw [← hprod, ← Finset.prod_filter_mul_prod_filter_not (Nat.primesLE (2 * n))
    (fun p => n < p)]
  refine Nat.mul_le_mul ?_ ?_
  · -- primes in `(n, 2n]`: each factor is at most `2n`
    calc (∏ p ∈ (Nat.primesLE (2 * n)).filter fun p => n < p,
            p ^ (Nat.centralBinom n).factorization p)
        ≤ ∏ p ∈ (Nat.primesLE (2 * n)).filter fun p => n < p, (2 * n) :=
          Finset.prod_le_prod fun p _ => Nat.pow_factorization_choose_le h2n0
      _ = (2 * n) ^ (dyadicPrimes n).card := by
          rw [Finset.prod_const]
  · -- primes `≤ n`
    have hset : (Nat.primesLE (2 * n)).filter (fun p => ¬ n < p) = Nat.primesLE n := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, h2⟩, h1⟩
    rw [hset, ← Finset.prod_filter_mul_prod_filter_not (Nat.primesLE n)
      (fun p => p ≤ Nat.sqrt (2 * n))]
    refine Nat.mul_le_mul ?_ ?_
    · -- primes `≤ √(2n)`: each factor is at most `2n`, and there are at most `√(2n)`
      calc (∏ p ∈ (Nat.primesLE n).filter (· ≤ Nat.sqrt (2 * n)),
              p ^ (Nat.centralBinom n).factorization p)
          ≤ ∏ p ∈ (Nat.primesLE n).filter (· ≤ Nat.sqrt (2 * n)), (2 * n) :=
            Finset.prod_le_prod fun p _ => Nat.pow_factorization_choose_le h2n0
        _ = (2 * n) ^ ((Nat.primesLE n).filter (· ≤ Nat.sqrt (2 * n))).card :=
            Finset.prod_const
        _ ≤ (2 * n) ^ Nat.sqrt (2 * n) := by
            apply Nat.pow_le_pow_right (by omega)
            calc ((Nat.primesLE n).filter (· ≤ Nat.sqrt (2 * n))).card
                ≤ (Finset.Icc 1 (Nat.sqrt (2 * n))).card := by
                  apply Finset.card_le_card
                  intro p hp
                  rw [Finset.mem_filter, Nat.mem_primesLE] at hp
                  exact Finset.mem_Icc.mpr ⟨hp.1.2.one_lt.le, hp.2⟩
              _ = Nat.sqrt (2 * n) := by rw [Finset.card_Icc]; omega
    · -- primes in `(√(2n), n]`: factors with `p ≤ 2n/3` are at most `p`,
      -- factors with `p > 2n/3` are `1`
      calc (∏ p ∈ (Nat.primesLE n).filter (fun p => ¬ p ≤ Nat.sqrt (2 * n)),
              p ^ (Nat.centralBinom n).factorization p)
          = ∏ p ∈ ((Nat.primesLE n).filter (fun p => ¬ p ≤ Nat.sqrt (2 * n))).filter
              (· ≤ 2 * n / 3), p ^ (Nat.centralBinom n).factorization p := by
            symm
            apply Finset.prod_subset (Finset.filter_subset _ _)
            intro p hpB hpnB
            have hp' : 2 * n / 3 < p := by
              by_contra hc
              exact hpnB (Finset.mem_filter.mpr ⟨hpB, by omega⟩)
            rw [Finset.mem_filter, Nat.mem_primesLE] at hpB
            have h2n3 : 2 * n < 3 * p := by omega
            rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn
              hpB.1.1 h2n3, pow_zero]
        _ ≤ ∏ p ∈ ((Nat.primesLE n).filter (fun p => ¬ p ≤ Nat.sqrt (2 * n))).filter
              (· ≤ 2 * n / 3), p := by
            apply Finset.prod_le_prod
            intro p hp
            rw [Finset.mem_filter, Nat.mem_primesLE] at hp
            obtain ⟨⟨⟨-, hp'⟩, hsqrt⟩, -⟩ := hp
            have hsqrt' : Nat.sqrt (2 * n) < p := by omega
            have he1 : (Nat.centralBinom n).factorization p ≤ 1 :=
              Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp hsqrt')
            calc p ^ (Nat.centralBinom n).factorization p ≤ p ^ 1 :=
                  pow_right_mono₀ hp'.one_lt.le he1
              _ = p := pow_one p
        _ ≤ ∏ p ∈ Nat.primesLE (2 * n / 3), p := by
            apply Finset.prod_le_prod_of_subset_of_one_le
            · intro p hp
              rw [Finset.mem_filter, Nat.mem_primesLE] at hp
              exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.1.2⟩
            · intro p hp _
              exact (Nat.prime_of_mem_primesLE hp).one_lt.le
        _ = (2 * n / 3)# := rfl
        _ ≤ 4 ^ (2 * n / 3) := Nat.primorial_le_four_pow (2 * n / 3)

/-- Taking logarithms: `Δ(n)·log(2n) ≥ (n/3)·log 4 - log n - √(2n)·log(2n)`. -/
theorem dyadicPrimes_card_mul_log_ge (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) / 3 * Real.log 4 - Real.log n - (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * n)
      ≤ (dyadicPrimes n).card * Real.log (2 * n) := by
  have hn0 : 0 < n := by omega
  have hcb := centralBinom_le_dyadic n (by omega)
  have h4 : (4 : ℝ) ^ n < (n : ℝ) * ((2 * n : ℝ) ^ (dyadicPrimes n).card *
      ((2 * n : ℝ) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3))) := by
    have h1 := Nat.four_pow_lt_mul_centralBinom n hn
    have h2 : n * Nat.centralBinom n ≤
        n * ((2 * n) ^ (dyadicPrimes n).card *
          ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3))) :=
      Nat.mul_le_mul_left n hcb
    exact_mod_cast h1.trans_le h2
  have hlog := Real.log_lt_log (by positivity) h4
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_pow] at hlog
  have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * n) := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa using this
  have hdiv : ((2 * n / 3 : ℕ) : ℝ) ≤ (2 * n : ℝ) / 3 := by
    simpa using Nat.cast_div_le (2 * n) 3
  have hlog2n : 0 ≤ Real.log (2 * n : ℝ) :=
    Real.log_nonneg (by norm_cast; omega)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [hlog, mul_le_mul_of_nonneg_right hsqrt hlog2n,
    mul_le_mul_of_nonneg_right hdiv hlog4]

/-!
### The eventual lower bound `Δ(n) ≥ n/(8 log n)`
-/

theorem eventually_dyadicPrimes_card_ge : ∀ᶠ n : ℕ in Filter.atTop,
    (n : ℝ) / (8 * Real.log n) ≤ (dyadicPrimes n).card := by
  -- `log n / n → 0`
  have h1 : Filter.Tendsto (fun n : ℕ => Real.log n / n) Filter.atTop (𝓝 0) := by
    simpa using
      (Real.isLittleO_log_id_atTop.comp_tendsto
        tendsto_natCast_atTop_atTop).tendsto_div_nhds_zero
  -- `√(2n)·log(2n)/n → 0`
  have h2 : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) / n)
      Filter.atTop (𝓝 0) := by
    have hb := (Real.isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
      (tendsto_natCast_atTop_atTop.const_mul_atTop' (show (0 : ℝ) < 2 by norm_num))
    have hb' := hb.tendsto_div_nhds_zero
    refine (hb'.const_mul 2).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hB0 : (0 : ℝ) < (2 * (n : ℝ)) ^ (1 / 2 : ℝ) := by positivity
    have hB2 : ((2 * (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 = 2 * (n : ℝ) := by
      have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2n]
      norm_num [Real.rpow_one]
    rw [Real.sqrt_eq_rpow, ← mul_div_assoc]
    rw [div_eq_div_iff hB0.ne' hn'.ne']
    calc (2 * Real.log (2 * (n : ℝ))) * (n : ℝ)
        = Real.log (2 * (n : ℝ)) * (2 * (n : ℝ)) := by ring
      _ = Real.log (2 * (n : ℝ)) * ((2 * (n : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by rw [hB2]
      _ = ((2 * (n : ℝ)) ^ (1 / 2 : ℝ)) * Real.log (2 * (n : ℝ)) *
            ((2 * (n : ℝ)) ^ (1 / 2 : ℝ)) := by ring
  -- margin
  have hc0 : (0 : ℝ) < Real.log 4 / 3 - 1 / 4 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_gt_d9]
  obtain ⟨ε, hε, hεε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε + ε ≤ Real.log 4 / 3 - 1 / 4 :=
    ⟨(Real.log 4 / 3 - 1 / 4) / 2, by linarith, by linarith⟩
  have e1 : ∀ᶠ n : ℕ in Filter.atTop, Real.log n / n < ε :=
    h1.eventually (Iio_mem_nhds hε)
  have e2 : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) / n < ε :=
    h2.eventually (Iio_mem_nhds hε)
  filter_upwards [e1, e2, eventually_ge_atTop 4] with n hn1 hn2 hn4
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogx : 0 < Real.log (2 * (n : ℝ)) := Real.log_pos (by linarith)
  have hlogn : 0 < Real.log n := Real.log_pos (by norm_cast; omega)
  have hlogn' : Real.log n < ε * n := by rwa [div_lt_iff₀ hn0] at hn1
  have hsqrt' : Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) < ε * n := by
    rwa [div_lt_iff₀ hn0] at hn2
  have hD := dyadicPrimes_card_mul_log_ge n hn4
  have hsqrt_le : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 * n)
    simpa using this
  have hbound : (n : ℝ) / 4 ≤ (dyadicPrimes n).card * Real.log (2 * (n : ℝ)) := by
    have h1 : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) < ε * n :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsqrt_le hlogx.le) hsqrt'
    have h2 : (ε + ε) * (n : ℝ) ≤ (Real.log 4 / 3 - 1 / 4) * n :=
      mul_le_mul_of_nonneg_right hεε hn0.le
    nlinarith [hD, hlogn', h1, h2, hlogx]
  have hD2 : (n : ℝ) / 4 / Real.log (2 * (n : ℝ)) ≤ (dyadicPrimes n).card := by
    rwa [div_le_iff₀ hlogx]
  have hlog2n_le : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hle : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by norm_cast; omega)
    linarith
  calc (n : ℝ) / (8 * Real.log n)
      = (n / 4) / (2 * Real.log n) := by ring
    _ ≤ (n / 4) / Real.log (2 * (n : ℝ)) := by
        rw [div_le_div_iff₀ (mul_pos two_pos hlogn) hlogx]
        have := mul_le_mul_of_nonneg_left hlog2n_le (show (0:ℝ) ≤ n / 4 by positivity)
        linarith
    _ ≤ _ := hD2

/-!
### The injection `p²·q₁·q₂·q₃·q₄ ↦ n`
-/

/-- `largestPrimeFactor (p²·m) = p` when `m ≥ 1` and every prime divisor of `m`
is at most `p`. -/
theorem largestPrimeFactor_sq_mul_of_forall_prime_dvd_le {p m : ℕ} (hp : p.Prime)
    (hm : 1 ≤ m) (h : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ p) :
    largestPrimeFactor (p ^ 2 * m) = p := by
  have h2 : 2 ≤ p ^ 2 * m := by
    calc 2 ≤ 2 ^ 2 * 1 := by norm_num
      _ ≤ p ^ 2 * m := Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hm
  rw [largestPrimeFactor_eq_maxPrimeFac h2]
  apply le_antisymm
  · rw [Nat.maxPrimeFac_le_iff (show 1 < p ^ 2 * m by omega)]
    intro q hq hqd
    rcases hq.dvd_mul.mp hqd with h' | h'
    · rcases hp.eq_one_or_self_of_dvd _ (hq.dvd_of_dvd_pow h') with h1 | h1
      · exact absurd h1 hq.ne_one
      · exact h1.le
    · exact h q hq h'
  · exact Nat.le_maxPrimeFac (by omega) hp ⟨p * m, by ring⟩

/-- `Nat.minFac m = a` when `a` is a prime divisor of `m` that is at most every
prime divisor of `m`. -/
theorem minFac_eq_of_forall_le {a m : ℕ} (ha : a.Prime) (hd : a ∣ m)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → a ≤ q) : Nat.minFac m = a := by
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact ha.not_dvd_one hd
  exact le_antisymm (Nat.minFac_le_of_dvd ha.two_le hd)
    (h _ (Nat.minFac_prime hm1) (Nat.minFac_dvd m))

/-- A prime divisor of a product of two primes is one of them. -/
theorem prime_dvd_prime_mul_two {r a b : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hb : b.Prime) (h : r ∣ a * b) : r = a ∨ r = b := by
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases ha.eq_one_or_self_of_dvd _ h' with e | e
    · exact absurd e hr.ne_one
    · exact Or.inl e
  · rcases hb.eq_one_or_self_of_dvd _ h' with e | e
    · exact absurd e hr.ne_one
    · exact Or.inr e

/-- A prime divisor of a product of three primes is one of them. -/
theorem prime_dvd_prime_mul_three {r a b c : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hb : b.Prime) (hc : c.Prime) (h : r ∣ a * (b * c)) :
    r = a ∨ r = b ∨ r = c := by
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases ha.eq_one_or_self_of_dvd _ h' with e | e
    · exact absurd e hr.ne_one
    · exact Or.inl e
  · rcases prime_dvd_prime_mul_two hr hb hc h' with e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr e)

/-- A prime divisor of a product of four primes is one of them. -/
theorem prime_dvd_prime_mul_four {r a b c d : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (h : r ∣ a * (b * (c * d))) :
    r = a ∨ r = b ∨ r = c ∨ r = d := by
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases ha.eq_one_or_self_of_dvd _ h' with e | e
    · exact absurd e hr.ne_one
    · exact Or.inl e
  · rcases prime_dvd_prime_mul_three hr hb hc hd h' with e | e | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr e))

/-- The map `(p, q₁, q₂, q₃, q₄) ↦ p²·q₁·q₂·q₃·q₄`. -/
def quintMap : ℕ × ℕ × ℕ × ℕ × ℕ → ℕ
  | (p, q1, q2, q3, q4) => p ^ 2 * (q1 * (q2 * (q3 * q4)))

/-- The finset of tuples `(p, q₁, q₂, q₃, q₄)` of primes in five consecutive
dyadic shells: `p ∈ (P0, 2P0]`, `qᵢ ∈ (2^{i-1}Q0, 2^iQ0]`. -/
def quintSet (P0 Q0 : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  dyadicPrimes P0 ×ˢ (dyadicPrimes Q0 ×ˢ (dyadicPrimes (2 * Q0) ×ˢ
    (dyadicPrimes (4 * Q0) ×ˢ dyadicPrimes (8 * Q0))))

theorem mem_quintSet {P0 Q0 p q1 q2 q3 q4 : ℕ} :
    (p, q1, q2, q3, q4) ∈ quintSet P0 Q0 ↔
      (p ∈ dyadicPrimes P0 ∧ q1 ∈ dyadicPrimes Q0 ∧ q2 ∈ dyadicPrimes (2 * Q0) ∧
        q3 ∈ dyadicPrimes (4 * Q0) ∧ q4 ∈ dyadicPrimes (8 * Q0)) := by
  simp [quintSet, Finset.mem_product]

theorem card_quintSet (P0 Q0 : ℕ) :
    (quintSet P0 Q0).card = (dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
      ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
        (dyadicPrimes (8 * Q0)).card))) := by
  simp [quintSet, Finset.card_product]

/-- `badSingletonCount x` is at least the number of quintuples; the conditions
`16·Q0 ≤ P0` (so every `qᵢ < p`) and the displayed bound (so `n ≤ x`)
make the tuple map a valid injection into the bad set. -/
theorem card_quintSet_le_badSingletonCount (x P0 Q0 : ℕ) (hQP : 16 * Q0 ≤ P0)
    (hx : (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) * (16 * Q0)))) ≤ x) :
    (quintSet P0 Q0).card ≤ badSingletonCount x := by
  classical
  have hbad : (quintSet P0 Q0).image quintMap ⊆
      (Finset.range (x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m) := by
    rw [Finset.image_subset_iff]
    rintro ⟨p, q1, q2, q3, q4⟩ ht
    rw [mem_quintSet] at ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    obtain ⟨hp, hpP, hp2⟩ := mem_dyadicPrimes.mp h1
    obtain ⟨hq1, -, hq1b⟩ := mem_dyadicPrimes.mp h2
    obtain ⟨hq2, -, hq2b⟩ := mem_dyadicPrimes.mp h3
    obtain ⟨hq3, -, hq3b⟩ := mem_dyadicPrimes.mp h4
    obtain ⟨hq4, -, hq4b⟩ := mem_dyadicPrimes.mp h5
    have hm : 1 ≤ q1 * (q2 * (q3 * q4)) :=
      Nat.succ_le_of_lt (mul_pos hq1.pos (mul_pos hq2.pos (mul_pos hq3.pos hq4.pos)))
    have hsmooth : ∀ r : ℕ, r.Prime → r ∣ q1 * (q2 * (q3 * q4)) → r ≤ p := by
      intro r hr hrd
      rcases prime_dvd_prime_mul_four hr hq1 hq2 hq3 hq4 hrd with rfl | rfl | rfl | rfl <;>
        omega
    have hlpf : largestPrimeFactor (p ^ 2 * (q1 * (q2 * (q3 * q4)))) = p :=
      largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hm hsmooth
    have hle : p ^ 2 * (q1 * (q2 * (q3 * q4))) ≤ x := by
      calc p ^ 2 * (q1 * (q2 * (q3 * q4)))
          ≤ (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) * (16 * Q0)))) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hp2 2)
              (Nat.mul_le_mul hq1b (Nat.mul_le_mul hq2b (Nat.mul_le_mul hq3b hq4b)))
        _ ≤ x := hx
    have h2 : 2 ≤ p ^ 2 * (q1 * (q2 * (q3 * q4))) := by
      calc 2 ≤ 2 ^ 2 * 1 := by norm_num
        _ ≤ p ^ 2 * (q1 * (q2 * (q3 * q4))) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hm
    simp only [Finset.mem_filter, quintMap]
    refine ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
    rw [hlpf]
    exact ⟨q1 * (q2 * (q3 * q4)), rfl⟩
  have hinj : Set.InjOn quintMap (quintSet P0 Q0) := by
    rintro ⟨p, q1, q2, q3, q4⟩ ht ⟨r, s1, s2, s3, s4⟩ hs h
    rw [Finset.mem_coe, mem_quintSet] at ht
    rw [Finset.mem_coe, mem_quintSet] at hs
    obtain ⟨h1, h2, h3, h4, h5⟩ := ht
    obtain ⟨g1, g2, g3, g4, g5⟩ := hs
    obtain ⟨hp, hpP, -⟩ := mem_dyadicPrimes.mp h1
    obtain ⟨hq1, -, hq1b⟩ := mem_dyadicPrimes.mp h2
    obtain ⟨hq2, hQ2, hq2b⟩ := mem_dyadicPrimes.mp h3
    obtain ⟨hq3, hQ3, hq3b⟩ := mem_dyadicPrimes.mp h4
    obtain ⟨hq4, hQ4, hq4b⟩ := mem_dyadicPrimes.mp h5
    obtain ⟨hrp, hrP, -⟩ := mem_dyadicPrimes.mp g1
    obtain ⟨hs1, -, hs1b⟩ := mem_dyadicPrimes.mp g2
    obtain ⟨hs2, hS2, hs2b⟩ := mem_dyadicPrimes.mp g3
    obtain ⟨hs3, hS3, hs3b⟩ := mem_dyadicPrimes.mp g4
    obtain ⟨hs4, hS4, hs4b⟩ := mem_dyadicPrimes.mp g5
    have h' : p ^ 2 * (q1 * (q2 * (q3 * q4))) = r ^ 2 * (s1 * (s2 * (s3 * s4))) := h
    have hq_s : ∀ t : ℕ, t.Prime → t ∣ q1 * (q2 * (q3 * q4)) → t ≤ p := by
      intro t ht' htd
      rcases prime_dvd_prime_mul_four ht' hq1 hq2 hq3 hq4 htd with rfl | rfl | rfl | rfl <;>
        omega
    have hs_s : ∀ t : ℕ, t.Prime → t ∣ s1 * (s2 * (s3 * s4)) → t ≤ r := by
      intro t ht' htd
      rcases prime_dvd_prime_mul_four ht' hs1 hs2 hs3 hs4 htd with rfl | rfl | rfl | rfl <;>
        omega
    have hmq : 1 ≤ q1 * (q2 * (q3 * q4)) :=
      Nat.succ_le_of_lt (mul_pos hq1.pos (mul_pos hq2.pos (mul_pos hq3.pos hq4.pos)))
    have hms : 1 ≤ s1 * (s2 * (s3 * s4)) :=
      Nat.succ_le_of_lt (mul_pos hs1.pos (mul_pos hs2.pos (mul_pos hs3.pos hs4.pos)))
    have hpr : p = r := by
      have e1 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hmq hq_s
      have e2 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hrp hms hs_s
      rw [← e1, h', e2]
    subst hpr
    have hw1 : q1 * (q2 * (q3 * q4)) = s1 * (s2 * (s3 * s4)) :=
      Nat.mul_left_cancel (pow_pos hp.pos 2) h'
    have hq1s1 : q1 = s1 := by
      have e1 : Nat.minFac (q1 * (q2 * (q3 * q4))) = q1 := by
        apply minFac_eq_of_forall_le hq1 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_four ht' hq1 hq2 hq3 hq4 htd with rfl | rfl | rfl | rfl <;>
          omega
      have e2 : Nat.minFac (s1 * (s2 * (s3 * s4))) = s1 := by
        apply minFac_eq_of_forall_le hs1 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_four ht' hs1 hs2 hs3 hs4 htd with rfl | rfl | rfl | rfl <;>
          omega
      rw [hw1] at e1
      exact e1.symm.trans e2
    subst hq1s1
    have hw2 : q2 * (q3 * q4) = s2 * (s3 * s4) := Nat.mul_left_cancel hq1.pos hw1
    have hq2s2 : q2 = s2 := by
      have e1 : Nat.minFac (q2 * (q3 * q4)) = q2 := by
        apply minFac_eq_of_forall_le hq2 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_three ht' hq2 hq3 hq4 htd with rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s2 * (s3 * s4)) = s2 := by
        apply minFac_eq_of_forall_le hs2 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_three ht' hs2 hs3 hs4 htd with rfl | rfl | rfl <;> omega
      rw [hw2] at e1
      exact e1.symm.trans e2
    subst hq2s2
    have hw3 : q3 * q4 = s3 * s4 := Nat.mul_left_cancel hq2.pos hw2
    have hq3s3 : q3 = s3 := by
      have e1 : Nat.minFac (q3 * q4) = q3 := by
        apply minFac_eq_of_forall_le hq3 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_two ht' hq3 hq4 htd with rfl | rfl <;> omega
      have e2 : Nat.minFac (s3 * s4) = s3 := by
        apply minFac_eq_of_forall_le hs3 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_two ht' hs3 hs4 htd with rfl | rfl <;> omega
      rw [hw3] at e1
      exact e1.symm.trans e2
    subst hq3s3
    have hq4s4 : q4 = s4 := Nat.mul_left_cancel hq3.pos hw3
    rw [hq4s4]
  calc (quintSet P0 Q0).card
      = ((quintSet P0 Q0).image quintMap).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ badSingletonCount x := Finset.card_le_card hbad

/-!
### Assembly of the final bound
-/

theorem badSingletonCount_eventually_ge_smooth :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log x ^ 5 ≤ (badSingletonCount x : ℝ) := by
  -- `t = x^{1/200} → ∞`
  have htt : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 200 : ℝ)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  -- `t^{34} → ∞`, `t^{33} → ∞`
  have htt34 : Filter.Tendsto (fun x : ℕ => ((x : ℝ) ^ (1 / 200 : ℝ)) ^ 34)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' Filter.atTop
      ((htt.eventually_ge_atTop 1).mono fun x hx =>
        le_self_pow₀ hx (by norm_num)) htt
  have htt33 : Filter.Tendsto (fun x : ℕ => ((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' Filter.atTop
      ((htt.eventually_ge_atTop 1).mono fun x hx =>
        le_self_pow₀ hx (by norm_num)) htt
  -- the five shells tend to infinity as naturals
  have hP0t : Filter.Tendsto (fun x : ℕ => ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 34 / 4⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono (fun x => Nat.le_ceil _)
        (htt34.atTop_div_const (by norm_num)))
  have hQ0t : Filter.Tendsto (fun x : ℕ => ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono (fun x => Nat.le_ceil _)
        (htt33.atTop_div_const (by norm_num)))
  have h2Q0t : Filter.Tendsto
      (fun x : ℕ => 2 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h4Q0t : Filter.Tendsto
      (fun x : ℕ => 4 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h8Q0t : Filter.Tendsto
      (fun x : ℕ => 8 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  -- dyadic Chebyshev bounds on each shell
  have hC1 : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 34 / 4⌉₊ : ℝ) /
          (8 * Real.log ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 34 / 4⌉₊)
        ≤ (dyadicPrimes ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 34 / 4⌉₊).card :=
    hP0t.eventually eventually_dyadicPrimes_card_ge
  have hC2 : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊ : ℝ) /
          (8 * Real.log ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)
        ≤ (dyadicPrimes ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊).card :=
    hQ0t.eventually eventually_dyadicPrimes_card_ge
  have hC3 : ∀ᶠ x : ℕ in Filter.atTop,
      ((2 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (2 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊))
        ≤ (dyadicPrimes (2 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)).card :=
    h2Q0t.eventually eventually_dyadicPrimes_card_ge
  have hC4 : ∀ᶠ x : ℕ in Filter.atTop,
      ((4 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (4 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊))
        ≤ (dyadicPrimes (4 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)).card :=
    h4Q0t.eventually eventually_dyadicPrimes_card_ge
  have hC5 : ∀ᶠ x : ℕ in Filter.atTop,
      ((8 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (8 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊))
        ≤ (dyadicPrimes (8 * ⌈((x : ℝ) ^ (1 / 200 : ℝ)) ^ 33 / 16⌉₊)).card :=
    h8Q0t.eventually eventually_dyadicPrimes_card_ge
  -- `t ≥ 32` eventually
  have ht32 : ∀ᶠ x : ℕ in Filter.atTop, (32 : ℝ) ≤ (x : ℝ) ^ (1 / 200 : ℝ) :=
    htt.eventually_ge_atTop 32
  refine ⟨1 / 32768, by norm_num, ?_⟩
  filter_upwards [hC1, hC2, hC3, hC4, hC5, ht32, eventually_ge_atTop 2]
    with x hC1 hC2 hC3 hC4 hC5 ht32 hx2
  -- abbreviations
  set t : ℝ := (x : ℝ) ^ (1 / 200 : ℝ) with ht
  rw [← ht] at hC1 hC2 hC3 hC4 hC5 ht32
  set P0 : ℕ := ⌈t ^ 34 / 4⌉₊ with hP0
  rw [← hP0] at hC1
  set Q0 : ℕ := ⌈t ^ 33 / 16⌉₊ with hQ0
  rw [← hQ0] at hC2 hC3 hC4 hC5
  -- basic positivity facts
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hLnn : (0 : ℝ) ≤ Real.log x := hLpos.le
  have ht_pos : (0 : ℝ) < t := by rw [ht]; exact Real.rpow_pos_of_pos hx0 _
  have ht33_pos : (0 : ℝ) < t ^ 33 := by positivity
  have ht34_pos : (0 : ℝ) < t ^ 34 := by positivity
  have ht33_ge : (16 : ℝ) ≤ t ^ 33 :=
    le_trans (by linarith [ht32] : (16 : ℝ) ≤ t) (le_self_pow₀ (by linarith) (by norm_num))
  have ht34_ge : (4 : ℝ) ≤ t ^ 34 :=
    le_trans (by linarith [ht32] : (4 : ℝ) ≤ t) (le_self_pow₀ (by linarith) (by norm_num))
  have hlogt : Real.log t = 1 / 200 * Real.log (x : ℝ) := by
    rw [ht, Real.log_rpow hx0]
  have ht200 : t ^ 200 = (x : ℝ) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 / 200 : ℝ) * ((200 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have ht166 : t ^ 166 = (x : ℝ) ^ (83 / 100 : ℝ) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 / 200 : ℝ) * ((166 : ℕ) : ℝ) = 83 / 100 by norm_num]
  -- bounds on `P0`, `Q0`
  have hP0_ge : t ^ 34 / 4 ≤ (P0 : ℝ) := by
    rw [hP0]; exact Nat.le_ceil _
  have hP0_le : (P0 : ℝ) ≤ t ^ 34 / 2 := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t ^ 34 / 4 by positivity)).le
    rw [hP0] at h
    linarith [ht34_ge]
  have hQ0_ge : t ^ 33 / 16 ≤ (Q0 : ℝ) := by
    rw [hQ0]; exact Nat.le_ceil _
  have hQ0_le : (Q0 : ℝ) ≤ t ^ 33 / 8 := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t ^ 33 / 16 by positivity)).le
    rw [hQ0] at h
    linarith [ht33_ge]
  -- `16·Q0 ≤ P0` (so that every `qᵢ < p`)
  have h8v : 8 * t ^ 33 ≤ t ^ 34 := by
    have h : t ^ 34 = t * t ^ 33 := pow_succ t 33
    rw [h]
    exact mul_le_mul_of_nonneg_right (by linarith [ht32]) ht33_pos.le
  have hQP : 16 * Q0 ≤ P0 := by
    have hr : (16 : ℝ) * Q0 ≤ (P0 : ℝ) := by linarith [hQ0_le, hP0_ge, h8v]
    exact_mod_cast hr
  -- `n ≤ x`
  have hxn : (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) * (16 * Q0)))) ≤ x := by
    have hreal : (2 * (P0 : ℝ)) ^ 2 * ((2 * (Q0 : ℝ)) * ((4 * (Q0 : ℝ)) *
        ((8 * (Q0 : ℝ)) * (16 * (Q0 : ℝ))))) ≤ (x : ℝ) := by
      have h1 : (2 : ℝ) * P0 ≤ t ^ 34 := by linarith [hP0_le]
      have h2 : (2 : ℝ) * Q0 ≤ t ^ 33 / 4 := by linarith [hQ0_le]
      have h3 : (4 : ℝ) * Q0 ≤ t ^ 33 / 2 := by linarith [hQ0_le]
      have h4 : (8 : ℝ) * Q0 ≤ t ^ 33 := by linarith [hQ0_le]
      have h5 : (16 : ℝ) * Q0 ≤ 2 * t ^ 33 := by linarith [hQ0_le]
      calc (2 * (P0 : ℝ)) ^ 2 * ((2 * (Q0 : ℝ)) * ((4 * (Q0 : ℝ)) *
              ((8 * (Q0 : ℝ)) * (16 * (Q0 : ℝ)))))
          ≤ (t ^ 34) ^ 2 * ((t ^ 33 / 4) * ((t ^ 33 / 2) * (t ^ 33 * (2 * t ^ 33)))) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) ?_ (by positivity)
              (by positivity)
            exact mul_le_mul h2 (mul_le_mul h3 (mul_le_mul h4 h5 (by positivity)
              (by positivity)) (by positivity) (by positivity)) (by positivity)
              (by positivity)
        _ = t ^ 200 / 4 := by ring
        _ = (x : ℝ) / 4 := by rw [ht200]
        _ ≤ x := by linarith [hx0]
    exact_mod_cast hreal
  -- nat count bound
  have hnat : (dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
      ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
        (dyadicPrimes (8 * Q0)).card))) ≤ badSingletonCount x := by
    rw [← card_quintSet]
    exact card_quintSet_le_badSingletonCount x P0 Q0 hQP hxn
  -- log bounds for each shell
  have hlogP0 : Real.log (P0 : ℝ) ≤ 34 / 200 * Real.log x := by
    have hpos : (0 : ℝ) < P0 := by linarith [hP0_ge, ht34_ge]
    calc Real.log (P0 : ℝ) ≤ Real.log (t ^ 34) :=
          Real.log_le_log hpos (by linarith [hP0_le, ht34_pos])
      _ = 34 * Real.log t := Real.log_pow _ _
      _ = 34 / 200 * Real.log x := by rw [hlogt]; push_cast; ring
  have hlogP0pos : 0 < Real.log (P0 : ℝ) := Real.log_pos (by linarith [hP0_ge, ht34_ge])
  have hlogQ0 : Real.log (Q0 : ℝ) ≤ 33 / 200 * Real.log x := by
    have hpos : (0 : ℝ) < Q0 := by linarith [hQ0_ge, ht33_ge]
    calc Real.log (Q0 : ℝ) ≤ Real.log (t ^ 33) :=
          Real.log_le_log hpos (by linarith [hQ0_le, ht33_pos])
      _ = 33 * Real.log t := Real.log_pow _ _
      _ = 33 / 200 * Real.log x := by rw [hlogt]; push_cast; ring
  have hlogQ0pos : 0 < Real.log (Q0 : ℝ) := Real.log_pos (by linarith [hQ0_ge, ht33_ge])
  have hlog2Q0 : Real.log (2 * Q0 : ℝ) ≤ 33 / 200 * Real.log x := by
    have hpos : (0 : ℝ) < (2 * Q0 : ℕ) := by positivity
    have hle : (2 * Q0 : ℝ) ≤ t ^ 33 := by
      have : (Q0 : ℝ) ≤ t ^ 33 / 8 := hQ0_le
      push_cast
      linarith [ht33_pos]
    calc Real.log (2 * Q0 : ℝ) ≤ Real.log (t ^ 33) := Real.log_le_log (by positivity) hle
      _ = 33 * Real.log t := Real.log_pow _ _
      _ = 33 / 200 * Real.log x := by rw [hlogt]; push_cast; ring
  have hlog2Q0pos : 0 < Real.log (2 * Q0 : ℝ) :=
    Real.log_pos (by have := hQ0_ge; push_cast at *; linarith [ht33_ge])
  have hlog4Q0 : Real.log (4 * Q0 : ℝ) ≤ 33 / 200 * Real.log x := by
    have hle : (4 * Q0 : ℝ) ≤ t ^ 33 := by
      have : (Q0 : ℝ) ≤ t ^ 33 / 8 := hQ0_le
      push_cast
      linarith [ht33_pos]
    calc Real.log (4 * Q0 : ℝ) ≤ Real.log (t ^ 33) := Real.log_le_log (by positivity) hle
      _ = 33 * Real.log t := Real.log_pow _ _
      _ = 33 / 200 * Real.log x := by rw [hlogt]; push_cast; ring
  have hlog4Q0pos : 0 < Real.log (4 * Q0 : ℝ) :=
    Real.log_pos (by have := hQ0_ge; push_cast at *; linarith [ht33_ge])
  have hlog8Q0 : Real.log (8 * Q0 : ℝ) ≤ 33 / 200 * Real.log x := by
    have hle : (8 * Q0 : ℝ) ≤ t ^ 33 := by
      have : (Q0 : ℝ) ≤ t ^ 33 / 8 := hQ0_le
      push_cast
      linarith [ht33_pos]
    calc Real.log (8 * Q0 : ℝ) ≤ Real.log (t ^ 33) := Real.log_le_log (by positivity) hle
      _ = 33 * Real.log t := Real.log_pow _ _
      _ = 33 / 200 * Real.log x := by rw [hlogt]; push_cast; ring
  have hlog8Q0pos : 0 < Real.log (8 * Q0 : ℝ) :=
    Real.log_pos (by have := hQ0_ge; push_cast at *; linarith [ht33_ge])
  -- lower bounds for each dyadic cardinal
  have hD1 : t ^ 34 / (6 * Real.log x) ≤ ((dyadicPrimes P0).card : ℝ) := by
    calc t ^ 34 / (6 * Real.log x)
        ≤ (t ^ 34 / 4) / (8 * Real.log P0) := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
            (mul_pos (by norm_num) hlogP0pos)]
          calc t ^ 34 * (8 * Real.log P0)
              ≤ t ^ 34 * (3 / 2 * Real.log x) :=
                mul_le_mul_of_nonneg_left (by linarith [hlogP0]) ht34_pos.le
            _ = t ^ 34 / 4 * (6 * Real.log x) := by ring
      _ ≤ (P0 : ℝ) / (8 * Real.log P0) :=
          div_le_div_of_nonneg_right hP0_ge (by positivity)
      _ ≤ _ := hC1
  have hD2 : t ^ 33 / (22 * Real.log x) ≤ ((dyadicPrimes Q0).card : ℝ) := by
    calc t ^ 33 / (22 * Real.log x)
        ≤ (t ^ 33 / 16) / (8 * Real.log Q0) := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
            (mul_pos (by norm_num) hlogQ0pos)]
          calc t ^ 33 * (8 * Real.log Q0)
              ≤ t ^ 33 * (11 / 8 * Real.log x) :=
                mul_le_mul_of_nonneg_left (by linarith [hlogQ0]) ht33_pos.le
            _ = t ^ 33 / 16 * (22 * Real.log x) := by ring
      _ ≤ (Q0 : ℝ) / (8 * Real.log Q0) :=
          div_le_div_of_nonneg_right hQ0_ge (by positivity)
      _ ≤ _ := hC2
  have hD3 : t ^ 33 / (11 * Real.log x) ≤ ((dyadicPrimes (2 * Q0)).card : ℝ) := by
    have hlo : t ^ 33 / 8 ≤ (2 * Q0 : ℝ) := by
      have := hQ0_ge; push_cast at *; linarith
    calc t ^ 33 / (11 * Real.log x)
        ≤ (t ^ 33 / 8) / (8 * Real.log (2 * Q0)) := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
            (mul_pos (by norm_num) hlog2Q0pos)]
          calc t ^ 33 * (8 * Real.log (2 * Q0))
              ≤ t ^ 33 * (11 / 8 * Real.log x) :=
                mul_le_mul_of_nonneg_left (by linarith [hlog2Q0]) ht33_pos.le
            _ = t ^ 33 / 8 * (11 * Real.log x) := by ring
      _ ≤ (2 * Q0 : ℝ) / (8 * Real.log (2 * Q0)) :=
          div_le_div_of_nonneg_right hlo (by positivity)
      _ ≤ _ := hC3
  have hD4 : t ^ 33 / (6 * Real.log x) ≤ ((dyadicPrimes (4 * Q0)).card : ℝ) := by
    have hlo : t ^ 33 / 4 ≤ (4 * Q0 : ℝ) := by
      have := hQ0_ge; push_cast at *; linarith
    calc t ^ 33 / (6 * Real.log x)
        ≤ (t ^ 33 / 4) / (8 * Real.log (4 * Q0)) := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
            (mul_pos (by norm_num) hlog4Q0pos)]
          calc t ^ 33 * (8 * Real.log (4 * Q0))
              ≤ t ^ 33 * (3 / 2 * Real.log x) :=
                mul_le_mul_of_nonneg_left (by linarith [hlog4Q0]) ht33_pos.le
            _ = t ^ 33 / 4 * (6 * Real.log x) := by ring
      _ ≤ (4 * Q0 : ℝ) / (8 * Real.log (4 * Q0)) :=
          div_le_div_of_nonneg_right hlo (by positivity)
      _ ≤ _ := hC4
  have hD5 : t ^ 33 / (3 * Real.log x) ≤ ((dyadicPrimes (8 * Q0)).card : ℝ) := by
    have hlo : t ^ 33 / 2 ≤ (8 * Q0 : ℝ) := by
      have := hQ0_ge; push_cast at *; linarith
    calc t ^ 33 / (3 * Real.log x)
        ≤ (t ^ 33 / 2) / (8 * Real.log (8 * Q0)) := by
          rw [div_le_div_iff₀ (mul_pos (by norm_num) hLpos)
            (mul_pos (by norm_num) hlog8Q0pos)]
          calc t ^ 33 * (8 * Real.log (8 * Q0))
              ≤ t ^ 33 * (3 / 2 * Real.log x) :=
                mul_le_mul_of_nonneg_left (by linarith [hlog8Q0]) ht33_pos.le
            _ = t ^ 33 / 2 * (3 * Real.log x) := by ring
      _ ≤ (8 * Q0 : ℝ) / (8 * Real.log (8 * Q0)) :=
          div_le_div_of_nonneg_right hlo (by positivity)
      _ ≤ _ := hC5
  -- product bound
  have hprod : t ^ 34 / (6 * Real.log x) * (t ^ 33 / (22 * Real.log x) *
      (t ^ 33 / (11 * Real.log x) * (t ^ 33 / (6 * Real.log x) *
        (t ^ 33 / (3 * Real.log x))))) ≤
      ((dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
        ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
          (dyadicPrimes (8 * Q0)).card))) : ℝ) :=
    mul_le_mul hD1
      (mul_le_mul hD2
        (mul_le_mul hD3
          (mul_le_mul hD4 hD5 (div_nonneg ht33_pos.le (by linarith [hLnn]))
            (by positivity))
          (div_nonneg ht33_pos.le (by linarith [hLnn])) (by positivity))
        (div_nonneg ht33_pos.le (by linarith [hLnn])) (by positivity))
      (div_nonneg ht33_pos.le (by linarith [hLnn])) (by positivity)
  -- final real inequality
  have key : t ^ 34 / (6 * Real.log x) * (t ^ 33 / (22 * Real.log x) *
      (t ^ 33 / (11 * Real.log x) * (t ^ 33 / (6 * Real.log x) *
        (t ^ 33 / (3 * Real.log x))))) = t ^ 166 / (26136 * Real.log x ^ 5) := by
    field_simp [hLpos.ne']
    ring
  calc (1 / 32768 : ℝ) * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log x ^ 5
      = t ^ 166 / (32768 * Real.log x ^ 5) := by
        rw [← ht166, div_eq_div_iff (pow_pos hLpos 5).ne'
          (mul_pos (by norm_num) (pow_pos hLpos 5)).ne']
        ring
    _ ≤ t ^ 166 / (26136 * Real.log x ^ 5) := by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by norm_num) (pow_pos hLpos 5))
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hLnn 5)
    _ = t ^ 34 / (6 * Real.log x) * (t ^ 33 / (22 * Real.log x) *
          (t ^ 33 / (11 * Real.log x) * (t ^ 33 / (6 * Real.log x) *
            (t ^ 33 / (3 * Real.log x))))) := key.symm
    _ ≤ _ := hprod
    _ ≤ (badSingletonCount x : ℝ) := by exact_mod_cast hnat

end SmoothLB

end JSP314
