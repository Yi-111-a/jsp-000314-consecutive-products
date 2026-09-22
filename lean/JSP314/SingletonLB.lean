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
# A strong lower bound for `badSingletonCount`

We prove that the number `S(x) = badSingletonCount x` of `n ≤ x` with
`1 < n` and `P(n)² ∣ n` satisfies the eventual lower bound

  `S(x) ≥ c · x^{2/3} / log x`

for an explicit constant `c = 1/256` and all sufficiently large `x`.

## Proof outline

* **Chebyshev-type dyadic bound.** From `4ⁿ < n · C(2n,n)`
  (`Nat.four_pow_lt_mul_centralBinom`) and the factorization
  `C(2n,n) = ∏ p^{e_p}` over primes `p ≤ 2n`, with the contributions
  - `p ≤ √(2n)` bounded by `2n` each (`Nat.pow_factorization_choose_le`),
  - `√(2n) < p ≤ 2n/3` bounded by `4^{2n/3}` via the primorial bound
    `Nat.primorial_le_four_pow` and `Nat.factorization_choose_le_one`,
  - `2n/3 < p ≤ n` contributing nothing
    (`Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul`),
  - `n < p ≤ 2n` bounded by `(2n)^{#dyadic primes}`,

  we get `C(2n,n) ≤ (2n)^{√(2n) + Δ(n)} · 4^{2n/3}`, hence
  `Δ(n) = #{p prime : n < p ≤ 2n} ≥ n / (8 log n)` eventually
  (`eventually_dyadicPrimes_card_ge`).

* **Injection.** For `n₀ = ⌈x^{1/3}⌉` every pair `(p, m)` with `p` prime,
  `n₀ < p ≤ 2n₀` and `1 ≤ m ≤ ⌊x/p²⌋` produces a bad singleton `p²·m ≤ x`,
  and the map is injective since `P(p²·m) = p`
  (`badSingletonCount_ge_sum_dyadic`).

* **Assembly.** `S(x) ≥ Δ(n₀)·⌊x/(4n₀²)⌋ ≥ (x^{1/3}/(12 log x^{1/3}))·(x^{1/3}/32)`
  which is `≥ x^{2/3}/(128 log x)` for large `x`
  (`badSingletonCount_eventually_ge`).
-/

namespace JSP314

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
  -- `hlog : n·log4 < log n + (D·log(2n) + (√·log(2n) + ⌊2n/3⌋·log4))`
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
    -- goal: `2 * log (2n) * n = B * log (2n) * B` where `B = (2n)^{1/2}`
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
  -- `D·log(2n) ≥ n·(log4/3 - 1/4 - ε - ε)·... ≥ n/4`
  have hbound : (n : ℝ) / 4 ≤ (dyadicPrimes n).card * Real.log (2 * (n : ℝ)) := by
    have h1 : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) < ε * n :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsqrt_le hlogx.le) hsqrt'
    have h2 : (ε + ε) * (n : ℝ) ≤ (Real.log 4 / 3 - 1 / 4) * n :=
      mul_le_mul_of_nonneg_right hεε hn0.le
    nlinarith [hD, hlogn', h1, h2, hlogx]
  -- divide out
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
        -- `n/4 · log(2n) ≤ n/4 · 2·log n`
        have := mul_le_mul_of_nonneg_left hlog2n_le (show (0:ℝ) ≤ n / 4 by positivity)
        linarith
    _ ≤ _ := hD2

/-!
### The injection `p² · m ↦ n`
-/

theorem largestPrimeFactor_sq_mul {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hmp : m ≤ p) :
    largestPrimeFactor (p ^ 2 * m) = p := by
  have h2 : 2 ≤ p ^ 2 * m := by
    calc 2 ≤ 2 ^ 2 * 1 := by norm_num
      _ ≤ p ^ 2 * m := Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hm
  rw [largestPrimeFactor_eq_maxPrimeFac h2]
  apply le_antisymm
  · have hq : (Nat.maxPrimeFac (p ^ 2 * m)).Prime :=
      Nat.prime_maxPrimeFac_of_one_lt (by omega)
    have hqd : Nat.maxPrimeFac (p ^ 2 * m) ∣ p ^ 2 * m := Nat.maxPrimeFac_dvd
    rcases hq.dvd_mul.mp hqd with h | h
    · have h'' := hq.dvd_of_dvd_pow h
      rcases hp.eq_one_or_self_of_dvd _ h'' with h1 | h1
      · exact absurd h1 hq.ne_one
      · exact h1.le
    · exact (Nat.le_of_dvd hm h).trans hmp
  · exact Nat.le_maxPrimeFac (by omega) hp ⟨p * m, by ring⟩

theorem badSingletonCount_ge_sum_dyadic (x n : ℕ) (hx : x ≤ n ^ 3) :
    (∑ p ∈ dyadicPrimes n, x / p ^ 2) ≤ badSingletonCount x := by
  classical
  let S : Finset (Σ _ : ℕ, ℕ) := (dyadicPrimes n).sigma fun p => Finset.Icc 1 (x / p ^ 2)
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun pm => pm.1 ^ 2 * pm.2
  have key : ∀ p m : ℕ, p ∈ dyadicPrimes n → 1 ≤ m → m ≤ x / p ^ 2 →
      largestPrimeFactor (p ^ 2 * m) = p := by
    intro p m hp hm1 hm2
    have hpp := (mem_dyadicPrimes.mp hp).1
    have hnp := (mem_dyadicPrimes.mp hp).2.1
    have hplt : x / p ^ 2 < p := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < p ^ 2)]
      calc x ≤ n ^ 3 := hx
        _ < p ^ 3 := Nat.pow_lt_pow_left hnp (by norm_num)
        _ = p * p ^ 2 := by ring
    exact largestPrimeFactor_sq_mul hpp hm1 (lt_of_le_of_lt hm2 hplt).le
  -- the image is contained in the bad set
  have hsub : S.image f ⊆
      (Finset.range (x + 1)).filter fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨⟨p, m⟩, hp, rfl⟩ := hy
    rw [Finset.mem_sigma] at hp
    obtain ⟨hpdy, hmIcc⟩ := hp
    rw [Finset.mem_Icc] at hmIcc
    obtain ⟨hpp, -, -⟩ := mem_dyadicPrimes.mp hpdy
    have hlpf := key p m hpdy hmIcc.1 hmIcc.2
    have hle : p ^ 2 * m ≤ x :=
      (Nat.mul_le_mul_left _ hmIcc.2).trans (Nat.mul_div_le x _)
    have h2 : 2 ≤ p ^ 2 * m := by
      calc 2 ≤ 2 ^ 2 * 1 := by norm_num
        _ ≤ p ^ 2 * m := Nat.mul_le_mul (Nat.pow_le_pow_left hpp.two_le 2) hmIcc.1
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt hle (Nat.lt_succ_self x)), by omega,
      hlpf ▸ dvd_mul_right _ _⟩
  -- the map is injective: `p` is recovered as the largest prime factor
  have hinj : Set.InjOn f S := by
    rintro ⟨p, m⟩ hp ⟨q, k⟩ hq h
    rw [Finset.mem_coe, Finset.mem_sigma] at hp hq
    obtain ⟨hpdy, hmIcc⟩ := hp
    obtain ⟨hqdy, hkIcc⟩ := hq
    rw [Finset.mem_Icc] at hmIcc hkIcc
    have hlp := key p m hpdy hmIcc.1 hmIcc.2
    have hlq := key q k hqdy hkIcc.1 hkIcc.2
    have h' : p ^ 2 * m = q ^ 2 * k := h
    have hpq : p = q := by rw [← hlp, h', hlq]
    subst hpq
    have hmk : m = k :=
      Nat.mul_left_cancel (pow_pos (mem_dyadicPrimes.mp hpdy).1.pos _) h'
    subst hmk
  calc (∑ p ∈ dyadicPrimes n, x / p ^ 2)
      = S.card := by
        rw [Finset.card_sigma]
        refine (Finset.sum_congr rfl fun p hp => ?_).symm
        rw [Nat.card_Icc]
        omega
    _ = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ badSingletonCount x := Finset.card_le_card hsub

/-!
### Assembly of the final bound
-/

theorem badSingletonCount_eventually_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ^ (2 / 3 : ℝ) / Real.log x ≤ (badSingletonCount x : ℝ) := by
  have ht : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hn0t : Filter.Tendsto (fun x : ℕ => ⌈(x : ℝ) ^ (1 / 3 : ℝ)⌉₊) Filter.atTop
      Filter.atTop :=
    tendsto_atTop_mono (fun x => Nat.le_ceil _) ht
  have hC : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈(x : ℝ) ^ (1 / 3 : ℝ)⌉₊ : ℝ) /
          (8 * Real.log ⌈(x : ℝ) ^ (1 / 3 : ℝ)⌉₊)
        ≤ (dyadicPrimes ⌈(x : ℝ) ^ (1 / 3 : ℝ)⌉₊).card :=
    hn0t.eventually eventually_dyadicPrimes_card_ge
  have h32 : ∀ᶠ x : ℕ in Filter.atTop, (32 : ℝ) ≤ (x : ℝ) ^ (1 / 3 : ℝ) :=
    ht.eventually_ge_atTop 32
  refine ⟨1 / 256, by norm_num, ?_⟩
  filter_upwards [hC, h32] with x hC' h32'
  set t := (x : ℝ) ^ (1 / 3 : ℝ) with ht_def
  set n0 := ⌈t⌉₊
  -- basic facts
  have ht0 : (0 : ℝ) ≤ t := Real.rpow_nonneg (by positivity) _
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have ht1 : (1 : ℝ) ≤ t := by linarith [h32']
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  -- `x = t³` as reals
  have hxr : (x : ℝ) = t ^ 3 := by
    rw [ht_def, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num [Real.rpow_one]
  have hlogx : Real.log (x : ℝ) = 3 * Real.log t := by
    rw [hxr, Real.log_pow]
    norm_num
  have ht2 : (x : ℝ) ^ (2 / 3 : ℝ) = t ^ 2 := by
    rw [hxr, ← Real.rpow_natCast t 3, ← Real.rpow_mul ht0]
    norm_num [Real.rpow_natCast]
  -- bounds on `n0`
  have hn0ge : (t : ℝ) ≤ n0 := Nat.le_ceil t
  have hn0lt : (n0 : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
  have hn0pos : (0 : ℝ) < n0 := lt_of_lt_of_le (by norm_num) (le_trans h32' hn0ge)
  have hn0ge2 : (2 : ℝ) ≤ n0 := le_trans (by norm_num) hn0ge
  have hn02 : (n0 : ℝ) ≤ 2 * t := by linarith
  have hlogn0p : 0 < Real.log n0 := Real.log_pos (by linarith)
  -- `x ≤ n0³` in ℕ
  have hxn3 : x ≤ n0 ^ 3 := by
    have h : (x : ℝ) ≤ (n0 : ℝ) ^ 3 := by
      rw [hxr]
      exact pow_le_pow_left₀ ht0 hn0ge 3
    have h' : (x : ℝ) ≤ ((n0 ^ 3 : ℕ) : ℝ) := by push_cast; push_cast at h ⊢; exact h
    exact_mod_cast h'
  -- `log n0 ≤ (3/2) log t`
  have hlogn0 : Real.log n0 ≤ 3 / 2 * Real.log t := by
    have h1 : Real.log (n0 : ℝ) ≤ Real.log (2 * t) := Real.log_le_log hn0pos (by linarith)
    have h2 : Real.log (2 * t) = Real.log 2 + Real.log t :=
      Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 2 ≤ Real.log t / 2 := by
      have h4 : Real.log 4 ≤ Real.log t := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_four_eq] at h4
      linarith
    linarith
  -- `D = #dyadicPrimes n0 ≥ t/(12 log t)`
  have hD : (t : ℝ) / (12 * Real.log t) ≤ (dyadicPrimes n0).card := by
    have hstep1 : t / (12 * Real.log t) ≤ n0 / (12 * Real.log t) := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hlogt) (mul_pos (by norm_num) hlogt)]
      have := mul_le_mul_of_nonneg_right hn0ge (mul_pos (by norm_num : (0:ℝ) < 12) hlogt).le
      linarith
    have hstep2 : n0 / (12 * Real.log t) ≤ n0 / (8 * Real.log n0) := by
      rw [div_le_div_iff₀ (mul_pos (by norm_num) hlogt) (mul_pos (by norm_num) hlogn0p)]
      have h8 : 8 * Real.log n0 ≤ 12 * Real.log t := by linarith
      have := mul_le_mul_of_nonneg_left h8 hn0pos.le
      linarith
    exact hstep1.trans (hstep2.trans hC')
  -- `K = x/(4 n0²) ≥ t/32`
  have hnatdiv : (x : ℝ) / (4 * (n0 : ℝ) ^ 2) - 1 ≤ ((x / (4 * n0 ^ 2) : ℕ) : ℝ) := by
    have hk0 : (0 : ℝ) < 4 * (n0 : ℝ) ^ 2 := by positivity
    have h : x < (x / (4 * n0 ^ 2) + 1) * (4 * n0 ^ 2) :=
      (Nat.div_lt_iff_lt_mul (show 0 < 4 * n0 ^ 2 by positivity)).mp (Nat.lt_succ_self _)
    have h' : (x : ℝ) / (4 * (n0 : ℝ) ^ 2) < ((x / (4 * n0 ^ 2) : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hk0]
      have h'' : (x : ℝ) < (((x / (4 * n0 ^ 2) + 1) * (4 * n0 ^ 2) : ℕ) : ℝ) :=
        by exact_mod_cast h
      push_cast at h''
      convert h'' using 1
      ring
    linarith
  have hx16 : (t : ℝ) / 16 ≤ (x : ℝ) / (4 * (n0 : ℝ) ^ 2) := by
    rw [div_le_iff₀ (show (0 : ℝ) < 4 * (n0 : ℝ) ^ 2 by positivity)]
    rw [hxr]
    have hn0sq : (n0 : ℝ) ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ hn0pos.le hn02 2
    have hprod : t * (n0 : ℝ) ^ 2 ≤ t * (2 * t) ^ 2 :=
      mul_le_mul_of_nonneg_left hn0sq ht0
    nlinarith [hprod]
  have hK : (t : ℝ) / 32 ≤ ((x / (4 * n0 ^ 2) : ℕ) : ℝ) := by
    nlinarith [hnatdiv, hx16, h32']
  -- `D · K ≤ S x` in ℕ
  have hnat : (dyadicPrimes n0).card * (x / (4 * n0 ^ 2)) ≤ badSingletonCount x := by
    calc (dyadicPrimes n0).card * (x / (4 * n0 ^ 2))
        = ∑ p ∈ dyadicPrimes n0, x / (4 * n0 ^ 2) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ dyadicPrimes n0, x / p ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpp, -, hp2n⟩ := mem_dyadicPrimes.mp hp
          exact Nat.div_le_div_left
            (calc p ^ 2 ≤ (2 * n0) ^ 2 := Nat.pow_le_pow_left hp2n 2
              _ = 4 * n0 ^ 2 := by ring)
            (by positivity)
      _ ≤ badSingletonCount x := badSingletonCount_ge_sum_dyadic x n0 hxn3
  -- real conclusion
  calc (1 / 256 : ℝ) * (x : ℝ) ^ (2 / 3 : ℝ) / Real.log x
      = (1 / 256) * t ^ 2 / (3 * Real.log t) := by rw [ht2, hlogx]
    _ ≤ t ^ 2 / (384 * Real.log t) := by
        rw [div_le_div_iff₀ (mul_pos (by norm_num) hlogt) (mul_pos (by norm_num) hlogt)]
        nlinarith [hlogt, ht1, sq_nonneg t]
    _ = (t / (12 * Real.log t)) * (t / 32) := by
        field_simp [hlogt.ne']
        ring
    _ ≤ (dyadicPrimes n0).card * ((x / (4 * n0 ^ 2) : ℕ) : ℝ) :=
        mul_le_mul hD hK (by positivity) (by positivity)
    _ ≤ badSingletonCount x := by exact_mod_cast hnat

end JSP314
