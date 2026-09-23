import JSP314.Defs
import JSP314.SmoothLB
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

open Finset Filter SmoothLB

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
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos hpp.pos)]
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
    have hfm : f ⟨p, m⟩ = p ^ 2 * m := rfl
    rw [Finset.mem_filter, hfm]
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hle (Nat.lt_succ_self x)), by omega, ?_⟩
    rw [hlpf]
    exact dvd_mul_right _ _
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
    exact congrArg (Sigma.mk _) hmk
  calc (∑ p ∈ dyadicPrimes n, x / p ^ 2)
      = S.card := by
        rw [Finset.card_sigma]
        refine (Finset.sum_congr rfl fun p hp => ?_).symm
        rw [Nat.card_Icc, Nat.add_sub_cancel]
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
      Filter.atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨i, hi⟩ := eventually_atTop.1 (ht.eventually_ge_atTop (b : ℝ))
    exact ⟨i, fun a ha ↦ Nat.cast_le.1 ((hi a ha).trans (Nat.le_ceil _))⟩
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
  have hn0ge2 : (2 : ℝ) ≤ n0 := le_trans (by linarith) hn0ge
  have hn02 : (n0 : ℝ) ≤ 2 * t := by linarith
  have hlogn0p : 0 < Real.log n0 := Real.log_pos (by linarith)
  -- `x ≤ n0³` in ℕ
  have hxn3 : x ≤ n0 ^ 3 := by
    have h : (x : ℝ) ≤ (n0 : ℝ) ^ 3 := by
      rw [hxr]
      exact pow_le_pow_left₀ ht0 hn0ge 3
    have h' : (x : ℝ) ≤ ((n0 ^ 3 : ℕ) : ℝ) := by push_cast; exact h
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
      exact h''
    linarith
  have hx16 : (t : ℝ) / 16 ≤ (x : ℝ) / (4 * (n0 : ℝ) ^ 2) := by
    rw [le_div_iff₀ (show (0 : ℝ) < 4 * (n0 : ℝ) ^ 2 by positivity)]
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
            (Nat.pow_pos hpp.pos)
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
        mul_le_mul hD hK (div_nonneg ht0 (by norm_num)) (Nat.cast_nonneg _)
    _ ≤ badSingletonCount x := by exact_mod_cast hnat

end JSP314
