import JSP314.BandSum
import JSP314.Assembly
import JSP314.SingletonLBz
import JSP314.ShortResidual

/-!
# JSP-000314 — fresh-eye audit addendum: weakest-link conditional closures

Independent audit of the sole remaining placeholder
`badNonSingleton_interval_bound` (`JSP314/Main.lean`).  This file adds no new
mathematical input; it repackages the already-proved combinatorial
decompositions into **strictly weaker sufficient hypotheses** than the
`/8`-ratio of `RatioGlue.badNonSingleton_interval_bound_of_runCountSum_ratio`,
and records two audit facts:

* **Non-vacuity** (`isBadInterval_8_9`, `two_le_badNonSingletonCount`,
  `eventually_two_le_badNonSingletonCount`): `[8,9]` is a non-singleton bad
  interval, so `N(x) ≥ 2` for all `x ≥ 9` — the residual is a genuine
  asymptotic statement, not vacuous.
* **Tightness of the run-witness reduction**
  (`inShortBadInterval_of_mem_rightRunWitness_one`,
  `inShortBadInterval_of_mem_leftRunWitness_one`,
  `sum_rightRunCount_one_le_shortBadCount`,
  `sum_leftRunCount_one_le_shortBadCount`): every `k = 1` run witness `m`
  generates the genuine bad interval `[m, m ± 1]`, so the diagonal of
  `runCountSum` is bounded *above* by `shortBadCount (2x)` — the witness count
  is not a spuriously large object.

## The conditional closures

`badNonSingleton_interval_bound_of_eventually_le` is a generic transporter:
from *any* pointwise decomposition `N ≤ c·f + (2·10^16+1)` and an eventual
bound `f ≤ S·(log x)^{-1}·(log log x)^K` (any fixed `K : ℝ`, any sign), the
residual `badNonSingleton_interval_bound` follows.  Instantiated with the four
existing decompositions:

| hypothesis on `f` | pointwise bound used |
|---|---|
| `shortBadCount` | `N ≤ T_short + C₀` (`SSBound`) |
| `∑_p nearPairCoveredCount x p` | `N ≤ ∑ + C₀` (`ShortResidual`) |
| `runCountSum` | `N ≤ 2·runCountSum + C₀` (`BandSum`) |

The `(log log x)^K` slack means the hypotheses need only hold up to any fixed
poly-loglog factor — and, via `exists_loglog_bound_of_const`, a plain
`f ≤ C·S·(log x)^{-1}` (any fixed `C`, absorbing `RatioGlue`'s `/8`) suffices.
-/

namespace JSP314

open Filter Classical

section Absorption

/-- `L = log x → ∞` along `ℕ` (local abbreviation used throughout). -/
private theorem tendsto_log_atTop' :
    Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log log x → ∞` along `ℕ`. -/
private theorem tendsto_loglog_atTop' :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_atTop'

/-- **Constant absorption into the singleton scale.**
Any constant is eventually `≤ S(x)·(log x)^{-1}`: the `z`-scale lower bound
`S(x) ≥ x·exp(−C·√(L·L₂))` (`SingletonLBz`) plus the exponential saving over
`x` (`BandSum.eventually_const_le_exp_neg_mul_log_inv`). -/
theorem badSingletonCount_mul_log_inv_eventually_ge (K0 : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      K0 ≤ (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) := by
  obtain ⟨C, _hC, hS⟩ := SingletonLBz.badSingletonCount_eventually_ge_zscale
  have hK := eventually_const_le_exp_neg_mul_log_inv K0 C
  filter_upwards [hK, hS, tendsto_log_atTop'.eventually_ge_atTop 1]
    with x hx hSx hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  exact hx.trans
    (mul_le_mul_of_nonneg_right hSx (Real.rpow_nonneg hL.le _))

/-- **Constant-to-loglog upgrade.**  If `f x ≤ C·S·(log x)^{-1}` eventually
for a fixed `C : ℝ`, then `f x ≤ S·(log x)^{-1}·(log log x)^1` eventually
(since `C ≤ log log x` eventually). -/
theorem exists_loglog_bound_of_const {f : ℕ → ℕ} (C : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K := by
  refine ⟨1, ?_⟩
  filter_upwards [h, tendsto_loglog_atTop'.eventually_ge_atTop C,
    tendsto_log_atTop'.eventually_ge_atTop 1] with x hx hC hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  have hBnn : (0 : ℝ) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  calc (f x : ℝ)
      ≤ C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) := hx
    _ = C * ((badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :=
        mul_assoc _ _ _
    _ ≤ Real.log (Real.log (x : ℝ)) *
          ((badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC hBnn
    _ = (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log (x : ℝ))) ^ (1 : ℝ) := by
        rw [Real.rpow_one]; ring

end Absorption

section Transporter

/-- **Generic transporter.**  From a pointwise decomposition
`N(x) ≤ c·f(x) + (2·10^16+1)` (any `c : ℕ`) and an eventual bound
`f(x) ≤ S(x)·(log x)^{-1}·(log log x)^K` for *some* real `K` (any sign), the
residual `badNonSingleton_interval_bound` holds.

Proof sketch: replace `K` by `max K 0`; for `t = log log x ≥ 2`,
`c ≤ t^c` (since `c ≤ 2^c`), `t^K ≤ t^{max K 0}`, the constant `2·10^16+1`
absorbs into `S·L^{-1}` (`badSingletonCount_mul_log_inv_eventually_ge`), and
`2 ≤ t` upgrades `2·t^{K₀+c}` to `t^{K₀+c+1}`, giving
`N ≤ S·L^{-1}·t^{K₀+c+1}` — the exact hypothesis of
`Assembly.badNonSingleton_interval_bound_of_loglog_factor`. -/
theorem badNonSingleton_interval_bound_of_eventually_le {f : ℕ → ℕ} (c : ℕ)
    (hdecomp : ∀ x : ℕ, badNonSingletonCount x ≤ c * f x + (2 * 10 ^ 16 + 1))
    (h : ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨K, hK⟩ := h
  apply badNonSingleton_interval_bound_of_loglog_factor (max K 0 + c + 1)
  have hC₀ := badSingletonCount_mul_log_inv_eventually_ge
    ((2 * 10 ^ 16 + 1 : ℕ) : ℝ)
  filter_upwards [hK, hC₀, tendsto_loglog_atTop'.eventually_ge_atTop 2,
    tendsto_log_atTop'.eventually_ge_atTop 1] with x hx hCx ht2 hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  set t := Real.log (Real.log (x : ℝ)) with htdef
  have ht1 : (1 : ℝ) ≤ t := by linarith [ht2]
  have ht0 : (0 : ℝ) < t := by linarith [ht2]
  set K₀ := max K 0 with hK₀def
  have hK₀nn : (0 : ℝ) ≤ K₀ := le_max_right _ _
  set B := (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) with hBdef
  have hBnn : (0 : ℝ) ≤ B :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  -- `f ≤ B·t^{K₀}` (exponent lift `K ≤ max K 0`).
  have hf : (f x : ℝ) ≤ B * t ^ K₀ :=
    hx.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left K 0)) hBnn)
  -- `(c:ℝ) ≤ t^{(c:ℝ)}` from `c < 2^c ≤ t^c`.
  have hc : (c : ℝ) ≤ t ^ (c : ℝ) := by
    have h2c : (c : ℝ) ≤ (2 : ℝ) ^ (c : ℝ) := by
      rw [Real.rpow_natCast]
      have h := Nat.lt_two_pow_self (n := c)
      exact_mod_cast h.le
    exact h2c.trans
      (Real.rpow_le_rpow (by norm_num) ht2 (Nat.cast_nonneg _))
  -- `c·f ≤ B·t^{K₀+c}`.
  have hcf : (c : ℝ) * (f x : ℝ) ≤ B * t ^ (K₀ + c) := by
    calc (c : ℝ) * (f x : ℝ)
        ≤ t ^ (c : ℝ) * (B * t ^ K₀) :=
          mul_le_mul hc hf (Nat.cast_nonneg _) (Real.rpow_nonneg ht0.le _)
      _ = B * t ^ (K₀ + c) := by
          rw [show t ^ (c : ℝ) * (B * t ^ K₀) = B * (t ^ K₀ * t ^ (c : ℝ)) by
            ring, ← Real.rpow_add ht0]
  -- `C₀ ≤ B ≤ B·t^{K₀+c}` since `t^{K₀+c} ≥ 1`.
  have hC₀' : ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ B * t ^ (K₀ + c) := by
    have h1 : (1 : ℝ) ≤ t ^ (K₀ + c) :=
      Real.one_le_rpow ht1 (add_nonneg hK₀nn (Nat.cast_nonneg _))
    calc ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ B := hCx
      _ = B * 1 := (mul_one _).symm
      _ ≤ B * t ^ (K₀ + c) := mul_le_mul_of_nonneg_left h1 hBnn
  -- assemble: `N ≤ 2·B·t^{K₀+c} ≤ B·t^{K₀+c+1}` since `2 ≤ t`.
  have hstep : (2 : ℝ) * (B * t ^ (K₀ + c)) ≤ B * t ^ (K₀ + c + 1) := by
    have e : t ^ (K₀ + c + 1) = t ^ (K₀ + c) * t := by
      rw [Real.rpow_add ht0, Real.rpow_one]
    calc (2 : ℝ) * (B * t ^ (K₀ + c))
        = B * t ^ (K₀ + c) * 2 := by ring
      _ ≤ B * t ^ (K₀ + c) * t :=
          mul_le_mul_of_nonneg_left ht2
            (mul_nonneg hBnn (Real.rpow_nonneg ht0.le _))
      _ = B * t ^ (K₀ + c + 1) := by rw [e]; ring
  have hdec : (badNonSingletonCount x : ℝ) ≤
      (c : ℝ) * (f x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hdecomp x
  calc (badNonSingletonCount x : ℝ)
      ≤ (c : ℝ) * (f x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := hdec
    _ ≤ B * t ^ (K₀ + c) + B * t ^ (K₀ + c) := add_le_add hcf hC₀'
    _ = 2 * (B * t ^ (K₀ + c)) := by ring
    _ ≤ B * t ^ (K₀ + c + 1) := hstep

end Transporter

section Closures

/-- `N = O(S / log x)` suffices: from `badNonSingletonCount x ≤ C·S·(log x)^{-1}`
eventually (any fixed `C : ℝ`), the residual holds. -/
theorem badNonSingleton_interval_bound_of_const_mul_ratio (C : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨K, hK⟩ := exists_loglog_bound_of_const (f := badNonSingletonCount) C h
  exact badNonSingleton_interval_bound_of_loglog_factor K hK

/-- Short-interval form: `T_short ≤ S·L^{-1}·(log log)^K` suffices
(`N ≤ T_short + C₀`). -/
theorem badNonSingleton_interval_bound_of_shortBadCount_loglog
    (h : ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (shortBadCount x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_eventually_le (f := shortBadCount) 1
    (fun x => by simpa using badNonSingletonCount_le_short_add_const x) h

/-- Constant-ratio version: `T_short ≤ C·S·(log x)^{-1}` suffices. -/
theorem badNonSingleton_interval_bound_of_shortBadCount_const (C : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      (shortBadCount x : ℝ) ≤
        C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_shortBadCount_loglog
    (exists_loglog_bound_of_const (f := shortBadCount) C h)

/-- Point-level pair form: `∑_p nearPairCoveredCount x p ≤ S·L^{-1}·(log log)^K`
suffices (`N ≤ ∑ + C₀` — no multiplicity factor, the tightest reduction). -/
theorem badNonSingleton_interval_bound_of_nearPairSum_loglog
    (h : ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          nearPairCoveredCount x p : ℕ) : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_eventually_le
    (f := fun x => ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
      nearPairCoveredCount x p) 1
    (fun x => by simpa using badNonSingletonCount_le_nearPair_sum_add_const x) h

/-- Constant-ratio version: `∑_p nearPairCoveredCount x p ≤ C·S·(log x)^{-1}`
suffices. -/
theorem badNonSingleton_interval_bound_of_nearPairSum_const (C : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          nearPairCoveredCount x p : ℕ) : ℝ) ≤
        C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_nearPairSum_loglog
    (exists_loglog_bound_of_const C h)

/-- Run-sum form: `runCountSum ≤ S·L^{-1}·(log log)^K` suffices
(`N ≤ 2·runCountSum + C₀`).  Strictly weaker than `RatioGlue`'s `/8` form. -/
theorem badNonSingleton_interval_bound_of_runCountSum_loglog
    (h : ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_eventually_le (f := runCountSum) 2
    badNonSingletonCount_le_two_mul_runCountSum_add_const h

/-- Constant-ratio version: `runCountSum ≤ C·S·(log x)^{-1}` suffices
(generalises `RatioGlue`'s `/8`). -/
theorem badNonSingleton_interval_bound_of_runCountSum_const (C : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_runCountSum_loglog
    (exists_loglog_bound_of_const (f := runCountSum) C h)

end Closures

section NonVacuity

/-- `largestPrimeFactor 72 = 3`: every prime divisor of `72 = 2³·3²` is `2` or
`3` (proved manually since `largestPrimeFactor` is not kernel-reducible). -/
theorem largestPrimeFactor_72 : largestPrimeFactor 72 = 3 := by
  apply le_antisymm
  · rw [lpf_le_iff_forall_prime_dvd_le (by norm_num : (1 : ℕ) ≤ 72)
      (by norm_num : (1 : ℕ) ≤ 3)]
    intro q hq hq72
    have h89 : q ∣ 8 ∨ q ∣ 9 := by
      have e : (72 : ℕ) = 8 * 9 := by norm_num
      exact hq.dvd_mul.mp (e ▸ hq72)
    rcases h89 with h8 | h9
    · have hq2 : q ∣ 2 := hq.prime.dvd_of_dvd_pow (show q ∣ 2 ^ 3 from h8)
      have hqeq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
      omega
    · have hq3 : q ∣ 3 := hq.prime.dvd_of_dvd_pow (show q ∣ 3 ^ 2 from h9)
      have hqeq := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp hq3
      omega
  · exact prime_dvd_le_largestPrimeFactor (by norm_num : 2 ≤ 72)
      Nat.prime_three (by norm_num : 3 ∣ 72)

/-- The interval `[8, 9]` is bad: `prod = 72 = 2³·3²`, `P = 3`, `3² ∣ 72`.
This makes the residual statement genuinely non-vacuous. -/
theorem isBadInterval_8_9 : IsBadInterval 8 9 := by
  have hprod : (Finset.Icc 8 9).prod id = 72 := by decide
  refine ⟨by norm_num, ?_⟩
  show largestPrimeFactor ((Finset.Icc 8 9).prod id) ≠ 1 ∧
    (largestPrimeFactor ((Finset.Icc 8 9).prod id)) ^ 2 ∣
      (Finset.Icc 8 9).prod id
  rw [hprod, largestPrimeFactor_72]
  exact ⟨by norm_num, by norm_num⟩

theorem inNonSingletonBadInterval_8 : InNonSingletonBadInterval 8 :=
  ⟨8, 9, by norm_num, isBadInterval_8_9, le_refl 8, by norm_num⟩

theorem inNonSingletonBadInterval_9 : InNonSingletonBadInterval 9 :=
  ⟨8, 9, by norm_num, isBadInterval_8_9, by norm_num, le_refl 9⟩

/-- `N(x) ≥ 2` for all `x ≥ 9`: both `8` and `9` are covered by `[8,9]`. -/
theorem two_le_badNonSingletonCount {x : ℕ} (hx : 9 ≤ x) :
    2 ≤ badNonSingletonCount x := by
  have hsub : ({8, 9} : Finset ℕ) ⊆
      (Finset.range (x + 1)).filter (fun n => InNonSingletonBadInterval n) := by
    intro n hn
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    rcases hn with rfl | rfl
    · exact ⟨by omega, inNonSingletonBadInterval_8⟩
    · exact ⟨by omega, inNonSingletonBadInterval_9⟩
  calc (2 : ℕ) = ({8, 9} : Finset ℕ).card :=
        (Finset.card_pair (by norm_num : (8 : ℕ) ≠ 9)).symm
    _ ≤ ((Finset.range (x + 1)).filter
          (fun n => InNonSingletonBadInterval n)).card :=
        Finset.card_le_card hsub
    _ = badNonSingletonCount x := rfl

/-- `N(x)` is nondecreasing in `x`. -/
theorem badNonSingletonCount_mono : Monotone badNonSingletonCount := by
  intro x y hxy
  unfold badNonSingletonCount
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.range_subset_range.mpr (show x + 1 ≤ y + 1 by omega)))

/-- The non-singleton bad count is eventually `≥ 2`: the residual is a real
asymptotic between diverging quantities, not a vacuous bound. -/
theorem eventually_two_le_badNonSingletonCount :
    ∀ᶠ x : ℕ in atTop, 2 ≤ badNonSingletonCount x := by
  filter_upwards [eventually_ge_atTop 9] with x hx
  exact two_le_badNonSingletonCount hx

end NonVacuity

section Tightness

/-- A `p²`-multiple `m` with `largestPrimeFactor m = p` and a `p`-smooth
right neighbour `m + 1` is itself covered by the short bad interval
`[m, m + 1]`: its product `m·(m+1)` has largest prime factor `p`, `p² ∣ m`
divides the product, and the length `1 < p`.  This is the tightness direction
of the run-witness reduction: every `k = 1` right run witness is a genuine
short-covered point. -/
theorem inShortBadInterval_of_mem_rightRunWitness_one {x p m : ℕ}
    (hp : Nat.Prime p) (hm : m ∈ rightRunWitness x p 1) :
    InShortBadInterval m := by
  rw [mem_rightRunWitness] at hm
  obtain ⟨_hm2x, hdvd, hlpf, hsm⟩ := hm
  have hsm1 : largestPrimeFactor (m + 1) ≤ p :=
    hsm (m + 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    exact hp.ne_one (hlpf ▸ largestPrimeFactor_eq_one_iff.mpr (by omega))
  have hprod : (Finset.Icc m (m + 1)).prod id = m * (m + 1) := by
    rw [Finset.prod_Icc_succ_top (show m ≤ m + 1 by omega) id,
      Finset.Icc_self, Finset.prod_singleton]
    rfl
  have hprod2 : 2 ≤ m * (m + 1) := by
    have h12 : 2 * 3 ≤ m * (m + 1) := Nat.mul_le_mul hm2 (by omega)
    omega
  -- `P = largestPrimeFactor (m·(m+1)) = p`.
  have hpD : p ∣ m * (m + 1) :=
    dvd_trans ((dvd_pow_self p two_ne_zero).trans hdvd) (dvd_mul_right m _)
  have hPle : largestPrimeFactor (m * (m + 1)) ≤ p := by
    rw [lpf_le_iff_forall_prime_dvd_le (by omega : 1 ≤ m * (m + 1)) hp.one_lt.le]
    intro q hq hqD
    rcases (hq.dvd_mul).mp hqD with hqm | hqm1
    · exact hlpf ▸ prime_dvd_le_largestPrimeFactor hm2 hq hqm
    · exact (prime_dvd_le_largestPrimeFactor (by omega : 2 ≤ m + 1) hq
        hqm1).trans hsm1
  have hPge : p ≤ largestPrimeFactor (m * (m + 1)) :=
    prime_dvd_le_largestPrimeFactor hprod2 hp hpD
  have hP : largestPrimeFactor (m * (m + 1)) = p := le_antisymm hPle hPge
  have hbad : IsBadInterval m (m + 1) := by
    refine ⟨by omega, ?_⟩
    show largestPrimeFactor ((Finset.Icc m (m + 1)).prod id) ≠ 1 ∧
      (largestPrimeFactor ((Finset.Icc m (m + 1)).prod id)) ^ 2 ∣
        (Finset.Icc m (m + 1)).prod id
    rw [hprod, hP]
    exact ⟨hp.ne_one, dvd_trans hdvd (dvd_mul_right m _)⟩
  exact ⟨m, m + 1, by omega, hbad, le_refl m, by omega, by
    rw [hprod, hP]
    have : m + 1 - m = 1 := by omega
    rw [this]
    exact hp.one_lt⟩

/-- The left analogue: a `p²`-multiple `m` with `largestPrimeFactor m = p` and
a `p`-smooth left neighbour `m − 1` is covered by the short bad interval
`[m − 1, m]` (note `m ≥ p² ≥ 4`, so `m − 1 ≥ 3`). -/
theorem inShortBadInterval_of_mem_leftRunWitness_one {x p m : ℕ}
    (hp : Nat.Prime p) (hm : m ∈ leftRunWitness x p 1) :
    InShortBadInterval m := by
  rw [mem_leftRunWitness] at hm
  obtain ⟨_hm2x, hdvd, hlpf, hsm⟩ := hm
  have hsm1 : largestPrimeFactor (m - 1) ≤ p :=
    hsm (m - 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    exact hp.ne_one (hlpf ▸ largestPrimeFactor_eq_one_iff.mpr (by omega))
  have hm4 : 4 ≤ m := by
    have hp2 : 4 ≤ p ^ 2 := by
      have := hp.two_le
      nlinarith
    exact hp2.trans (Nat.le_of_dvd (by omega) hdvd)
  have hm1m : m - 1 + 1 = m := by omega
  have hIcc : Finset.Icc (m - 1) m = Finset.Icc (m - 1) (m - 1 + 1) := by
    rw [hm1m]
  have hprod : (Finset.Icc (m - 1) m).prod id = (m - 1) * m := by
    rw [hIcc, Finset.prod_Icc_succ_top (show m - 1 ≤ m - 1 + 1 by omega) id,
      Finset.Icc_self, Finset.prod_singleton, hm1m]
    rfl
  have hprod2 : 2 ≤ (m - 1) * m := by
    have h12 : 3 * 4 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) hm4
    omega
  have hpD : p ∣ (m - 1) * m :=
    dvd_trans ((dvd_pow_self p two_ne_zero).trans hdvd) (dvd_mul_left m _)
  have hPle : largestPrimeFactor ((m - 1) * m) ≤ p := by
    rw [lpf_le_iff_forall_prime_dvd_le (by omega : 1 ≤ (m - 1) * m) hp.one_lt.le]
    intro q hq hqD
    rcases (hq.dvd_mul).mp hqD with hqm1 | hqm
    · exact (prime_dvd_le_largestPrimeFactor (by omega : 2 ≤ m - 1) hq
        hqm1).trans hsm1
    · exact hlpf ▸ prime_dvd_le_largestPrimeFactor hm2 hq hqm
  have hPge : p ≤ largestPrimeFactor ((m - 1) * m) :=
    prime_dvd_le_largestPrimeFactor hprod2 hp hpD
  have hP : largestPrimeFactor ((m - 1) * m) = p := le_antisymm hPle hPge
  have hbad : IsBadInterval (m - 1) m := by
    refine ⟨by omega, ?_⟩
    show largestPrimeFactor ((Finset.Icc (m - 1) m).prod id) ≠ 1 ∧
      (largestPrimeFactor ((Finset.Icc (m - 1) m).prod id)) ^ 2 ∣
        (Finset.Icc (m - 1) m).prod id
    rw [hprod, hP]
    exact ⟨hp.ne_one, dvd_trans hdvd (dvd_mul_left m _)⟩
  exact ⟨m - 1, m, by omega, hbad, by omega, le_refl m, by
    rw [hprod, hP]
    have : m - (m - 1) = 1 := by omega
    rw [this]
    exact hp.one_lt⟩

/-- The `k = 1` right-run witnesses, summed over `p`, are a *bona fide* piece
of `shortBadCount (2x)`: distinct `p` give disjoint witness sets
(`p = largestPrimeFactor m` is determined by `m`), and every witness is
covered by `[m, m+1]`.  Hence `runCountSum` is not a vacuously large
overcount — its diagonal already corresponds to real covered points. -/
theorem sum_rightRunCount_one_le_shortBadCount (x : ℕ) :
    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), rightRunCount x p 1 ≤
      shortBadCount (2 * x) := by
  classical
  have hdisj : (Nat.primesLE (Nat.sqrt (2 * x)) : Set ℕ).PairwiseDisjoint
      (fun p => rightRunWitness x p 1) := by
    intro p _hp q _hq hpq
    show Disjoint (rightRunWitness x p 1) (rightRunWitness x q 1)
    rw [Finset.disjoint_left]
    intro m hmp hmq
    rw [mem_rightRunWitness] at hmp hmq
    exact hpq (hmp.2.2.1.symm.trans hmq.2.2.1)
  have hsub : (Nat.primesLE (Nat.sqrt (2 * x))).biUnion
        (fun p => rightRunWitness x p 1) ⊆
      (Finset.range (2 * x + 1)).filter (fun n => InShortBadInterval n) := by
    intro m hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨p, hp, hm⟩ := hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_add_one_iff.mpr (mem_rightRunWitness.mp hm).1,
      inShortBadInterval_of_mem_rightRunWitness_one
        (Nat.prime_of_mem_primesLE hp) hm⟩
  calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), rightRunCount x p 1
      = ((Nat.primesLE (Nat.sqrt (2 * x))).biUnion
          (fun p => rightRunWitness x p 1)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((Finset.range (2 * x + 1)).filter
          (fun n => InShortBadInterval n)).card :=
        Finset.card_le_card hsub
    _ = shortBadCount (2 * x) := rfl

/-- The left-side analogue of `sum_rightRunCount_one_le_shortBadCount`. -/
theorem sum_leftRunCount_one_le_shortBadCount (x : ℕ) :
    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), leftRunCount x p 1 ≤
      shortBadCount (2 * x) := by
  classical
  have hdisj : (Nat.primesLE (Nat.sqrt (2 * x)) : Set ℕ).PairwiseDisjoint
      (fun p => leftRunWitness x p 1) := by
    intro p _hp q _hq hpq
    show Disjoint (leftRunWitness x p 1) (leftRunWitness x q 1)
    rw [Finset.disjoint_left]
    intro m hmp hmq
    rw [mem_leftRunWitness] at hmp hmq
    exact hpq (hmp.2.2.1.symm.trans hmq.2.2.1)
  have hsub : (Nat.primesLE (Nat.sqrt (2 * x))).biUnion
        (fun p => leftRunWitness x p 1) ⊆
      (Finset.range (2 * x + 1)).filter (fun n => InShortBadInterval n) := by
    intro m hm
    rw [Finset.mem_biUnion] at hm
    obtain ⟨p, hp, hm⟩ := hm
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_add_one_iff.mpr (mem_leftRunWitness.mp hm).1,
      inShortBadInterval_of_mem_leftRunWitness_one
        (Nat.prime_of_mem_primesLE hp) hm⟩
  calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), leftRunCount x p 1
      = ((Nat.primesLE (Nat.sqrt (2 * x))).biUnion
          (fun p => leftRunWitness x p 1)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((Finset.range (2 * x + 1)).filter
          (fun n => InShortBadInterval n)).card :=
        Finset.card_le_card hsub
    _ = shortBadCount (2 * x) := rfl

end Tightness

end JSP314

section AxiomCheck

#print axioms JSP314.badNonSingleton_interval_bound_of_eventually_le
#print axioms JSP314.badNonSingleton_interval_bound_of_shortBadCount_loglog
#print axioms JSP314.badNonSingleton_interval_bound_of_nearPairSum_loglog
#print axioms JSP314.badNonSingleton_interval_bound_of_runCountSum_loglog
#print axioms JSP314.badNonSingleton_interval_bound_of_const_mul_ratio
#print axioms JSP314.badNonSingleton_interval_bound_of_shortBadCount_const
#print axioms JSP314.badNonSingleton_interval_bound_of_nearPairSum_const
#print axioms JSP314.badNonSingleton_interval_bound_of_runCountSum_const
#print axioms JSP314.isBadInterval_8_9
#print axioms JSP314.two_le_badNonSingletonCount
#print axioms JSP314.eventually_two_le_badNonSingletonCount
#print axioms JSP314.badNonSingletonCount_mono
#print axioms JSP314.inShortBadInterval_of_mem_rightRunWitness_one
#print axioms JSP314.inShortBadInterval_of_mem_leftRunWitness_one
#print axioms JSP314.sum_rightRunCount_one_le_shortBadCount
#print axioms JSP314.sum_leftRunCount_one_le_shortBadCount
#print axioms JSP314.badSingletonCount_mul_log_inv_eventually_ge
#print axioms JSP314.exists_loglog_bound_of_const

end AxiomCheck
