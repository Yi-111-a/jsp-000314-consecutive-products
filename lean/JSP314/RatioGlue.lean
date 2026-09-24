import JSP314.BandSum
import JSP314.SingletonLBz
import JSP314.Assembly
import Mathlib.Tactic

/-!
# JSP-000314 — ratio-form conditional closure for `badNonSingleton_interval_bound`

The single remaining `sorry` of the project (`JSP314/Main.lean`,
`badNonSingleton_interval_bound`) is reduced here to a clean **ratio-shaped**
obligation on the combinatorial run-count sum `BandSum.runCountSum`:

  `runCountSum x ≤ badSingletonCount x * (log x)^{-1} / 8`   eventually,

matching Tao's actual estimate `N(x) ≲ S(x)·(log x)^{-1}` (the fixed constant
`1/8`, like any fixed constant, is absorbed by the `L^ε` slack).  No new
mathematical input is assumed: the singleton `z`-scale lower bound
(`SingletonLBz.badSingletonCount_eventually_ge_zscale`) plus constant
absorption (`BandSum.eventually_const_le_exp_neg_mul_log_inv`) turn the
Sylvester–Schur constant `2·10^16+1` of
`BandSum.badNonSingletonCount_le_two_mul_runCountSum_add_const` into
`≤ S·(log x)^{-1}`.

Contents:

* `badNonSingleton_interval_bound_of_runCountSum_ratio` — the `/8`-ratio
  hypothesis implies the residual.
* `badNonSingleton_interval_bound_of_runCountSum_ratio_loglog` — the same with
  an extra `(log log x)^K` slack (`K ≥ 0`) in the hypothesis, discharged via
  `Assembly.badNonSingleton_interval_bound_of_loglog_factor`.
-/

namespace JSP314

open Filter

/-- **Ratio-form conditional closure.**

If eventually `runCountSum x ≤ badSingletonCount x * (log x)^{-1} / 8`, then
the residual `badNonSingleton_interval_bound` holds: for every `ε > 0`,
eventually `N(x) ≤ (log x)^{-1+ε} · S(x)`.

Proof: `N ≤ 2·runCountSum + (2·10^16+1)`; the hypothesis gives
`2·runCountSum ≤ S·L^{-1}/4`, while `2·10^16+1 ≤ x·e^{-C·s}·L^{-1} ≤ S·L^{-1}`
eventually (constant absorption + the singleton `z`-scale lower bound).  Hence
`N ≤ (5/4)·S·L^{-1} ≤ S·L^{-(1-ε)}` once `L^ε ≥ 5/4`. -/
theorem badNonSingleton_interval_bound_of_runCountSum_ratio
    (h : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) / 8) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  obtain ⟨C, _hCpos, hS⟩ := SingletonLBz.badSingletonCount_eventually_ge_zscale
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hK := eventually_const_le_exp_neg_mul_log_inv
    ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) C
  have hLε : Tendsto (fun x : ℕ => (Real.log (x : ℝ)) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hLt
  have h54 : ∀ᶠ x : ℕ in atTop, (5 / 4 : ℝ) ≤ (Real.log (x : ℝ)) ^ ε :=
    hLε.eventually_ge_atTop (5 / 4)
  filter_upwards [h, hS, hK, h54, hLt.eventually_ge_atTop 1]
    with x hx hSx hKx h54x hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  set B := (badSingletonCount x : ℝ) * L ^ (-(1 : ℝ)) with hBdef
  have hB_nn : (0 : ℝ) ≤ B :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  -- The Sylvester–Schur constant is absorbed: `2·10^16+1 ≤ x·e^{-C·s}·L^{-1} ≤ B`.
  have hKB : ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ B := by
    have h1 : (x : ℝ) * Real.exp (-C * s) * L ^ (-(1 : ℝ)) ≤ B :=
      mul_le_mul_of_nonneg_right hSx (Real.rpow_nonneg hL.le _)
    exact hKx.trans h1
  have hNle : (badNonSingletonCount x : ℝ) ≤
      2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_two_mul_runCountSum_add_const x
  have htot : (badNonSingletonCount x : ℝ) ≤ B * (5 / 4) := by
    calc (badNonSingletonCount x : ℝ)
        ≤ 2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := hNle
      _ ≤ 2 * (B / 8) + B :=
          add_le_add (mul_le_mul_of_nonneg_left hx (by norm_num)) hKB
      _ = B * (5 / 4) := by ring
  have hLm1 : L ^ (-(1 : ℝ)) * L ^ ε = L ^ (-(1 - ε)) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  calc (badNonSingletonCount x : ℝ)
      ≤ B * (5 / 4) := htot
    _ ≤ B * L ^ ε := mul_le_mul_of_nonneg_left h54x hB_nn
    _ = (badSingletonCount x : ℝ) * (L ^ (-(1 : ℝ)) * L ^ ε) := by
        rw [hBdef]; ring
    _ = (badSingletonCount x : ℝ) * L ^ (-(1 - ε)) := by rw [hLm1]
    _ = L ^ (-(1 - ε)) * badSingletonCount x := by ring

/-- **Ratio-form closure with a `log log`-factor slack.**

If eventually `runCountSum x ≤ S·(log x)^{-1}·(log log x)^K / 8` for some fixed
`K ≥ 0`, the residual holds.  Proof: the same absorption gives
`N ≤ (5/4)·S·L^{-1}·(log log x)^K ≤ S·L^{-1}·(log log x)^{K+1}` eventually,
then `Assembly.badNonSingleton_interval_bound_of_loglog_factor`. -/
theorem badNonSingleton_interval_bound_of_runCountSum_ratio_loglog
    (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K / 8) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  apply badNonSingleton_interval_bound_of_loglog_factor (K + 1)
  obtain ⟨C, _hCpos, hS⟩ := SingletonLBz.badSingletonCount_eventually_ge_zscale
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hCst := eventually_const_le_exp_neg_mul_log_inv
    ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) C
  have hll : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLt
  have h54 : ∀ᶠ x : ℕ in atTop, (5 / 4 : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
    hll.eventually_ge_atTop (5 / 4)
  filter_upwards [h, hS, hCst, h54, hLt.eventually_ge_atTop 1,
    hll.eventually_ge_atTop 1]
    with x hx hSx hCx h54x hL1 hll1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  have hllpos : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := by linarith
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  set F := (badSingletonCount x : ℝ) * L ^ (-(1 : ℝ)) with hFdef
  have hF_nn : (0 : ℝ) ≤ F :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  have hg1 : (1 : ℝ) ≤ Real.log L ^ K := Real.one_le_rpow hll1 hK
  -- `2·10^16+1 ≤ x·e^{-C·s}·L^{-1} ≤ F ≤ F·(log log x)^K`.
  have hKF : ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ F * Real.log L ^ K := by
    have h1 : (x : ℝ) * Real.exp (-C * s) * L ^ (-(1 : ℝ)) ≤ F :=
      mul_le_mul_of_nonneg_right hSx (Real.rpow_nonneg hL.le _)
    have h2 : ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ F := hCx.trans h1
    calc ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ F * 1 := by rw [mul_one]; exact h2
      _ ≤ F * Real.log L ^ K := mul_le_mul_of_nonneg_left hg1 hF_nn
  have hNle : (badNonSingletonCount x : ℝ) ≤
      2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_two_mul_runCountSum_add_const x
  have htot : (badNonSingletonCount x : ℝ) ≤
      F * Real.log L ^ K * (5 / 4) := by
    calc (badNonSingletonCount x : ℝ)
        ≤ 2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := hNle
      _ ≤ 2 * (F * Real.log L ^ K / 8) + F * Real.log L ^ K :=
          add_le_add (mul_le_mul_of_nonneg_left hx (by norm_num)) hKF
      _ = F * Real.log L ^ K * (5 / 4) := by ring
  calc (badNonSingletonCount x : ℝ)
      ≤ F * Real.log L ^ K * (5 / 4) := htot
    _ ≤ F * Real.log L ^ K * Real.log L :=
        mul_le_mul_of_nonneg_left h54x
          (mul_nonneg hF_nn (Real.rpow_nonneg hllpos.le _))
    _ = F * (Real.log L ^ K * Real.log L ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
    _ = F * Real.log L ^ (K + 1) := by rw [← Real.rpow_add hllpos]
    _ = (badSingletonCount x : ℝ) * L ^ (-(1 : ℝ)) *
          Real.log L ^ (K + 1) := by rw [hFdef]; ring

end JSP314
