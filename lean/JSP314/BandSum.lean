import JSP314.RunDecomp
import JSP314.SSBound
import JSP314.SqueezeZ
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# JSP-000314 — band-sum assembler for the `hN` hypothesis of `SqueezeZ`

This file collects the *combinatorial* part of the `N(x)` estimate: the
run-count decomposition of `ShortResidual`/`RunDecomp`/`SSBound` plus the
real-analysis fact that any fixed polynomial saving `x^{1−δ}` is eventually
`≤ x·exp(−c·s)` where `s = √(L·L₂)`, `L = log x`, `L₂ = log log x`.

Contents:

* `runCountSum` — `∑_{p ≤ √(2x)} ∑_{k ≤ 2p} (rightRunCount + leftRunCount)`.
* `badNonSingletonCount_le_two_mul_runCountSum_add_const` —
  `N(x) ≤ 2·runCountSum(x) + (2·10^16 + 1)`.
* `tendsto_sqrt_ll_div_log_atTop` — `s/L → 0`.
* `eventually_rpow_one_sub_mul_log_pow_le_exp_neg` — for `δ > 0` and any
  `c γ`, eventually `x^{1-δ}·(log x)^γ ≤ x·exp(−c·s)`.
* `eventually_const_le_exp_neg_mul_log_inv` — constants are absorbed.
* `hN_of_runCountSum_le` — conditional assembler into the `hN` shape of
  `SqueezeZ.badNonSingleton_interval_bound_of_zscale`.
* `badNonSingleton_interval_bound_of_runCountSum` — the full conditional
  squeeze `hS + runCountSum bound ⇒ residual`.
-/

namespace JSP314

open Filter

/-- The run-count double sum from `RunDecomp.shortBadCount_le_run_sum`. -/
noncomputable def runCountSum (x : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- Total decomposition: `N(x) ≤ 2·runCountSum(x) + (2·10^16+1)` — the short
branch is bounded by the run sum (`RunDecomp`) and the long branch by the
Sylvester–Schur constant (`SSBound`). -/
theorem badNonSingletonCount_le_two_mul_runCountSum_add_const (x : ℕ) :
    badNonSingletonCount x ≤ 2 * runCountSum x + (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_short_add_const x
  have h2 : shortBadCount x ≤ 2 * runCountSum x := shortBadCount_le_run_sum x
  omega

/-- `s/L → 0` along `ℕ`, where `s = √(L·L₂)`. -/
theorem tendsto_sqrt_ll_div_log_atTop :
    Tendsto
      (fun x : ℕ =>
        Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) /
          Real.log (x : ℝ))
      atTop (nhds 0) := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hLt).tendsto_div_nhds_zero
  -- `(s/L)² = L₂/L` pointwise, hence `(s/L)² → 0`.
  have h2 : Tendsto
      (fun x : ℕ =>
        (Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) /
          Real.log (x : ℝ)) ^ 2)
      atTop (nhds 0) := by
    refine hratio.congr' ?_
    filter_upwards [hLt.eventually_ge_atTop 1] with x hx
    have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
    have hL2 : (0 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := Real.log_nonneg hx
    rw [div_pow, Real.sq_sqrt (mul_nonneg hL.le hL2)]
    field_simp
  -- `√` continuity: `√((s/L)²) = s/L → 0`.
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  refine h3.congr' ?_
  filter_upwards [hLt.eventually_ge_atTop 1] with x hx
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  exact Real.sqrt_sq (div_nonneg (Real.sqrt_nonneg _) hL.le)

/-- For `δ > 0` and any `c γ : ℝ`, eventually
`x^{1-δ}·(log x)^γ ≤ x·exp(−c·√(L·L₂))`: a fixed polynomial saving beats any
fixed sub-polynomial (`z`-scale) saving. -/
theorem eventually_rpow_one_sub_mul_log_pow_le_exp_neg (δ γ c : ℝ)
    (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (1 - δ) * (Real.log (x : ℝ)) ^ γ ≤
        (x : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLt
  have hratio : Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hLt).tendsto_div_nhds_zero
  -- `c·s ≤ (δ/3)·L` eventually, from `c·(s/L) → 0`.
  have e1 : ∀ᶠ x : ℕ in atTop,
      c * Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) ≤
        (δ / 3) * Real.log (x : ℝ) := by
    have hc : Tendsto
        (fun x : ℕ =>
          c * (Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) /
            Real.log (x : ℝ)))
        atTop (nhds (c * 0)) :=
      tendsto_sqrt_ll_div_log_atTop.const_mul c
    rw [mul_zero] at hc
    filter_upwards [hc.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < δ/3)),
      hLt.eventually_ge_atTop 1] with x hx hL1
    have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
    have h' := mul_lt_mul_of_pos_right hx hL
    have h'' : c * (Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) /
        Real.log (x : ℝ)) * Real.log (x : ℝ) =
        c * Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) := by
      field_simp
    linarith [h'.le]
  -- `γ·L₂ ≤ (δ/3)·L` eventually, from `γ·(L₂/L) → 0`.
  have e2 : ∀ᶠ x : ℕ in atTop,
      γ * Real.log (Real.log (x : ℝ)) ≤ (δ / 3) * Real.log (x : ℝ) := by
    have hc : Tendsto
        (fun x : ℕ =>
          γ * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)))
        atTop (nhds (γ * 0)) := hratio.const_mul γ
    rw [mul_zero] at hc
    filter_upwards [hc.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < δ/3)),
      hLt.eventually_ge_atTop 1] with x hx hL1
    have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
    have h' := mul_lt_mul_of_pos_right hx hL
    have h'' : γ * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) *
        Real.log (x : ℝ) = γ * Real.log (Real.log (x : ℝ)) := by
      field_simp
    linarith [h'.le]
  filter_upwards [e1, e2, hLt.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x he1 he2 hL1 hx
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  have hδL : (0 : ℝ) ≤ δ * L := mul_nonneg hδ.le hL.le
  have hsum : c * s + γ * Real.log L ≤ δ * L := by linarith
  have hsplit : (x : ℝ) ^ (1 - δ) = (x : ℝ) * (x : ℝ) ^ (-δ) := by
    rw [show (1 : ℝ) - δ = 1 + -δ by ring, Real.rpow_add hxr, Real.rpow_one]
  rw [hsplit]
  have hLγ : (L : ℝ) ^ γ = Real.exp (γ * Real.log L) := by
    rw [Real.rpow_def_of_pos hL, mul_comm (Real.log L) γ]
  have hxδ : (x : ℝ) ^ δ = Real.exp (δ * L) := by
    rw [Real.rpow_def_of_pos hxr, mul_comm L δ]
  have key : (x : ℝ) ^ (-δ) * L ^ γ ≤ Real.exp (-c * s) := by
    have h1 : Real.exp (c * s) * L ^ γ ≤ (x : ℝ) ^ δ := by
      rw [hLγ, hxδ, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hsum
    have hxδpos : (0 : ℝ) < (x : ℝ) ^ δ := Real.rpow_pos_of_pos hxr δ
    rw [Real.rpow_neg hxr.le,
      show Real.exp (-c * s) = (Real.exp (c * s))⁻¹ by
        rw [show -c * s = -(c * s) by ring, Real.exp_neg],
      inv_mul_eq_div, ← one_div,
      div_le_div_iff₀ hxδpos (Real.exp_pos _), one_mul,
      mul_comm (L ^ γ) _]
    exact h1
  calc (x : ℝ) * (x : ℝ) ^ (-δ) * L ^ γ
      = (x : ℝ) * ((x : ℝ) ^ (-δ) * L ^ γ) := by ring
    _ ≤ (x : ℝ) * Real.exp (-c * s) :=
        mul_le_mul_of_nonneg_left key hxr.le

/-- Any constant is eventually `≤ x·exp(−c·s)·(log x)^{-1}`. -/
theorem eventually_const_le_exp_neg_mul_log_inv (C c : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      (C : ℝ) ≤ (x : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 : ℝ)) := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hA := eventually_rpow_one_sub_mul_log_pow_le_exp_neg (1 / 2) 1 c
    (by norm_num)
  have hCx : ∀ᶠ x : ℕ in atTop, (C : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  filter_upwards [hA, hCx, hLt.eventually_ge_atTop 1] with x hA' hC' hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  have hx0 : x ≠ 0 := by
    intro h0
    subst h0
    norm_num at hL1
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hx0
  rw [show (1 - (1 : ℝ) / 2) = 1 / 2 by ring, Real.rpow_one] at hA'
  rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hL]
  calc (C : ℝ) * Real.log (x : ℝ)
      ≤ (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) :=
        mul_le_mul_of_nonneg_right hC' hL.le
    _ ≤ (x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ) *
        Real.log (Real.log (x : ℝ)))) := hA'

/-- **Conditional `hN` assembler.**  If `runCountSum x ≤
x·exp(−C_N·s)·(log x)^{-1}/8` eventually, then the `N`-side hypothesis of
`SqueezeZ.badNonSingleton_interval_bound_of_zscale` holds for `C_N`. -/
theorem hN_of_runCountSum_le {CN : ℝ}
    (h : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        (x : ℝ) *
          Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 : ℝ)) / 8) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) *
          Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε)) := by
  intro ε hε
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC := eventually_const_le_exp_neg_mul_log_inv
    ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) CN
  have hLε : Tendsto (fun x : ℕ => (Real.log (x : ℝ)) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp hLt
  have h54 : ∀ᶠ x : ℕ in atTop, (5 / 4 : ℝ) ≤ (Real.log (x : ℝ)) ^ ε :=
    hLε.eventually_ge_atTop (5 / 4)
  filter_upwards [h, hC, h54, hLt.eventually_ge_atTop 1] with x hx hxC h54x hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  set s := Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)))
    with hsdef
  have hNle : (badNonSingletonCount x : ℝ) ≤
      2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_two_mul_runCountSum_add_const x
  set A := (x : ℝ) * Real.exp (-CN * s) * (Real.log x) ^ (-(1 : ℝ))
    with hAdef
  have hA_nn : (0 : ℝ) ≤ A :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (Real.rpow_nonneg hL.le _)
  have htot : (badNonSingletonCount x : ℝ) ≤ A * (5 / 4) := by
    calc (badNonSingletonCount x : ℝ)
        ≤ 2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := hNle
      _ ≤ 2 * (A / 8) + A := by
          simp only [hAdef, hsdef] at hx hxC ⊢
          linarith
      _ = A * (5 / 4) := by ring
  have hLm1 : (Real.log x) ^ (-(1 : ℝ)) * (Real.log x) ^ ε =
      (Real.log x) ^ (-(1 - ε)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc (badNonSingletonCount x : ℝ)
      ≤ A * (5 / 4) := htot
    _ ≤ A * (Real.log x) ^ ε :=
        mul_le_mul_of_nonneg_left h54x hA_nn
    _ = (x : ℝ) * Real.exp (-CN * s) * ((Real.log x) ^ (-(1 : ℝ)) *
          (Real.log x) ^ ε) := by rw [hAdef]; ring
    _ = (x : ℝ) * Real.exp (-CN * s) * (Real.log x) ^ (-(1 - ε)) := by
        rw [hLm1]

/-- **Full conditional squeeze.**  `hS` (with explicit `C_S`) plus a
`runCountSum` bound at constant `C_N > C_S` imply the residual
`badNonSingleton_interval_bound` statement. -/
theorem badNonSingleton_interval_bound_of_runCountSum {CS CN : ℝ}
    (hgap : CS < CN)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-CS * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
        ≤ badSingletonCount x)
    (h : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤
        (x : ℝ) *
          Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 : ℝ)) / 8) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  exact badNonSingleton_interval_bound_of_zscale hgap hS
    (hN_of_runCountSum_le h) ε hε

end JSP314
