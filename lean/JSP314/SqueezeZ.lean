import JSP314.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# JSP-000314 — z-scale squeeze for `badNonSingleton_interval_bound`

The power-saving squeeze in `Squeeze2` cannot close the residual: the true
non-singleton count `N(x)` is `x^{1−o(1)}` (of order
`x·exp(−2√2·√(log x·log log x))`), not `O(x^{1−δ})` for a fixed `δ`.
The correct comparison is at the sub-polynomial scale
`z(x) = exp(√(log x·log log x))`:

* singleton lower bound: `S(x) ≥ x·exp(−C_S·√(log x·log log x))`;
* non-singleton upper bound:
  `N(x) ≤ x·exp(−C_N·√(log x·log log x))·(log x)^{−(1−ε)}` with `C_N > C_S`.

Then `N(x)/S(x) ≤ exp(−(C_N−C_S)·√(LL₂))·(log x)^{−(1−ε)}`, and
`exp(−δ·√(LL₂))` decays faster than every fixed power of `log x`, so the
ratio is `≤ (log x)^{−(1−ε)}` eventually.
-/

namespace JSP314

open Filter Topology

/-- `√(log x · log log x) → ∞` along `ℕ`. -/
theorem tendsto_sqrt_ll_atTop :
    Tendsto
      (fun x : ℕ =>
        Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))))
      atTop atTop := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLt
  have hmono : ∀ᶠ x : ℕ in atTop,
      Real.sqrt (Real.log (x : ℝ)) ≤
        Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) := by
    filter_upwards [hLt.eventually_ge_atTop 0,
      hL2t.eventually_ge_atTop 1] with x hL hx2
    exact Real.sqrt_le_sqrt (le_mul_of_one_le_right hL hx2)
  exact tendsto_atTop_mono' atTop hmono (Real.tendsto_sqrt_atTop.comp hLt)

/-- `exp(−δ·√(log x·log log x))·(log x)^γ → 0` for `δ > 0`:
sub-polynomial exponential decay beats every power of `log x`. -/
theorem tendsto_exp_neg_sqrt_ll_mul_log_pow (δ γ : ℝ) (hδ : 0 < δ) :
    Tendsto
      (fun x : ℕ =>
        Real.exp (-δ * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ))))
          * (Real.log x) ^ γ)
      atTop (nhds 0) := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLt
  have hsqrt := tendsto_sqrt_ll_atTop
  have hratio : Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hLt).tendsto_div_nhds_zero
  -- Step A: `exp(−(δ/2)·√(LL₂)) → 0`.
  have hneg : Tendsto
      (fun x : ℕ =>
        -(δ / 2) * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
      atTop atBot :=
    (tendsto_const_mul_atBot_of_neg
      (neg_neg_of_pos (half_pos hδ))).mpr hsqrt
  have hsmall : Tendsto
      (fun x : ℕ =>
        Real.exp (-(δ / 2) * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  -- Step B: eventually `γ·L₂ ≤ (δ/2)·√(L·L₂)`.
  have hγ : ∀ᶠ x : ℕ in atTop,
      γ * Real.log (Real.log (x : ℝ)) ≤
        (δ / 2) * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))) := by
    by_cases hγ0 : γ ≤ 0
    · filter_upwards [hL2t.eventually_ge_atTop 0] with x hx2
      exact (mul_nonpos_of_nonpos_of_nonneg hγ0 hx2).trans
        (mul_nonneg (half_pos hδ).le (Real.sqrt_nonneg _))
    · push Not at hγ0
      have hC : (0 : ℝ) < δ ^ 2 / (4 * γ ^ 2) :=
        div_pos (sq_pos_of_pos hδ)
          (mul_pos (by norm_num) (sq_pos_of_pos hγ0))
      filter_upwards [hratio.eventually (Iio_mem_nhds hC),
        hLt.eventually_ge_atTop 1,
        hL2t.eventually_ge_atTop 0] with x hx hxL hx2
      have hLpos : 0 < Real.log (x : ℝ) :=
        lt_of_lt_of_le (by norm_num) hxL
      -- `4γ²·L₂ ≤ δ²·L` from `L₂/L ≤ δ²/(4γ²)`:
      have h4 : 4 * γ ^ 2 * Real.log (Real.log (x : ℝ)) ≤
          δ ^ 2 * Real.log (x : ℝ) := by
        have h := (div_le_iff₀ hLpos).mp hx.le
        have h42 : (0 : ℝ) < 4 * γ ^ 2 :=
          mul_pos (by norm_num) (sq_pos_of_pos hγ0)
        calc 4 * γ ^ 2 * Real.log (Real.log (x : ℝ))
            ≤ 4 * γ ^ 2 * (δ ^ 2 / (4 * γ ^ 2) * Real.log (x : ℝ)) :=
          mul_le_mul_of_nonneg_left h h42.le
          _ = δ ^ 2 * Real.log (x : ℝ) := by
            field_simp
      -- `(2γ·L₂)² ≤ δ²·(L·L₂)`:
      have h5 : (2 * γ * Real.log (Real.log (x : ℝ))) ^ 2 ≤
          δ ^ 2 * (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) := by
        have h := mul_le_mul_of_nonneg_right h4 hx2
        nlinarith [h]
      -- take square roots: `2γ·L₂ ≤ δ·√(L·L₂)`:
      have h2γ : 2 * γ * Real.log (Real.log (x : ℝ)) ≤
          δ * Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) := by
        have hl : Real.sqrt ((2 * γ * Real.log (Real.log (x : ℝ))) ^ 2) =
            2 * γ * Real.log (Real.log (x : ℝ)) :=
          Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) hγ0.le) hx2)
        have hr : Real.sqrt
            (δ ^ 2 * (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)))) =
            δ * Real.sqrt (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ))) := by
          rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
        have := Real.sqrt_le_sqrt h5
        rwa [hl, hr] at this
      linarith
  -- Step C: `exp(−δ√)·L^γ ≤ exp(−(δ/2)·√)` eventually.
  have hbound : ∀ᶠ x : ℕ in atTop,
      Real.exp (-δ * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ γ ≤
        Real.exp (-(δ / 2) * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) := by
    filter_upwards [hγ, hLt.eventually_ge_atTop 1] with x hxγ hx1
    have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hx1
    rw [Real.rpow_def_of_pos hLpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hxγ
    nlinarith [hxγ]
  have hnonneg : ∀ᶠ x : ℕ in atTop,
      (0 : ℝ) ≤ Real.exp (-δ * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ γ := by
    filter_upwards [hLt.eventually_ge_atTop 0] with x hx
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsmall hnonneg hbound

/-- **The z-scale squeeze.**  From `S ≥ x·exp(−C_S·√(LL₂))` and
`N ≤ x·exp(−C_N·√(LL₂))·(log x)^{−(1−ε)}` with `C_N > C_S`, conclude
`badNonSingleton_interval_bound`'s statement. -/
theorem badNonSingleton_interval_bound_of_zscale {CS CN : ℝ}
    (hgap : CS < CN)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-CS * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
        ≤ badSingletonCount x)
    (hN : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ))))
          * (Real.log x) ^ (-(1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  set δ := CN - CS with hδdef
  have hδ : 0 < δ := sub_pos.mpr hgap
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `exp(−δ√)·L^{ε/2} < 1` eventually.
  have ht := tendsto_exp_neg_sqrt_ll_mul_log_pow δ (ε / 2) hδ
  have ht1 : ∀ᶠ x : ℕ in atTop,
      Real.exp (-δ * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε / 2) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht1, hS, hN (ε / 2) (half_pos hε), eventually_ge_atTop 3,
    hLt.eventually_ge_atTop 1]
    with x h1 hSx hNx hx3 hL1
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  -- split `exp(−CN·s) = exp(−CS·s)·exp(−δ·s)`
  have hsplit : Real.exp (-CN * s) =
      Real.exp (-CS * s) * Real.exp (-δ * s) := by
    rw [← Real.exp_add]
    congr 1
    have : CN = CS + δ := by linarith [hδdef]
    rw [this]
    ring
  -- `exp(−δ·s)·L^{−(1−ε/2)} ≤ L^{−(1−ε)}`:
  have hle1 : Real.exp (-δ * s) * L ^ (-(1 - ε / 2)) ≤ L ^ (-(1 - ε)) := by
    have hLp : L ^ (-(1 - ε / 2)) = L ^ (ε / 2) * L ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    rw [hLp]
    calc Real.exp (-δ * s) * (L ^ (ε / 2) * L ^ (-(1 : ℝ)))
        = (Real.exp (-δ * s) * L ^ (ε / 2)) * L ^ (-(1 : ℝ)) := by ring
      _ ≤ 1 * L ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hLpos.le _)
      _ ≤ L ^ (-(1 - ε)) := by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  calc (badNonSingletonCount x : ℝ)
      ≤ x * Real.exp (-CN * s) * L ^ (-(1 - ε / 2)) := hNx
    _ = (x * Real.exp (-CS * s)) * (Real.exp (-δ * s) * L ^ (-(1 - ε / 2))) := by
        rw [hsplit]; ring
    _ ≤ (x * Real.exp (-CS * s)) * L ^ (-(1 - ε)) :=
        mul_le_mul_of_nonneg_left hle1
          (mul_nonneg hxpos.le (Real.exp_pos _).le)
    _ = L ^ (-(1 - ε)) * (x * Real.exp (-CS * s)) := by ring
    _ ≤ L ^ (-(1 - ε)) * badSingletonCount x :=
        mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hLpos.le _)

end JSP314
