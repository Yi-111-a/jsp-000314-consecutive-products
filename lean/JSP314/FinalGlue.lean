import JSP314.SqueezeZ
import JSP314.SingletonLBz
import JSP314.SmoothLB4
import Mathlib.Tactic

/-!
# JSP-000314 — final glue for `badNonSingleton_interval_bound`

This file closes the *real-analysis* part of the residual
`badNonSingleton_interval_bound` (`JSP314/Main.lean`) at the `z`-scale
`s(x) = √(L·L₂)`, `L = log x`, `L₂ = log log x`.  Everything here is a
filter/`exp`/`rpow` manipulation; no new mathematical input is assumed.

## The squeeze

* `hS` (singleton lower bound, **proved** in this repo):
  `S(x) ≥ x·exp(−C_S·s)` — best available constant `C_S > 2√2`
  (`SmoothLB4.badSingletonCount_eventually_ge_zscale_two`; a weaker `C = 10`
  version is `SingletonLBz.badSingletonCount_eventually_ge_zscale`).
* `hN` (non-singleton upper bound, **the remaining hypothesis**):
  `N(x) ≤ x·exp(−C_N·s)·(log x)^{-(1-ε)}` with `C_N > C_S`.

Then `N(x)/S(x) ≤ exp(−(C_N−C_S)·s)·(log x)^{-(1-ε)}`, and the factor
`exp(−δ·s)` (`δ = C_N−C_S > 0`) decays faster than *every* fixed power of
`log x` (`SqueezeZ.tendsto_exp_neg_sqrt_ll_mul_log_pow`), so it is `< 1`
eventually and `N(x) ≤ (log x)^{-(1-ε')}·S(x)` for **any** `ε'` — the
exponential gap absorbs the difference between the two log-powers
completely, so even a *single* `ε` on the `hN` side yields every `ε'` on
the conclusion side.

## Contents

* `badNonSingleton_le_log_pow_mul_singleton_of_exp_gap` — the general glue:
  one-shot eventual bound, arbitrary exponents `ε`, `ε'`.
* `badNonSingleton_interval_bound_of_exp_gap` — `Main.lean`-shaped
  conclusion `∀ ε > 0, ∀ᶠ x, N ≤ (log x)^{-(1-ε)}·S` from `hN` quantified
  over all `ε` (the `SqueezeZ` hypothesis shape).
* `badNonSingleton_interval_bound_of_exp_gap_single` — the same conclusion
  from `hN` at a *single* exponent `ε₀`.
* `badNonSingleton_bound_of_hN` — `hN` is the **only** hypothesis left:
  the singleton bound is instantiated from the strongest proved source,
  `SmoothLB4` (every `C_S > 2√2`), so `hN` is only needed at some
  `C_N > 2√2`.
* `badNonSingleton_bound_of_hN_three` — the concrete instance `C_N = 3`.
-/

namespace JSP314

open Filter

/-- `2·√2 < 3` (since `2 < (3/2)² = 9/4`). -/
theorem two_mul_sqrt_two_lt_three : 2 * Real.sqrt 2 < 3 := by
  have h : Real.sqrt 2 < 3 / 2 := by
    have h2 : (2 : ℝ) < (3 / 2) ^ 2 := by norm_num
    have h3 : Real.sqrt 2 < Real.sqrt ((3 / 2 : ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) h2
    rwa [Real.sqrt_sq (by norm_num)] at h3
  linarith

/-- **General glue (one-shot).**

If `S(x) ≥ x·exp(−C_S·s)` and `N(x) ≤ x·exp(−C_N·s)·(log x)^{-(1-ε)}`
eventually, with `C_N > C_S`, then for **any** real `ε'` whatsoever
`N(x) ≤ (log x)^{-(1-ε')}·S(x)` eventually.

Proof: write `exp(−C_N·s) = exp(−C_S·s)·exp(−δ·s)` with `δ = C_N−C_S > 0`.
Since `exp(−δ·s)·(log x)^{ε-ε'} → 0`
(`tendsto_exp_neg_sqrt_ll_mul_log_pow`), it is `< 1` eventually, hence
`exp(−δ·s)·(log x)^{-(1-ε)} = (exp(−δ·s)·(log x)^{ε-ε'})·(log x)^{-(1-ε')}
≤ (log x)^{-(1-ε')}`. -/
theorem badNonSingleton_le_log_pow_mul_singleton_of_exp_gap
    {CS CN ε ε' : ℝ} (hgap : CS < CN)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-CS * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
        ≤ (badSingletonCount x : ℝ))
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε))) :
    ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε')) * (badSingletonCount x : ℝ) := by
  have hδ : 0 < CN - CS := sub_pos.mpr hgap
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `exp(−δ·s)·L^{ε−ε'} → 0`, hence `< 1` eventually.
  have ht := tendsto_exp_neg_sqrt_ll_mul_log_pow (CN - CS) (ε - ε') hδ
  have ht1 : ∀ᶠ x : ℕ in atTop,
      Real.exp (-(CN - CS) * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε - ε') < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht1, hS, hN, hLt.eventually_ge_atTop 1]
    with x h1 hSx hNx hL1
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hxnn : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  -- split `exp(−C_N·s) = exp(−C_S·s)·exp(−δ·s)`.
  have hsplit : Real.exp (-CN * s) =
      Real.exp (-CS * s) * Real.exp (-(CN - CS) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  -- absorb: `exp(−δ·s)·L^{-(1-ε)} ≤ L^{-(1-ε')}`.
  have hle : Real.exp (-(CN - CS) * s) * L ^ (-(1 - ε)) ≤
      L ^ (-(1 - ε')) := by
    have hLp : L ^ (-(1 - ε)) = L ^ (ε - ε') * L ^ (-(1 - ε')) := by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    rw [hLp, ← mul_assoc]
    calc Real.exp (-(CN - CS) * s) * L ^ (ε - ε') * L ^ (-(1 - ε'))
        ≤ 1 * L ^ (-(1 - ε')) :=
          mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hLpos.le _)
      _ = L ^ (-(1 - ε')) := one_mul _
  calc (badNonSingletonCount x : ℝ)
      ≤ x * Real.exp (-CN * s) * L ^ (-(1 - ε)) := hNx
    _ = (x * Real.exp (-CS * s)) *
          (Real.exp (-(CN - CS) * s) * L ^ (-(1 - ε))) := by
        rw [hsplit]; ring
    _ ≤ (x * Real.exp (-CS * s)) * L ^ (-(1 - ε')) :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hxnn (Real.exp_pos _).le)
    _ = L ^ (-(1 - ε')) * (x * Real.exp (-CS * s)) := by ring
    _ ≤ L ^ (-(1 - ε')) * badSingletonCount x :=
        mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hLpos.le _)

/-- **Main.lean-shaped variant, `hN` for all `ε`.**

Same conclusion as `badNonSingleton_interval_bound` (`Main.lean`): for
every `ε > 0`, eventually `N(x) ≤ (log x)^{-(1-ε)}·S(x)`.  The `hN`
hypothesis is the `SqueezeZ` shape: for every `ε > 0`, eventually
`N(x) ≤ x·exp(−C_N·s)·(log x)^{-(1-ε)}`. -/
theorem badNonSingleton_interval_bound_of_exp_gap {CS CN : ℝ}
    (hgap : CS < CN)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-CS * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
        ≤ (badSingletonCount x : ℝ))
    (hN : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  exact badNonSingleton_le_log_pow_mul_singleton_of_exp_gap hgap hS
    (hN ε hε)

/-- **Main.lean-shaped variant, `hN` at a single exponent `ε₀`.**

Because the `exp(−δ·s)` factor beats every power of `log x`, `hN` is only
needed at *one* exponent `ε₀` (any real number — even `ε₀ = 0`, i.e.
`N(x) ≤ x·exp(−C_N·s)/log x`, or `ε₀ = 1`, i.e. `N ≤ x·exp(−C_N·s)`):
the conclusion then holds for every `ε > 0`. -/
theorem badNonSingleton_interval_bound_of_exp_gap_single {CS CN ε₀ : ℝ}
    (hgap : CS < CN)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-CS * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ))))
        ≤ (badSingletonCount x : ℝ))
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε₀))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  exact badNonSingleton_le_log_pow_mul_singleton_of_exp_gap hgap hS hN

/-- **`hN` is the only remaining hypothesis.**

The singleton lower bound is already **proved** in this repository for
every constant `C_S > 2·√2`
(`SmoothLB4.badSingletonCount_eventually_ge_zscale_two`, which compiles;
a strictly weaker `C_S = 10` version is
`SingletonLBz.badSingletonCount_eventually_ge_zscale`).  Hence the
residual `badNonSingleton_interval_bound` follows from `hN` alone at any
single constant `C_N > 2·√2` (with the `∀ ε` eventual bound): pick
`C_S ∈ (2√2, C_N)` via `exists_between` and squeeze. -/
theorem badNonSingleton_bound_of_hN
    (hN : ∃ CN : ℝ, 2 * Real.sqrt 2 < CN ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        (badNonSingletonCount x : ℝ) ≤
          (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
              Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨CN, hCN, hNev⟩ := hN
  obtain ⟨CS, hCSgt, hCSlt⟩ := exists_between hCN
  exact badNonSingleton_interval_bound_of_exp_gap hCSlt
    (SmoothLB4.badSingletonCount_eventually_ge_zscale_two CS hCSgt) hNev

/-- **Concrete instance `C_N = 3`** (since `3 > 2√2`): if for every `ε > 0`
eventually `N(x) ≤ x·exp(−3·s)·(log x)^{-(1-ε)}`, then
`badNonSingleton_interval_bound` holds. -/
theorem badNonSingleton_bound_of_hN_three
    (hN : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-3 * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_bound_of_hN ⟨3, two_mul_sqrt_two_lt_three, hN⟩

/-- **Variant using only `SingletonLBz` (`C_S = 10`, proved and already
imported by the umbrella `JSP314.lean`).**

Same conclusion; `hN` is required at every constant `C_N > 10` (the
witness `C_S` of `SingletonLBz.badSingletonCount_eventually_ge_zscale`
is hidden behind `∃`, so `hN` is quantified over all sufficiently large
constants and instantiated at `max 11 (C_S + 1)`). -/
theorem badNonSingleton_bound_of_hN_const10
    (hN : ∀ CN : ℝ, 10 < CN → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℕ in atTop,
        (badNonSingletonCount x : ℝ) ≤
          (x : ℝ) * Real.exp (-CN * Real.sqrt (Real.log (x : ℝ) *
              Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 - ε))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨CS, -, hS⟩ := SingletonLBz.badSingletonCount_eventually_ge_zscale
  have hCN : (10 : ℝ) < max 11 (CS + 1) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact badNonSingleton_interval_bound_of_exp_gap
    (lt_of_lt_of_le (lt_add_one CS) (le_max_right _ _)) hS (hN _ hCN)

end JSP314
