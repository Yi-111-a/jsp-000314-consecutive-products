import JSP314.SqueezeZ

/-!
# JSP-000314 — alternative sufficient hypotheses for `badNonSingleton_interval_bound`

This file assembles **more flexible** sufficient conditions for the single
remaining analytic placeholder `badNonSingleton_interval_bound`
(`JSP314/Main.lean`).  Everything here is a filter/`rpow` manipulation in the
spirit of `JSP314/SqueezeZ.lean`; no new mathematical input is assumed.

Variants provided (each concludes the full statement of
`badNonSingleton_interval_bound`):

* `badNonSingleton_interval_bound_of_sameExp_log_slack` — **same-exponent
  log-slack squeeze**.  Both sides share the *same* sub-polynomial exponential
  factor `exp(−C·√(L·L₂))` (no strict gap `C_N > C_S` needed, unlike
  `SqueezeZ.badNonSingleton_interval_bound_of_zscale`); the saving comes from a
  strict gain in the logarithmic power: `S ≥ x·e^{−C·s}·L^{−A}` and
  `N ≤ x·e^{−C·s}·L^{−(1+δ)}` with `δ > A`.

* `badNonSingleton_interval_bound_of_loglog_factor` — **ratio squeeze with a
  `log log` factor, fixed `K`**: `N ≤ S·(log x)^{−1}·(log log x)^K`.

* `badNonSingleton_interval_bound_of_loglog_ratio_allK` — **ratio squeeze, all
  `K`**: `∀ K, N ≤ (log x)^{−1}·(log log x)^K·S` eventually (instantiating
  `K = 0` already suffices).

* `badNonSingleton_interval_bound_of_rpow_slack` — **power-of-log slack**:
  `∃ A > 1, N ≤ S·(log x)^{−A}`.

The key analytic input for the `log log` variants is
`Real.isLittleO_log_rpow_rpow_atTop`, which absorbs `(log log x)^K` into any
positive power of `log x` (`loglog_rpow_le_log_rpow`).
-/

namespace JSP314

open Filter Topology

/-- `(log log x)^K ≤ (log x)^ε` eventually, for any `K : ℝ` and any `ε > 0`:
every fixed real power of `log log` is absorbed by every positive power of
`log`.  This is `isLittleO_log_rpow_rpow_atTop` composed with
`log x → ∞`, evaluated at constant `1`. -/
theorem loglog_rpow_le_log_rpow (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (Real.log (x : ℝ))) ^ K ≤ (Real.log (x : ℝ)) ^ ε := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLt
  have hb := ((isLittleO_log_rpow_rpow_atTop K hε).comp_tendsto hLt).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, hLt.eventually_ge_atTop 0,
    hL2t.eventually_ge_atTop 0] with x hx hL0 hL20
  simp only [Function.comp_apply] at hx
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg hL20 _),
    Real.norm_of_nonneg (Real.rpow_nonneg hL0 _), one_mul] at hx

/-- **Variant (1): same-exponent log-slack squeeze.**

From a singleton lower bound and non-singleton upper bound sharing the *same*
sub-polynomial factor `exp(−C·√(L·L₂))` (no strict constant gap required —
this is the point of flexibility over
`badNonSingleton_interval_bound_of_zscale`), but with a strict gain in the
log-power, `N/S ≤ (log x)^{−(1+δ−A)} ≤ (log x)^{−1+ε}` eventually since
`δ > A`. -/
theorem badNonSingleton_interval_bound_of_sameExp_log_slack
    {C A δ : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hδ : A < δ)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-A)
        ≤ badSingletonCount x)
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-(1 + δ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hS, hN, hLt.eventually_ge_atTop 1] with x hSx hNx hL1
  set L := Real.log (x : ℝ) with hLdef
  set s := Real.sqrt (L * Real.log L) with hsdef
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  -- `L^{-(1+δ)} = L^{-A} · L^{-(1+δ-A)}`: peel the `L^{-A}` off the upper bound.
  have hsplit : L ^ (-(1 + δ)) = L ^ (-A) * L ^ (-(1 + δ - A)) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  -- `-(1+δ-A) ≤ -(1-ε)` since `δ > A` and `ε > 0`.
  have hpow : L ^ (-(1 + δ - A)) ≤ L ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  calc (badNonSingletonCount x : ℝ)
      ≤ (x : ℝ) * Real.exp (-C * s) * L ^ (-(1 + δ)) := hNx
    _ = L ^ (-(1 + δ - A)) * ((x : ℝ) * Real.exp (-C * s) * L ^ (-A)) := by
        rw [hsplit]; ring
    _ ≤ L ^ (-(1 + δ - A)) * badSingletonCount x :=
        mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hLpos.le _)
    _ ≤ L ^ (-(1 - ε)) * badSingletonCount x :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)

/-- **Variant (2a): ratio squeeze with a `log log` factor, fixed `K`.**

From `N ≤ S·(log x)^{-1}·(log log x)^K` (one fixed real `K`), conclude the
residual: `(log log x)^K ≤ (log x)^ε` eventually, so
`N ≤ S·(log x)^{-1+ε}`. -/
theorem badNonSingleton_interval_bound_of_loglog_factor (K : ℝ)
    (h : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := loglog_rpow_le_log_rpow K ε hε
  filter_upwards [h, hll, hLt.eventually_ge_atTop 1] with x hx hxll hL1
  set L := Real.log (x : ℝ) with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
  have hSp : (0 : ℝ) ≤ badSingletonCount x := Nat.cast_nonneg _
  have hL1nn : 0 ≤ L ^ (-(1 : ℝ)) := Real.rpow_nonneg hLpos.le _
  calc (badNonSingletonCount x : ℝ)
      ≤ (badSingletonCount x : ℝ) * L ^ (-(1 : ℝ)) * Real.log L ^ K := hx
    _ ≤ (badSingletonCount x : ℝ) * L ^ (-(1 : ℝ)) * L ^ ε :=
        mul_le_mul_of_nonneg_left hxll (mul_nonneg hSp hL1nn)
    _ = (badSingletonCount x : ℝ) * (L ^ (-(1 : ℝ)) * L ^ ε) := by ring
    _ = (badSingletonCount x : ℝ) * L ^ (-(1 - ε)) := by
        rw [← Real.rpow_add hLpos]; congr 1; ring
    _ = L ^ (-(1 - ε)) * badSingletonCount x := by ring

/-- **Variant (2b): ratio squeeze, all `K`.**

From `∀ K, N ≤ (log x)^{-1}·(log log x)^K·S` eventually, conclude the
residual.  (Only `K = 0` is needed: `(log log x)^0 = 1` and
`(log x)^{-1} ≤ (log x)^{-1+ε}` once `log x ≥ 1`.) -/
theorem badNonSingleton_interval_bound_of_loglog_ratio_allK
    (h : ∀ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ K *
          (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h 0, hLt.eventually_ge_atTop 1] with x hx hL1
  have hSp : (0 : ℝ) ≤ badSingletonCount x := Nat.cast_nonneg _
  simp only [Real.rpow_zero, mul_one] at hx
  have hpow : (Real.log (x : ℝ)) ^ (-(1 : ℝ)) ≤
      (Real.log (x : ℝ)) ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  exact hx.trans (mul_le_mul_of_nonneg_right hpow hSp)

/-- **Variant (3): power-of-log slack.**

From `∃ A > 1, N ≤ S·(log x)^{-A}` eventually, conclude the residual: since
`-A < -1 ≤ -(1-ε)`, `(log x)^{-A} ≤ (log x)^{-1+ε}` once `log x ≥ 1`. -/
theorem badNonSingleton_interval_bound_of_rpow_slack
    (h : ∃ A : ℝ, 1 < A ∧ ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-A)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨A, hA, hN⟩ := h
  intro ε hε
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hN, hLt.eventually_ge_atTop 1] with x hx hL1
  have hSp : (0 : ℝ) ≤ badSingletonCount x := Nat.cast_nonneg _
  have hpow : (Real.log (x : ℝ)) ^ (-A) ≤ (Real.log (x : ℝ)) ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  calc (badNonSingletonCount x : ℝ)
      ≤ (badSingletonCount x : ℝ) * (Real.log (x : ℝ)) ^ (-A) := hx
    _ ≤ (badSingletonCount x : ℝ) * (Real.log (x : ℝ)) ^ (-(1 - ε)) :=
        mul_le_mul_of_nonneg_left hpow hSp
    _ = (Real.log (x : ℝ)) ^ (-(1 - ε)) * badSingletonCount x := by ring

end JSP314
