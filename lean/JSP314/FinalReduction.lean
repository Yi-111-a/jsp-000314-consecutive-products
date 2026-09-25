import JSP314.RunDecomp
import JSP314.SSBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# JSP-000314 — Final reduction: the residual as a run-band sum

This file compresses the remaining mathematical content of
`badNonSingleton_interval_bound` (`Main.lean`, the sole unproved placeholder)
into a single named quantity and a single hypothesis shape.

## The residual quantity

`runBandSum x` is the "runs-through-the-witness" bound produced by
`RunDecomp.shortBadCount_le_run_sum`:

```
runBandSum x =
  2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)
```

## The reductions

* `badNonSingletonCount_le_runBandSum` — **pointwise, unconditional**:
  `N(x) ≤ runBandSum x + (2·10^16 + 1)`, obtained by chaining
  `SSBound.badNonSingletonCount_le_short_add_const` with
  `RunDecomp.shortBadCount_le_run_sum`.

* `badNonSingleton_interval_bound_of_runBand` — **master reduction**:
  if `runBandSum x ≤ (log x)^{-(1-ε)}·S(x)` eventually for every `ε > 0`,
  then `N(x) ≤ (log x)^{-(1-ε)}·S(x)` eventually for every `ε > 0`, i.e. the
  full residual `badNonSingleton_interval_bound` follows.  The additive
  constant `2·10^16 + 1` is absorbed because `S(x)·(log x)^{-(1-ε)} → ∞`
  (via `Assault5.badSingletonCount_eventually_ge_log6`, which gives
  `S(x) ≥ c·x^{83/100}/(log x)^6` eventually), and half of the slack is
  peeled off by applying the hypothesis at `ε/2`.

* `badNonSingleton_interval_bound_of_runBand_const_twoMul` — the razor-edge
  shape `N(x) ≤ C·S(2x)·log^{-(1-ε)}x`: a multiplicative constant `C` and a
  factor-`2` slack on the singleton count are both absorbed by the same
  `ε/2`-plus-divergence mechanism (using `badSingletonCount_mono`,
  `S(x) ≤ S(2x)`).

No unproved placeholders, no new axioms.
-/

open Nat Filter Classical

namespace JSP314

/-- The run-band sum: twice the total number of `(p, k)` run witnesses with
`p ≤ √(2x)` prime and `1 ≤ k ≤ 2p`.  This is exactly the bound produced by
`RunDecomp.shortBadCount_le_run_sum`. -/
noncomputable def runBandSum (x : ℕ) : ℕ :=
  2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)

/-- `badSingletonCount` is monotone (the filtered range grows with `x`). -/
theorem badSingletonCount_mono : Monotone badSingletonCount := by
  intro x y hxy
  unfold badSingletonCount
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hn.2⟩

/-- **Pointwise step**: `N(x) ≤ runBandSum x + (2·10^16 + 1)` for every `x`,
chaining the Sylvester–Schur-witness constant bound
(`badNonSingletonCount_le_short_add_const`) with the run decomposition
(`shortBadCount_le_run_sum`). -/
theorem badNonSingletonCount_le_runBandSum (x : ℕ) :
    badNonSingletonCount x ≤ runBandSum x + (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_short_add_const x
  have h2 := shortBadCount_le_run_sum x
  unfold runBandSum
  omega

/-- **Master reduction.**  If `runBandSum x ≤ (log x)^{-(1-ε)}·S(x)`
eventually for every `ε > 0`, then `badNonSingleton_interval_bound` holds.

Proof sketch: apply `H` at `ε/2`.  Eventually `(log x)^{ε/2} ≥ 2`, so
`runBandSum x ≤ (log x)^{-(1-ε/2)}·S(x) = (log x)^{ε/2}·(log x)^{-(1-ε)}·S(x)
·(log x)^{-ε/2} ≤ (1/2)·(log x)^{-(1-ε)}·S(x)`.  Meanwhile
`(log x)^{-(1-ε)}·S(x) ≥ c·x^{83/100}·(log x)^{-(7-ε)} → ∞`, so eventually it
exceeds `2·(2·10^16+1)`, absorbing the constant term. -/
theorem badNonSingleton_interval_bound_of_runBand
    (H : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandSum x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  obtain ⟨c, hc, hS⟩ := badSingletonCount_eventually_ge_log6
  have hLt : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `(log x)^{ε/2} → ∞`, hence `≥ 2` eventually.
  have hLp : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp hLt
  have hL2 : ∀ᶠ x : ℕ in atTop, (2 : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    hLp.eventually_ge_atTop 2
  -- `K·x^{-83/100}·(log x)^{7-ε} → 0` for `K = 2·(2·10^16+1)/c`, hence `< 1`
  -- eventually; multiplied by `c·x^{83/100}·(log x)^{-(7-ε)} > 0` this gives
  -- `2·(2·10^16+1) ≤ c·x^{83/100}·(log x)^{-(7-ε)}`.
  have ht : Tendsto
      (fun n : ℕ =>
        (2 * (2 * 10 ^ 16 + 1) / c) *
          ((n : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log n) ^ (7 - ε)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_neg_mul_log_pow (83 / 100) (7 - ε) (by norm_num)).const_mul
        (2 * (2 * 10 ^ 16 + 1) / c)
  have ht1 : ∀ᶠ x : ℕ in atTop,
      (2 * (2 * 10 ^ 16 + 1) / c) *
        ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log x) ^ (7 - ε)) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [H (ε / 2) (half_pos hε), hL2, hS, ht1,
    eventually_ge_atTop 2] with x hx hLp2 hSx hC hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxp : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLpow : 0 < Real.log (x : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hL _
  -- `(log x)^{-(1-ε/2)} = (log x)^{-(1-ε)}/(log x)^{ε/2}`.
  have hsplit : Real.log (x : ℝ) ^ (-(1 - ε / 2))
      = Real.log (x : ℝ) ^ (-(1 - ε)) / Real.log (x : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_sub hL]
    congr 1
    ring
  -- Hence `(log x)^{-(1-ε/2)}·S ≤ (1/2)·(log x)^{-(1-ε)}·S`.
  have hterm : Real.log (x : ℝ) ^ (-(1 - ε / 2)) * (badSingletonCount x : ℝ)
      ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount x : ℝ)) := by
    rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ hLpow]
    have hA : (0 : ℝ) ≤ Real.log (x : ℝ) ^ (-(1 - ε)) *
        (badSingletonCount x : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hL.le _) (Nat.cast_nonneg _)
    calc Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)
        = (Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) * 1 := by
          ring
      _ ≤ (Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) *
            (Real.log (x : ℝ) ^ (ε / 2) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hA
      _ = (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (badSingletonCount x : ℝ)) * Real.log (x : ℝ) ^ (ε / 2) := by
          ring
  -- Constant absorption: `2·(2·10^16+1) ≤ (log x)^{-(1-ε)}·S(x)`.
  have hCabs : (2 * 10 ^ 16 + 1 : ℝ) ≤
      (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
        (badSingletonCount x : ℝ)) := by
    have hpos : 0 < c * (x : ℝ) ^ (83 / 100 : ℝ) *
        Real.log (x : ℝ) ^ (-(7 - ε)) :=
      mul_pos (mul_pos hc (Real.rpow_pos_of_pos hxp _))
        (Real.rpow_pos_of_pos hL _)
    have hle : 2 * (2 * 10 ^ 16 + 1 : ℝ) ≤
        c * (x : ℝ) ^ (83 / 100 : ℝ) * Real.log (x : ℝ) ^ (-(7 - ε)) := by
      have hle' := mul_le_mul_of_nonneg_right hC.le hpos.le
      rw [one_mul] at hle'
      have hX : (x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ) = 1 := by
        rw [← Real.rpow_add hxp,
          show (-(83 / 100 : ℝ)) + 83 / 100 = 0 by ring, Real.rpow_zero]
      have hL2 : Real.log (x : ℝ) ^ (7 - ε) *
          Real.log (x : ℝ) ^ (-(7 - ε)) = 1 := by
        rw [← Real.rpow_add hL, show (7 - ε) + -(7 - ε) = (0 : ℝ) by ring,
          Real.rpow_zero]
      have e : (2 * (2 * 10 ^ 16 + 1) / c) *
            ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (7 - ε))
            * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
              Real.log (x : ℝ) ^ (-(7 - ε)))
          = 2 * (2 * 10 ^ 16 + 1) := by
        calc (2 * (2 * 10 ^ 16 + 1) / c) *
              ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (7 - ε))
              * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
                Real.log (x : ℝ) ^ (-(7 - ε)))
            = (2 * (2 * 10 ^ 16 + 1) / c * c) *
                ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ)) *
                (Real.log (x : ℝ) ^ (7 - ε) *
                  Real.log (x : ℝ) ^ (-(7 - ε))) := by
              ring
          _ = (2 * (2 * 10 ^ 16 + 1) / c * c) * 1 * 1 := by rw [hX, hL2]
          _ = 2 * (2 * 10 ^ 16 + 1) := by
              rw [mul_one, mul_one, div_mul_cancel₀ _ hc.ne']
      rwa [e] at hle'
    -- `(log x)^{-(1-ε)}·(c·x^{83/100}/(log x)^6) = c·x^{83/100}·(log x)^{-(7-ε)}`.
    have hR : (Real.log x) ^ (-(1 - ε)) *
          (c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6)
        = c * (x : ℝ) ^ (83 / 100 : ℝ) * (Real.log x) ^ (-(7 - ε)) := by
      have e : (Real.log x) ^ (-(7 - ε))
          = (Real.log x) ^ (-(1 - ε)) / (Real.log x) ^ 6 := by
        rw [← Real.rpow_natCast (Real.log x) 6, ← Real.rpow_sub hL]
        congr 1
        ring
      rw [e, ← mul_div_assoc, ← mul_div_assoc]
      ring
    calc (2 * 10 ^ 16 + 1 : ℝ)
        ≤ (1 / 2) * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
            Real.log (x : ℝ) ^ (-(7 - ε))) := by linarith
      _ = (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6)) := by rw [hR]
      _ ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (badSingletonCount x : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hL.le _))
            (by norm_num)
  -- Combine: `N(x) ≤ runBandSum x + C ≤ (1/2)T + (1/2)T = T`.
  have hN : (badNonSingletonCount x : ℝ) ≤
      (runBandSum x : ℝ) + (2 * 10 ^ 16 + 1 : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_runBandSum x
  calc (badNonSingletonCount x : ℝ)
      ≤ (runBandSum x : ℝ) + (2 * 10 ^ 16 + 1 : ℝ) := hN
    _ ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount x : ℝ))
        + (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount x : ℝ)) :=
        add_le_add (le_trans hx hterm) hCabs
    _ = Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by ring

/-- **Razor-edge variant**: if `runBandSum x ≤ C·(log x)^{-(1-ε)}·S(2x)`
eventually for every `ε > 0` — with an arbitrary multiplicative constant `C`
and the factor-`2` slack on the singleton count — then
`N(x) ≤ (log x)^{-(1-ε)}·S(2x)` eventually for every `ε > 0`.  Both `C` and
the additive constant `2·10^16+1` are absorbed because
`(log x)^{-(1-ε)}·S(2x) ≥ (log x)^{-(1-ε)}·S(x) → ∞`. -/
theorem badNonSingleton_interval_bound_of_runBand_const_twoMul
    (C : ℝ)
    (H : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandSum x : ℝ) ≤
        C * ((Real.log x) ^ (-(1 - ε)) * (badSingletonCount (2 * x) : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount (2 * x) : ℝ) := by
  intro ε hε
  obtain ⟨c, hc, hS⟩ := badSingletonCount_eventually_ge_log6
  have hLt : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- `(log x)^{ε/2} → ∞`, hence `≥ max 2 (2C)` eventually.
  have hLp : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp hLt
  have hL2 : ∀ᶠ x : ℕ in atTop,
      (max 2 (2 * C) : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    hLp.eventually_ge_atTop (max 2 (2 * C))
  have ht : Tendsto
      (fun n : ℕ =>
        (2 * (2 * 10 ^ 16 + 1) / c) *
          ((n : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log n) ^ (7 - ε)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_neg_mul_log_pow (83 / 100) (7 - ε) (by norm_num)).const_mul
        (2 * (2 * 10 ^ 16 + 1) / c)
  have ht1 : ∀ᶠ x : ℕ in atTop,
      (2 * (2 * 10 ^ 16 + 1) / c) *
        ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log x) ^ (7 - ε)) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [H (ε / 2) (half_pos hε), hL2, hS, ht1,
    eventually_ge_atTop 2] with x hx hLp2 hSx hC hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxp : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLpow : 0 < Real.log (x : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hL _
  have hB2C : 2 * C ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    le_trans (le_max_right _ _) hLp2
  -- `S(x) ≤ S(2x)` transports the lower bound.
  have hSx2 : c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6 ≤
      (badSingletonCount (2 * x) : ℝ) :=
    le_trans hSx (by exact_mod_cast badSingletonCount_mono (Nat.le_mul_of_pos_left x (by norm_num : 0 < 2)))
  have hsplit : Real.log (x : ℝ) ^ (-(1 - ε / 2))
      = Real.log (x : ℝ) ^ (-(1 - ε)) / Real.log (x : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_sub hL]
    congr 1
    ring
  -- `C·(log x)^{-(1-ε/2)}·S(2x) ≤ (1/2)·(log x)^{-(1-ε)}·S(2x)`.
  have hterm : C * (Real.log (x : ℝ) ^ (-(1 - ε / 2)) *
        (badSingletonCount (2 * x) : ℝ))
      ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)) := by
    rw [hsplit]
    have hrw : C * (Real.log (x : ℝ) ^ (-(1 - ε)) / Real.log (x : ℝ) ^ (ε / 2) *
          (badSingletonCount (2 * x) : ℝ))
        = C * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (badSingletonCount (2 * x) : ℝ)) / Real.log (x : ℝ) ^ (ε / 2) := by
      ring
    rw [hrw, div_le_iff₀ hLpow]
    have hA : (0 : ℝ) ≤ Real.log (x : ℝ) ^ (-(1 - ε)) *
        (badSingletonCount (2 * x) : ℝ) :=
      mul_nonneg (Real.rpow_nonneg hL.le _) (Nat.cast_nonneg _)
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hB2C)]
  -- Constant absorption, identical to the master reduction.
  have hCabs : (2 * 10 ^ 16 + 1 : ℝ) ≤
      (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
        (badSingletonCount (2 * x) : ℝ)) := by
    have hpos : 0 < c * (x : ℝ) ^ (83 / 100 : ℝ) *
        Real.log (x : ℝ) ^ (-(7 - ε)) :=
      mul_pos (mul_pos hc (Real.rpow_pos_of_pos hxp _))
        (Real.rpow_pos_of_pos hL _)
    have hle : 2 * (2 * 10 ^ 16 + 1 : ℝ) ≤
        c * (x : ℝ) ^ (83 / 100 : ℝ) * Real.log (x : ℝ) ^ (-(7 - ε)) := by
      have hle' := mul_le_mul_of_nonneg_right hC.le hpos.le
      rw [one_mul] at hle'
      have hX : (x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ) = 1 := by
        rw [← Real.rpow_add hxp,
          show (-(83 / 100 : ℝ)) + 83 / 100 = 0 by ring, Real.rpow_zero]
      have hL2' : Real.log (x : ℝ) ^ (7 - ε) *
          Real.log (x : ℝ) ^ (-(7 - ε)) = 1 := by
        rw [← Real.rpow_add hL, show (7 - ε) + -(7 - ε) = (0 : ℝ) by ring,
          Real.rpow_zero]
      have e : (2 * (2 * 10 ^ 16 + 1) / c) *
            ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (7 - ε))
            * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
              Real.log (x : ℝ) ^ (-(7 - ε)))
          = 2 * (2 * 10 ^ 16 + 1) := by
        calc (2 * (2 * 10 ^ 16 + 1) / c) *
              ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (7 - ε))
              * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
                Real.log (x : ℝ) ^ (-(7 - ε)))
            = (2 * (2 * 10 ^ 16 + 1) / c * c) *
                ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ)) *
                (Real.log (x : ℝ) ^ (7 - ε) *
                  Real.log (x : ℝ) ^ (-(7 - ε))) := by
              ring
          _ = (2 * (2 * 10 ^ 16 + 1) / c * c) * 1 * 1 := by rw [hX, hL2']
          _ = 2 * (2 * 10 ^ 16 + 1) := by
              rw [mul_one, mul_one, div_mul_cancel₀ _ hc.ne']
      rwa [e] at hle'
    have hR : (Real.log x) ^ (-(1 - ε)) *
          (c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6)
        = c * (x : ℝ) ^ (83 / 100 : ℝ) * (Real.log x) ^ (-(7 - ε)) := by
      have e : (Real.log x) ^ (-(7 - ε))
          = (Real.log x) ^ (-(1 - ε)) / (Real.log x) ^ 6 := by
        rw [← Real.rpow_natCast (Real.log x) 6, ← Real.rpow_sub hL]
        congr 1
        ring
      rw [e, ← mul_div_assoc, ← mul_div_assoc]
      ring
    calc (2 * 10 ^ 16 + 1 : ℝ)
        ≤ (1 / 2) * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
            Real.log (x : ℝ) ^ (-(7 - ε))) := by linarith
      _ = (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6)) := by rw [hR]
      _ ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (badSingletonCount (2 * x) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hSx2 (Real.rpow_nonneg hL.le _))
            (by norm_num)
  have hN : (badNonSingletonCount x : ℝ) ≤
      (runBandSum x : ℝ) + (2 * 10 ^ 16 + 1 : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_runBandSum x
  calc (badNonSingletonCount x : ℝ)
      ≤ (runBandSum x : ℝ) + (2 * 10 ^ 16 + 1 : ℝ) := hN
    _ ≤ (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ))
        + (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)) :=
        add_le_add (le_trans hx hterm) hCabs
    _ = Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount (2 * x) : ℝ) := by
        ring

end JSP314
