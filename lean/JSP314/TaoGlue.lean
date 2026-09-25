import JSP314.FinalReduction
import JSP314.BandSum
import JSP314.SharpSqueeze
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# JSP-000314 — Tao glue: the sharpest named hypotheses for the residual

This file closes `badNonSingleton_interval_bound` (`Main.lean`) down to the
*sharpest* hypothesis shapes currently plausible, so that future rounds only
need to supply band estimates.  Everything here is proved (no placeholders, no new
axioms); each theorem is a conditional reduction.

## Contents

* `runCountLow`, `runCountHigh` — the split of `runCountSum` (and hence
  `runBandSum`) into a *low band* `p ≤ Z` and a *high band* `p > Z` at an
  arbitrary cut `Z : ℕ`.  `runCountLow_add_runCountHigh` and
  `runBandLow_add_runBandHigh` give the pointwise decompositions.

* `runBandSum_le_of_bandSplit` — if each band is separately
  `≤ (its share)·(log x)^{-(1-ε)}·S(2x)` eventually for every `ε > 0`, then
  `runBandSum x ≤ (Cs + Cl)·(log x)^{-(1-ε)}·S(2x)` eventually: exactly the
  hypothesis of
  `FinalReduction.badNonSingleton_interval_bound_of_runBand_const_twoMul`.

* `badNonSingleton_interval_bound_of_bandSplit` — the previous item fed
  through `..._of_runBand_const_twoMul`: band estimates imply
  `N(x) ≤ (log x)^{-(1-ε)}·S(2x)` eventually for every `ε > 0`.

* `badNonSingleton_interval_bound_of_runBand_twoMul_S` — transports the
  `S(2x)`-comparison to `S(x)` under a *stability* hypothesis
  `S(2x) ≤ Cs·S(x) + Ca` eventually (e.g. the `S(2x) ≤ 3·S(x) + 2` being
  proved in `Stability.lean` — taken here as an arbitrary hypothesis).
  Conclusion is the exact `Main.lean` statement.

* `badNonSingleton_interval_bound_of_bandSplit_S` — the full chain:
  two band bounds + stability ⇒ `badNonSingleton_interval_bound`.

* `badSingletonCount_twoMul_eventually_le_real` — casts an `ℕ`-valued
  (pointwise or eventual) stability bound `S(2x) ≤ Cs·S(x) + Ca` to the
  `ℝ`-valued eventual hypothesis used above.

* `badNonSingleton_interval_bound_of_N_zscale_sharp` — convenience wrapper
  around `SharpSqueeze.badNonSingleton_interval_bound_of_sharp_SLB4`
  producing the exact `Main.lean` statement shape, so a future edit of
  `Main.lean` is a one-line `exact`.
-/

open Nat Filter Classical

namespace JSP314

section BandSplit

/-- Low band of the run-count sum: primes `p ≤ Z`. -/
noncomputable def runCountLow (x Z : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (· ≤ Z),
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- High band of the run-count sum: primes `p > Z`. -/
noncomputable def runCountHigh (x Z : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p),
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- Low band of the run-band sum (`= 2·runCountLow`). -/
noncomputable def runBandLow (x Z : ℕ) : ℕ := 2 * runCountLow x Z

/-- High band of the run-band sum (`= 2·runCountHigh`). -/
noncomputable def runBandHigh (x Z : ℕ) : ℕ := 2 * runCountHigh x Z

/-- `runBandSum` is literally `2·runCountSum`. -/
theorem runBandSum_eq_two_mul_runCountSum (x : ℕ) :
    runBandSum x = 2 * runCountSum x := rfl

/-- **Pointwise split of `runCountSum`** at the cut `Z`:
`runCountLow + runCountHigh = runCountSum`. -/
theorem runCountLow_add_runCountHigh (x Z : ℕ) :
    runCountLow x Z + runCountHigh x Z = runCountSum x := by
  have hcomp : (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Z < p)
      = (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => ¬ p ≤ Z) :=
    Finset.filter_congr (fun p _ => by omega)
  unfold runCountLow runCountHigh runCountSum
  rw [hcomp, Finset.sum_filter_add_sum_filter_not]

/-- **Pointwise split of `runBandSum`** at the cut `Z`:
`runBandLow + runBandHigh = runBandSum`. -/
theorem runBandLow_add_runBandHigh (x Z : ℕ) :
    runBandLow x Z + runBandHigh x Z = runBandSum x := by
  rw [runBandLow, runBandHigh, ← mul_add, runCountLow_add_runCountHigh,
    runBandSum_eq_two_mul_runCountSum]

end BandSplit

section Reductions

/-- **Band-split assembler.**  If at a cut `Z(x)` the low band `p ≤ Z(x)` is
eventually `≤ Cs·(log x)^{-(1-ε)}·S(2x)` and the high band `p > Z(x)` is
eventually `≤ Cl·(log x)^{-(1-ε)}·S(2x)`, for every `ε > 0`, then
`runBandSum x ≤ (Cs + Cl)·(log x)^{-(1-ε)}·S(2x)` eventually for every
`ε > 0` — precisely the hypothesis of
`badNonSingleton_interval_bound_of_runBand_const_twoMul`. -/
theorem runBandSum_le_of_bandSplit
    (Z : ℕ → ℕ) (Cs Cl : ℝ)
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandLow x (Z x) : ℝ) ≤
        Cs * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)))
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandHigh x (Z x) : ℝ) ≤
        Cl * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandSum x : ℝ) ≤
        (Cs + Cl) * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)) := by
  intro ε hε
  filter_upwards [hs ε hε, hl ε hε] with x hxs hxl
  have hsplit : (runBandSum x : ℝ) =
      (runBandLow x (Z x) : ℝ) + (runBandHigh x (Z x) : ℝ) := by
    rw [← runBandLow_add_runBandHigh x (Z x), Nat.cast_add]
  rw [hsplit]
  calc (runBandLow x (Z x) : ℝ) + (runBandHigh x (Z x) : ℝ)
      ≤ Cs * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
            (badSingletonCount (2 * x) : ℝ))
        + Cl * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
            (badSingletonCount (2 * x) : ℝ)) := add_le_add hxs hxl
    _ = (Cs + Cl) * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)) := by ring

/-- **Band-split reduction.**  Two eventual band bounds at `S(2x)` imply
`N(x) ≤ (log x)^{-(1-ε)}·S(2x)` eventually for every `ε > 0` (the conclusion
of `badNonSingleton_interval_bound_of_runBand_const_twoMul`). -/
theorem badNonSingleton_interval_bound_of_bandSplit
    (Z : ℕ → ℕ) (Cs Cl : ℝ)
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandLow x (Z x) : ℝ) ≤
        Cs * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)))
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandHigh x (Z x) : ℝ) ≤
        Cl * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log (x : ℝ)) ^ (-(1 - ε)) * (badSingletonCount (2 * x) : ℝ) :=
  badNonSingleton_interval_bound_of_runBand_const_twoMul (Cs + Cl)
    (runBandSum_le_of_bandSplit Z Cs Cl hs hl)

/-- **Stability transport**: an `ℕ`-valued eventual stability bound
`S(2x) ≤ Cs·S(x) + Ca` (with `Cs Ca : ℕ`) yields the `ℝ`-valued hypothesis
used by `badNonSingleton_interval_bound_of_runBand_twoMul_S`.  Covers the
sibling file's pointwise `S(2x) ≤ 3·S(x) + 2` via
`Filter.Eventually.of_forall`. -/
theorem badSingletonCount_twoMul_eventually_le_real {Cs Ca : ℕ}
    (h : ∀ᶠ x : ℕ in atTop,
      badSingletonCount (2 * x) ≤ Cs * badSingletonCount x + Ca) :
    ∀ᶠ x : ℕ in atTop,
      (badSingletonCount (2 * x) : ℝ) ≤
        (Cs : ℝ) * badSingletonCount x + Ca := by
  filter_upwards [h] with x hx
  exact_mod_cast hx

/-- **Stability reduction.**  Combining
`badNonSingleton_interval_bound_of_runBand_const_twoMul` (giving
`N ≤ (log x)^{-(1-ε)}·S(2x)`) with an eventual stability bound
`S(2x) ≤ Cs·S(x) + Ca` transports the comparison to `S(x)`, producing the
exact `Main.lean` statement.

Proof sketch: apply the `twoMul` reduction at `ε/2`, so
`N ≤ L^{-(1-ε/2)}·S(2x) ≤ L^{-(1-ε/2)}·(Cs·S + Ca)`.  Since
`L^{ε/2} → ∞`, eventually `Cs ≤ L^{ε/2}/4`; and the proved lower bound
`S(x) ≥ c·x^{83/100}/L^6` (Assault5) eventually gives
`Ca ≤ (L^{ε/2}/4)·S`.  Hence `Cs·S + Ca ≤ (L^{ε/2}/2)·S` and
`N ≤ (1/2)·L^{-(1-ε)}·S ≤ L^{-(1-ε)}·S`. -/
theorem badNonSingleton_interval_bound_of_runBand_twoMul_S
    (C Cs Ca : ℝ)
    (hstab : ∀ᶠ x : ℕ in atTop,
      (badSingletonCount (2 * x) : ℝ) ≤
        Cs * (badSingletonCount x : ℝ) + Ca)
    (H : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandSum x : ℝ) ≤
        C * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log (x : ℝ)) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  have hN := badNonSingleton_interval_bound_of_runBand_const_twoMul C H
    (ε / 2) (half_pos hε)
  obtain ⟨c, hc, hS⟩ := badSingletonCount_eventually_ge_log6
  have hLt : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLp : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (ε / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hε)).comp hLt
  -- `(log x)^{ε/2} → ∞`, hence `≥ max 2 (4·Cs)` eventually.
  have hL2 : ∀ᶠ x : ℕ in atTop,
      (max 2 (4 * Cs) : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    hLp.eventually_ge_atTop _
  -- `4(|Ca|+1)·c^{-1}·x^{-83/100}·L^{6+ε/2} → 0`, hence `< 1` eventually:
  -- multiplied by `c·x^{83/100}·L^{-(6+ε/2)}` this gives
  -- `4(|Ca|+1) ≤ c·x^{83/100}·L^{-(6+ε/2)}`.
  have ht : Tendsto
      (fun n : ℕ =>
        (4 * (|Ca| + 1) / c) *
          ((n : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log n) ^ (6 + ε / 2)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_neg_mul_log_pow (83 / 100) (6 + ε / 2)
        (by norm_num)).const_mul (4 * (|Ca| + 1) / c)
  have ht1 : ∀ᶠ x : ℕ in atTop,
      (4 * (|Ca| + 1) / c) *
        ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (Real.log (x : ℝ)) ^ (6 + ε / 2)) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hN, hstab, hL2, hS, ht1, eventually_ge_atTop 2]
    with x hNx hStab hLp2 hSx hCx hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxp : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLpow : 0 < Real.log (x : ℝ) ^ (ε / 2) := Real.rpow_pos_of_pos hL _
  have hSnn : (0 : ℝ) ≤ (badSingletonCount x : ℝ) := Nat.cast_nonneg _
  have hLge2 : (2 : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    le_trans (le_max_left _ _) hLp2
  have hCs4 : 4 * Cs ≤ Real.log (x : ℝ) ^ (ε / 2) :=
    le_trans (le_max_right _ _) hLp2
  -- Constant absorption: `4(|Ca|+1)·L^{ε/2} ≤ S(x)` via the `x^{83/100}`
  -- lower bound on `S`.
  have hpos : 0 < c * (x : ℝ) ^ (83 / 100 : ℝ) *
      Real.log (x : ℝ) ^ (-(6 + ε / 2)) :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos hxp _))
      (Real.rpow_pos_of_pos hL _)
  have hle' := mul_le_mul_of_nonneg_right hCx.le hpos.le
  rw [one_mul] at hle'
  have hX : (x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ) = 1 := by
    rw [← Real.rpow_add hxp,
      show (-(83 / 100 : ℝ)) + 83 / 100 = 0 by ring, Real.rpow_zero]
  have hL6 : Real.log (x : ℝ) ^ (6 + ε / 2) *
      Real.log (x : ℝ) ^ (-(6 + ε / 2)) = 1 := by
    rw [← Real.rpow_add hL, show (6 + ε / 2) + -(6 + ε / 2) = (0 : ℝ) by ring,
      Real.rpow_zero]
  have e : (4 * (|Ca| + 1) / c) *
        ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (6 + ε / 2))
        * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
          Real.log (x : ℝ) ^ (-(6 + ε / 2)))
        = 4 * (|Ca| + 1) := by
    calc (4 * (|Ca| + 1) / c) *
          ((x : ℝ) ^ (-(83 / 100 : ℝ)) * Real.log (x : ℝ) ^ (6 + ε / 2))
          * (c * (x : ℝ) ^ (83 / 100 : ℝ) *
            Real.log (x : ℝ) ^ (-(6 + ε / 2)))
        = (4 * (|Ca| + 1) / c * c) *
            ((x : ℝ) ^ (-(83 / 100 : ℝ)) * (x : ℝ) ^ (83 / 100 : ℝ)) *
            (Real.log (x : ℝ) ^ (6 + ε / 2) *
              Real.log (x : ℝ) ^ (-(6 + ε / 2))) := by ring
      _ = (4 * (|Ca| + 1) / c * c) * 1 * 1 := by rw [hX, hL6]
      _ = 4 * (|Ca| + 1) := by
          rw [mul_one, mul_one, div_mul_cancel₀ _ hc.ne']
  rw [e] at hle'
  have hLpA : Real.log (x : ℝ) ^ (-(6 + ε / 2)) * Real.log (x : ℝ) ^ (ε / 2)
      = Real.log (x : ℝ) ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hS4 : 4 * (|Ca| + 1) * Real.log (x : ℝ) ^ (ε / 2) ≤
      (badSingletonCount x : ℝ) := by
    have hle2 := mul_le_mul_of_nonneg_right hle' hLpow.le
    calc 4 * (|Ca| + 1) * Real.log (x : ℝ) ^ (ε / 2)
        ≤ (c * (x : ℝ) ^ (83 / 100 : ℝ) *
            Real.log (x : ℝ) ^ (-(6 + ε / 2))) * Real.log (x : ℝ) ^ (ε / 2) :=
          hle2
      _ = c * (x : ℝ) ^ (83 / 100 : ℝ) *
            Real.log (x : ℝ) ^ (-(6 : ℝ)) := by
          rw [← hLpA]; ring
      _ = c * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log (x : ℝ) ^ 6 := by
          have h6 : Real.log (x : ℝ) ^ (-(6 : ℝ)) =
              (Real.log (x : ℝ) ^ 6)⁻¹ := by
            rw [show (-(6 : ℝ)) = -(((6 : ℕ)) : ℝ) by norm_num,
              Real.rpow_neg hL.le, Real.rpow_natCast]
          rw [h6, div_eq_mul_inv]
      _ ≤ (badSingletonCount x : ℝ) := hSx
  -- `Cs·S ≤ (L^{ε/2}/4)·S` and `Ca ≤ (L^{ε/2}/4)·S`.
  have hCs : Cs * (badSingletonCount x : ℝ) ≤
      Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ) := by
    have hCs' : Cs ≤ Real.log (x : ℝ) ^ (ε / 2) / 4 := by linarith
    exact mul_le_mul_of_nonneg_right hCs' hSnn
  have hCa : Ca ≤
      Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ) := by
    have hLge1 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) := by linarith
    have hQ : (1 / 4 : ℝ) ≤ Real.log (x : ℝ) ^ (ε / 2) / 4 := by linarith
    calc Ca ≤ |Ca| + 1 := le_trans (le_abs_self Ca) (by linarith)
      _ ≤ (|Ca| + 1) * Real.log (x : ℝ) ^ (ε / 2) :=
          le_mul_of_one_le_right (by positivity) hLge1
      _ ≤ (badSingletonCount x : ℝ) / 4 := by linarith
      _ = (1 / 4) * (badSingletonCount x : ℝ) := by ring
      _ ≤ Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ) :=
          mul_le_mul_of_nonneg_right hQ hSnn
  -- `Cs·S + Ca ≤ (L^{ε/2}/4 + L^{ε/2}/4)·S`.
  have hhalf : Cs * (badSingletonCount x : ℝ) + Ca ≤
      Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ)
        + Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ) := by
    linarith
  -- `(log x)^{-(1-ε/2)}·(log x)^{ε/2} = (log x)^{-(1-ε)}`.
  have hfac : Real.log (x : ℝ) ^ (-(1 - ε / 2)) * Real.log (x : ℝ) ^ (ε / 2)
      = Real.log (x : ℝ) ^ (-(1 - ε)) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hterm : Real.log (x : ℝ) ^ (-(1 - ε / 2)) *
        (badSingletonCount (2 * x) : ℝ)
      ≤ Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
    calc Real.log (x : ℝ) ^ (-(1 - ε / 2)) * (badSingletonCount (2 * x) : ℝ)
        ≤ Real.log (x : ℝ) ^ (-(1 - ε / 2)) *
            (Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ)
              + Real.log (x : ℝ) ^ (ε / 2) / 4 * (badSingletonCount x : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hStab hhalf)
            (Real.rpow_nonneg hL.le _)
      _ = (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε / 2)) *
            Real.log (x : ℝ) ^ (ε / 2) * (badSingletonCount x : ℝ)) := by ring
      _ = (1 / 2) * (Real.log (x : ℝ) ^ (-(1 - ε)) *
            (badSingletonCount x : ℝ)) := by rw [hfac]
      _ ≤ Real.log (x : ℝ) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
          have hT : (0 : ℝ) ≤ Real.log (x : ℝ) ^ (-(1 - ε)) *
              (badSingletonCount x : ℝ) :=
            mul_nonneg (Real.rpow_nonneg hL.le _) hSnn
          linarith
  exact le_trans hNx hterm

/-- **Full band-split chain**: low-band bound + high-band bound + stability
`S(2x) ≤ Ct·S(x) + Ca` eventually ⇒ the exact `badNonSingleton_interval_bound`
statement of `Main.lean`.  Downstream agents need only supply the two band
estimates and the stability bound. -/
theorem badNonSingleton_interval_bound_of_bandSplit_S
    (Z : ℕ → ℕ) (Cs Cl Ct Ca : ℝ)
    (hstab : ∀ᶠ x : ℕ in atTop,
      (badSingletonCount (2 * x) : ℝ) ≤
        Ct * (badSingletonCount x : ℝ) + Ca)
    (hs : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandLow x (Z x) : ℝ) ≤
        Cs * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ)))
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (runBandHigh x (Z x) : ℝ) ≤
        Cl * ((Real.log (x : ℝ)) ^ (-(1 - ε)) *
          (badSingletonCount (2 * x) : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log (x : ℝ)) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_runBand_twoMul_S (Cs + Cl) Ct Ca hstab
    (runBandSum_le_of_bandSplit Z Cs Cl hs hl)

/-- **Z-scale sharp wrapper.**  From the SharpSqueeze hypothesis
`∀ᶠ x, N(x) ≤ x·exp(-C·s)·(log x)^{-B}` with `C > 2√2` and `B > 1`
(`s = √(log x·log log x)`), derive the exact `Main.lean` statement of
`badNonSingleton_interval_bound` — a future edit of `Main.lean` is a one-line
`exact` application.  This is
`SharpSqueeze.badNonSingleton_interval_bound_of_sharp_SLB4` (which uses the
proved `SmoothLB4.badSingletonCount_eventually_ge_zscale_two` for the `S`
side) restated under a name matching its role. -/
theorem badNonSingleton_interval_bound_of_N_zscale_sharp {C B : ℝ}
    (hC : 2 * Real.sqrt 2 < C) (hB : 1 < B)
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log (x : ℝ)) ^ (-B)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log (x : ℝ)) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_sharp_SLB4 hC hB hN

end Reductions

end JSP314
