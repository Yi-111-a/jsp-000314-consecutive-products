import JSP314.FreshEye
import JSP314.SmoothUB
import JSP314.Squeeze2
import JSP314.Assault5
import Mathlib.Tactic

/-!
# JSP-000314 — LowBand: small-prime part of the near-pair sum

This file refines the residual hypothesis of `badNonSingleton_interval_bound`
(`JSP314/Main.lean`) by splitting the near-pair sum

  `∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p`

at a cutoff `Y(x)` into a *small* part `p ≤ Y(x)` and a *large* part
`p > Y(x)`.  For the cutoff `Y(x) = log₂(log₂ x)` the small part is
**proved here** to be `≤ x^{1/2}` eventually (via
`SmoothUB.nearPair_smallp_sum_le_rpow_half_eventually`), which is absorbed
into `S(x)·(log x)^{-1}` using the proved lower bound
`S(x) ≥ c·x^{83/100}/(log x)^6` (`Assault5.badSingletonCount_eventually_ge_log6`).

Hence the residual `badNonSingleton_interval_bound` is reduced to a bound
on the **large-prime part only** (`badNonSingleton_interval_bound_of_largePairSum`):
it suffices that
`∑_{log₂log₂x < p ≤ √(2x)} nearPairCoveredCount x p
   ≤ S(x)·(log x)^{-1}·(log log x)^K` eventually for some `K`.

## Contents

* `smallPairSum`, `largePairSum` — the two parts; `smallPairSum_add_largePairSum`
  gives the pointwise split.
* `badNonSingleton_interval_bound_of_pairSum_split` — generic transporter:
  loglog-loss bounds on both parts imply the residual (through
  `FreshEye.badNonSingleton_interval_bound_of_eventually_le`).
* `smallPairSum_le_rpow_half_eventually` — the proved `x^{1/2}` bound.
* `smallPairSum_loglog_bound` — the small part meets the `S·L^{-1}·(loglog)^0`
  transporter shape.
* `badNonSingleton_interval_bound_of_largePairSum` — the sharpened residual.
-/

open Nat Filter Classical

namespace JSP314

/-- `log x → ∞` along `ℕ` (local copy; the FreshEye analogue is private). -/
private theorem tendsto_log_atTop_lb :
    Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log log x → ∞` along `ℕ` (local copy). -/
private theorem tendsto_loglog_atTop_lb :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_atTop_lb

section Split

/-- Small-prime part of the near-pair sum: `p ≤ Y`. -/
noncomputable def smallPairSum (x Y : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (· ≤ Y),
    nearPairCoveredCount x p

/-- Large-prime part of the near-pair sum: `p > Y`. -/
noncomputable def largePairSum (x Y : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Y < p),
    nearPairCoveredCount x p

/-- **Pointwise split** of the near-pair sum at the cutoff `Y`. -/
theorem smallPairSum_add_largePairSum (x Y : ℕ) :
    smallPairSum x Y + largePairSum x Y =
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p := by
  have hcomp : (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => Y < p)
      = (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => ¬ p ≤ Y) :=
    Finset.filter_congr fun p _ => by omega
  unfold smallPairSum largePairSum
  rw [hcomp, Finset.sum_filter_add_sum_filter_not]

/-- `N(x) ≤ smallPairSum + largePairSum + (2·10^16 + 1)` pointwise. -/
theorem badNonSingletonCount_le_pairSplit_add_const (x Y : ℕ) :
    badNonSingletonCount x ≤
      smallPairSum x Y + largePairSum x Y + (2 * 10 ^ 16 + 1) := by
  have h := badNonSingletonCount_le_nearPair_sum_add_const x
  rw [← smallPairSum_add_largePairSum] at h
  exact h

end Split

section Transporter

/-- **Pair-split transporter.**  If at a cutoff `Y(x)` both the small-prime
part and the large-prime part of the near-pair sum are eventually
`≤ S(x)·(log x)^{-1}·(log log x)^K` (each with its own real exponent `K`),
then `badNonSingleton_interval_bound` holds. -/
theorem badNonSingleton_interval_bound_of_pairSum_split
    (Y : ℕ → ℕ)
    (hs : ∃ Ks : ℝ, ∀ᶠ x : ℕ in atTop,
      (smallPairSum x (Y x) : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ Ks)
    (hl : ∃ Kl : ℝ, ∀ᶠ x : ℕ in atTop,
      (largePairSum x (Y x) : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ Kl) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨Ks, hKs⟩ := hs
  obtain ⟨Kl, hKl⟩ := hl
  refine badNonSingleton_interval_bound_of_eventually_le
    (f := fun x => smallPairSum x (Y x) + largePairSum x (Y x)) 1 ?_
    ⟨max Ks Kl + 1, ?_⟩
  · intro x
    simpa using badNonSingletonCount_le_pairSplit_add_const x (Y x)
  · filter_upwards [hKs, hKl,
      tendsto_loglog_atTop_lb.eventually_ge_atTop 2,
      tendsto_log_atTop_lb.eventually_ge_atTop 1]
      with x hxs hxl ht2 hL1
    have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
    set t := Real.log (Real.log (x : ℝ)) with htdef
    have ht0 : (0 : ℝ) < t := by linarith [ht2]
    have ht1 : (1 : ℝ) ≤ t := by linarith [ht2]
    set B := (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ))
      with hBdef
    have hBnn : (0 : ℝ) ≤ B :=
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
    have hs' : (smallPairSum x (Y x) : ℝ) ≤ B * t ^ max Ks Kl :=
      hxs.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)) hBnn)
    have hl' : (largePairSum x (Y x) : ℝ) ≤ B * t ^ max Ks Kl :=
      hxl.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)) hBnn)
    have hstep : (2 : ℝ) * (B * t ^ max Ks Kl) ≤
        B * t ^ (max Ks Kl + 1) := by
      have e : t ^ (max Ks Kl + 1) = t ^ max Ks Kl * t := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      calc (2 : ℝ) * (B * t ^ max Ks Kl)
          = B * t ^ max Ks Kl * 2 := by ring
        _ ≤ B * t ^ max Ks Kl * t :=
            mul_le_mul_of_nonneg_left ht2
              (mul_nonneg hBnn (Real.rpow_nonneg ht0.le _))
        _ = B * t ^ (max Ks Kl + 1) := by rw [e]; ring
    calc ((smallPairSum x (Y x) + largePairSum x (Y x) : ℕ) : ℝ)
        = (smallPairSum x (Y x) : ℝ) + (largePairSum x (Y x) : ℝ) :=
          Nat.cast_add _ _
      _ ≤ B * t ^ max Ks Kl + B * t ^ max Ks Kl := add_le_add hs' hl'
      _ = 2 * (B * t ^ max Ks Kl) := by ring
      _ ≤ B * t ^ (max Ks Kl + 1) := hstep

end Transporter

section SmallPart

/-- **Small part is `≤ x^{1/2}` eventually.**  The filtered sum at
`Y = log₂(log₂ x)` is a subsum of the full `primesLE (log₂log₂ x)` sum
(along `Nat.mem_primesLE`), bounded by `x^{1/2}` via
`SmoothUB.nearPair_smallp_sum_le_rpow_half_eventually`. -/
theorem smallPairSum_le_rpow_half_eventually :
    ∀ᶠ x : ℕ in atTop,
      (smallPairSum x (Nat.log 2 (Nat.log 2 x)) : ℝ) ≤
        (x : ℝ) ^ (1 / 2 : ℝ) := by
  filter_upwards [nearPair_smallp_sum_le_rpow_half_eventually]
    with x hx
  have hsub : (Nat.primesLE (Nat.sqrt (2 * x))).filter
        (· ≤ Nat.log 2 (Nat.log 2 x))
      ⊆ Nat.primesLE (Nat.log 2 (Nat.log 2 x)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.2, (Nat.mem_primesLE.mp hp.1).2⟩
  have hsum : smallPairSum x (Nat.log 2 (Nat.log 2 x))
      ≤ ∑ p ∈ Nat.primesLE (Nat.log 2 (Nat.log 2 x)),
          nearPairCoveredCount x p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  have hsum' : (smallPairSum x (Nat.log 2 (Nat.log 2 x)) : ℝ) ≤
      (∑ p ∈ Nat.primesLE (Nat.log 2 (Nat.log 2 x)),
        nearPairCoveredCount x p : ℕ) := by
    exact_mod_cast hsum
  exact hsum'.trans hx

/-- **Small part meets the transporter shape** with exponent `K = 0`:
`smallPairSum ≤ S(x)·(log x)^{-1}` eventually.  Indeed it is `≤ x^{1/2}`,
while `S(x) ≥ c·x^{83/100}/(log x)^6` eventually, and
`x^{1/2}·(log x) ≤ c·x^{83/100}/(log x)^6` because
`x^{-(83/100 - 1/2)}·(log x)^7 → 0` (any positive power of `x` beats any
power of `log x`: `Squeeze2.tendsto_pow_neg_mul_log_pow`). -/
theorem smallPairSum_loglog_bound :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (smallPairSum x (Nat.log 2 (Nat.log 2 x)) : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K := by
  obtain ⟨c, hc, hS⟩ := badSingletonCount_eventually_ge_log6
  refine ⟨0, ?_⟩
  -- `c⁻¹·x^{-(83/100 - 1/2)}·(log x)^7 → 0`, hence `< 1` eventually.
  have ht : Tendsto
      (fun n : ℕ => (c ⁻¹) *
        ((n : ℝ) ^ (-(83 / 100 - 1 / 2 : ℝ)) * (Real.log n) ^ (7 : ℝ)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_neg_mul_log_pow (83 / 100 - 1 / 2) 7
        (by norm_num)).const_mul (c ⁻¹)
  have ht1 : ∀ᶠ x : ℕ in atTop,
      (c ⁻¹) * ((x : ℝ) ^ (-(83 / 100 - 1 / 2 : ℝ)) *
          (Real.log x) ^ (7 : ℝ)) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [smallPairSum_le_rpow_half_eventually, hS, ht1,
    tendsto_log_atTop_lb.eventually_ge_atTop 1, eventually_ge_atTop 2]
    with x hx hSx hcx hL1 hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxp : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  rw [Real.rpow_zero, mul_one]
  -- Bridge `(log x)^(7:ℝ)` (rpow, from `tendsto_pow_neg_mul_log_pow`) to npow.
  have h7 : Real.log (x : ℝ) ^ (7 : ℝ) = Real.log (x : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h7] at hcx
  -- `key : x^{1/2}·L^7 < c·x^{83/100}` from `hcx : c⁻¹·x^{-(33/100)}·L^7 < 1`.
  have key : (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ^ 7 <
      c * (x : ℝ) ^ (83 / 100 : ℝ) := by
    calc (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ^ 7
        = (x : ℝ) ^ (83 / 100 : ℝ) * (x : ℝ) ^ (-(83 / 100 - 1 / 2) : ℝ) *
            Real.log (x : ℝ) ^ 7 := by
          rw [← Real.rpow_add hxp,
            show (83 / 100 : ℝ) + -(83 / 100 - 1 / 2) = 1 / 2 by ring]
      _ = (x : ℝ) ^ (83 / 100 : ℝ) * (c * c ⁻¹) *
            ((x : ℝ) ^ (-(83 / 100 - 1 / 2) : ℝ) * Real.log (x : ℝ) ^ 7) := by
          rw [mul_inv_cancel₀ hc.ne', mul_one, mul_assoc]
      _ = (x : ℝ) ^ (83 / 100 : ℝ) * c *
            (c ⁻¹ * ((x : ℝ) ^ (-(83 / 100 - 1 / 2) : ℝ) *
              Real.log (x : ℝ) ^ 7)) := by ring
      _ < (x : ℝ) ^ (83 / 100 : ℝ) * c * 1 :=
          mul_lt_mul_of_pos_left hcx
            (mul_pos (Real.rpow_pos_of_pos hxp _) hc)
      _ = c * (x : ℝ) ^ (83 / 100 : ℝ) := by ring
  -- Divide `x^{1/2}·L^7 < c·x^{83/100}` by `L^6 > 0`.
  have hgoal : (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ≤
      c * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log (x : ℝ) ^ 6 := by
    rw [le_div_iff₀ (pow_pos hL 6)]
    calc (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) * Real.log (x : ℝ) ^ 6
        = (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ^ 7 := by ring
      _ ≤ c * (x : ℝ) ^ (83 / 100 : ℝ) := key.le
  have hgoal' : (x : ℝ) ^ (1 / 2 : ℝ) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) := by
    have h1 : (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) ≤
        (badSingletonCount x : ℝ) := hgoal.trans hSx
    calc (x : ℝ) ^ (1 / 2 : ℝ)
        = (x : ℝ) ^ (1 / 2 : ℝ) * Real.log (x : ℝ) * (Real.log x)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hL), mul_one]
      _ ≤ (badSingletonCount x : ℝ) * (Real.log x)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hL.le)
      _ = (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
  exact hx.trans hgoal'

end SmallPart

section Residual

/-- **Sharpened residual.**  `badNonSingleton_interval_bound` — and hence the
headline `bad_interval_count_asymptotic` — follows from a bound on the
**large-prime part only** of the near-pair sum at the cutoff
`Y = log₂(log₂ x)`:

  `∑_{log₂log₂x < p ≤ √(2x)} nearPairCoveredCount x p
     ≤ S(x)·(log x)^{-1}·(log log x)^K`   eventually, for some real `K`.

The small-prime part is discharged unconditionally in
`smallPairSum_loglog_bound`. -/
theorem badNonSingleton_interval_bound_of_largePairSum
    (hl : ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (largePairSum x (Nat.log 2 (Nat.log 2 x)) : ℝ) ≤
        (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
          (Real.log (Real.log x)) ^ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_pairSum_split
    (fun x => Nat.log 2 (Nat.log 2 x)) smallPairSum_loglog_bound hl

end Residual

end JSP314
