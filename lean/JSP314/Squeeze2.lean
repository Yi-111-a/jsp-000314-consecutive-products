import JSP314.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-!
# JSP-000314 — conditional squeeze for `badNonSingleton_interval_bound`

This file reduces the residual analytic core `badNonSingleton_interval_bound`
(`Main.lean`, currently unproved) to a *power-saving* hypothesis on the
non-singleton count `N(x) = badNonSingletonCount x`, relative to a power-type
lower bound on the singleton count `S(x) = badSingletonCount x`.

## The squeeze

If `S(x) ≥ c·x^β / (log x)^6` eventually and `N(x) ≤ C·x^{1−δ}` eventually
with `1 − δ < β` (i.e. the power-saving bound on `N` is genuinely below the
power lower bound on `S`), then for every `ε > 0`, eventually

  `N(x) ≤ C·x^{1−δ} ≤ (log x)^{−(1−ε)} · c·x^β·(log x)^{−6}
        ≤ (log x)^{−(1−ε)} · S(x)`,

because the ratio `(C/c)·x^{−(β−(1−δ))}·(log x)^{7−ε} → 0`
(`tendsto_pow_neg_mul_log_pow`, from Mathlib's
`isLittleO_log_rpow_rpow_atTop`).

## ⚠ Numerical caveat (deviation from the original sketch)

The squeeze needs the `N`-bound exponent `1 − δ` to be *strictly less* than
the `S`-bound exponent `β`.  Hence:

* `badNonSingleton_interval_bound_of_power_saving'` takes `1 − δ < β`
  (the sketch's `δ < β` does not imply `1 − δ < β` for `β < 1` and is
  insufficient);
* `badNonSingleton_interval_bound_of_power_saving` keeps the hypothesis
  `∀ δ < 1/6, ∃ C, N ≤ C·x^{1−δ}` verbatim, which yields exponents
  `1 − δ > 5/6`, so it must be paired with a singleton lower bound at some
  exponent `β > 5/6`.  In particular the `β = 83/100` bound proved in
  `SmoothLB.lean` does **not** suffice: `83/100 = 0.83 < 5/6 = 0.833…`,
  leaving a residual gap `x^{1/300}` (the sign of this gap was inverted in
  the sketch: `11/12 − 83/100 = 26/300 > 0`, and `5/6 − 83/100 = 1/300`).

`SmoothLB.lean` / `SingletonLB.lean` do not currently compile (mathlib API
drift plus a few genuine errors), so the singleton lower bound is taken here
as an explicit hypothesis `hS`; either file's conclusion can be fed in once
repaired (with `β = 83/100` it additionally requires `β > 5/6`, so a slightly
stronger `S`-bound or a stronger power saving `δ > 17/100`, i.e. beyond
`1/6`, would be needed).
-/

namespace JSP314

open Filter Asymptotics

/-- **Generic squeeze lemma.**  For `a > 0` and any real `γ`,
`x^{-a}·(log x)^γ → 0` as `x → ∞` along `ℕ`.

Proof: `log^γ =o x^a` at `∞` (`isLittleO_log_rpow_rpow_atTop`), so
`log x^γ / x^a → 0`; for `x > 0` this equals `x^{-a}·(log x)^γ`. -/
theorem tendsto_pow_neg_mul_log_pow (a γ : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-a) * (Real.log n) ^ γ) atTop (nhds 0) := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ γ / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop γ ha).tendsto_div_nhds_zero
  have h1 := h0.comp tendsto_natCast_atTop_atTop
  have hev : (fun n : ℕ => Real.log (n : ℝ) ^ γ / (n : ℝ) ^ a) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-a) * (Real.log n) ^ γ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hn'.le, div_eq_mul_inv, mul_comm]
  exact h1.congr' hev

/-- **The squeeze step.**  If `S(x) ≥ c·x^β/(log x)^6` and
`N(x) ≤ C·x^{1−δ}` with `1 − δ < β`, then
`N(x) ≤ (log x)^{-(1−ε)}·S(x)` eventually for every `ε > 0`. -/
theorem badNonSingleton_interval_bound_of_squeeze
    {c β : ℝ} (hc : 0 < c)
    (hS : ∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) ^ β / (Real.log x) ^ 6 ≤ (badSingletonCount x : ℝ))
    {δ C : ℝ} (hδβ : 1 - δ < β)
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤ C * (x : ℝ) ^ (1 - δ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  have ha : 0 < β - (1 - δ) := sub_pos.mpr hδβ
  -- `(C/c)·x^{-(β-(1-δ))}·(log x)^{7-ε} → 0`, hence `< 1` eventually.
  have ht : Tendsto
      (fun n : ℕ =>
        (C / c) * ((n : ℝ) ^ (-(β - (1 - δ))) * (Real.log n) ^ (7 - ε)))
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_neg_mul_log_pow (β - (1 - δ)) (7 - ε) ha).const_mul (C / c)
  have ht1 : ∀ᶠ x : ℕ in atTop,
      (C / c) * ((x : ℝ) ^ (-(β - (1 - δ))) * (Real.log x) ^ (7 - ε)) < 1 :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht1, hS, hN, eventually_ge_atTop 2] with x h1 hSx hNx hx2
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxp : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  -- `x^{-(β-(1-δ))}·x^β = x^{1-δ}` and `(log x)^{7-ε}·(log x)^{-(7-ε)} = 1`.
  have hX : (x : ℝ) ^ (-(β - (1 - δ))) * (x : ℝ) ^ β = (x : ℝ) ^ (1 - δ) := by
    rw [← Real.rpow_add hxp]
    congr 1
    ring
  have hL2 : (Real.log x) ^ (7 - ε) * (Real.log x) ^ (-(7 - ε)) = 1 := by
    have e : (7 - ε) + -(7 - ε) = (0 : ℝ) := by ring
    rw [← Real.rpow_add hL, e, Real.rpow_zero]
  -- multiplying the `< 1` bound by the positive `c·x^β·(log x)^{-(7-ε)}`
  -- yields `C·x^{1-δ} ≤ c·x^β·(log x)^{-(7-ε)}`.
  have hpos : 0 < c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε)) :=
    mul_pos (mul_pos hc (Real.rpow_pos_of_pos hxp _)) (Real.rpow_pos_of_pos hL _)
  have hle : C * (x : ℝ) ^ (1 - δ) ≤
      c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε)) := by
    have hle' := mul_le_mul_of_nonneg_right h1.le hpos.le
    rw [one_mul] at hle'
    have e : (C / c) * ((x : ℝ) ^ (-(β - (1 - δ))) * (Real.log x) ^ (7 - ε)) *
          (c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε))) = C * (x : ℝ) ^ (1 - δ) := by
      rw [show (C / c) * ((x : ℝ) ^ (-(β - (1 - δ))) * (Real.log x) ^ (7 - ε)) *
            (c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε)))
          = (C / c * c) * ((x : ℝ) ^ (-(β - (1 - δ))) * (x : ℝ) ^ β) *
            ((Real.log x) ^ (7 - ε) * (Real.log x) ^ (-(7 - ε))) by ring,
        hX, hL2, mul_one, div_mul_cancel₀ C hc.ne']
    rwa [e] at hle'
  -- `(log x)^{-(1-ε)}·(c·x^β/(log x)^6) = c·x^β·(log x)^{-(7-ε)}`.
  have hR : (Real.log x) ^ (-(1 - ε)) * (c * (x : ℝ) ^ β / (Real.log x) ^ 6)
      = c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε)) := by
    have e : (Real.log x) ^ (-(7 - ε))
        = (Real.log x) ^ (-(1 - ε)) / (Real.log x) ^ 6 := by
      rw [← Real.rpow_natCast (Real.log x) 6, ← Real.rpow_sub hL]
      congr 1
      ring
    rw [e, ← mul_div_assoc, ← mul_div_assoc]
    ring
  calc (badNonSingletonCount x : ℝ) ≤ C * (x : ℝ) ^ (1 - δ) := hNx
    _ ≤ c * (x : ℝ) ^ β * (Real.log x) ^ (-(7 - ε)) := hle
    _ = (Real.log x) ^ (-(1 - ε)) * (c * (x : ℝ) ^ β / (Real.log x) ^ 6) := hR.symm
    _ ≤ (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
        mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hL.le _)

/-- **Conditional squeeze, existential form.**
Concludes exactly the statement of `badNonSingleton_interval_bound`
(`Main.lean`) from a singleton lower bound `hS` at exponent `β` and a
power-saving bound `hN` on `N` at exponent `1 - δ` strictly below `β`.

NOTE: the hypothesis on `δ` is `1 − δ < β` (the condition the squeeze
actually needs), *not* `δ < β` as in the original sketch — for `β < 1` the
latter does not imply the former and does not suffice. -/
theorem badNonSingleton_interval_bound_of_power_saving'
    {β : ℝ}
    (hS : ∃ c : ℝ, 0 < c ∧ 0 < β ∧ (∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) ^ β / (Real.log x) ^ 6 ≤ (badSingletonCount x : ℝ)))
    (hN : ∃ δ : ℝ, ∃ C : ℝ, 0 < δ ∧ 1 - δ < β ∧ (∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤ C * (x : ℝ) ^ (1 - δ))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨c, hc, -, hSev⟩ := hS
  obtain ⟨δ, C, -, hδβ, hNev⟩ := hN
  exact badNonSingleton_interval_bound_of_squeeze hc hSev hδβ hNev

/-- **Conditional squeeze from uniform power saving `δ < 1/6`.**
Keeps the power-saving hypothesis `∀ δ ∈ (0, 1/6), ∃ C, N ≤ C·x^{1−δ}`
verbatim; the produced exponents `1 − δ` range over `(5/6, 1)`, so the
singleton lower bound `hS` must hold at some exponent `β > 5/6` for the
squeeze to close.  (With `β = 83/100` — the `SmoothLB` value — this fails by
a factor `x^{1/300}`; `5/6 = 83.333…/100`.) -/
theorem badNonSingleton_interval_bound_of_power_saving
    (hS : ∃ c : ℝ, ∃ β : ℝ, 0 < c ∧ 5 / 6 < β ∧ (∀ᶠ x : ℕ in atTop,
      c * (x : ℝ) ^ β / (Real.log x) ^ 6 ≤ (badSingletonCount x : ℝ)))
    (hβ : ∀ δ : ℝ, 0 < δ → δ < 1 / 6 → ∃ C : ℝ, ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤ C * (x : ℝ) ^ (1 - δ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨c, β, hc, hβ56, hSev⟩ := hS
  -- pick `δ₀` in `(max (1-β) 0, 1/6)`, nonempty since `β > 5/6`.
  have hmax : max (1 - β) 0 < 1 / 6 := by
    rw [max_lt_iff]
    constructor <;> linarith
  obtain ⟨δ0, hδ0l, hδ0u⟩ := exists_between hmax
  obtain ⟨C, hC⟩ := hβ δ0 (lt_of_le_of_lt (le_max_right _ _) hδ0l) hδ0u
  have h1δ : 1 - δ0 < β := by
    have h := (le_max_left (1 - β) 0).trans_lt hδ0l
    linarith
  exact badNonSingleton_interval_bound_of_squeeze hc hSev h1δ hC

end JSP314
