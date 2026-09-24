import JSP314.Main
import JSP314.SmoothLB4
import Mathlib.Tactic

/-!
# JSP-000314 — sharp-exponent squeeze at a *single* z-scale constant

The exponential-gap squeeze of `SqueezeZ`/`FinalGlue` asks for
`N(x) ≤ x·exp(−C_N·s)·(log x)^{-(1-ε)}` with `C_N > C_S` where
`S(x) ≥ x·exp(−C_S·s)`.  That frame is (believed) **vacuous**: the truth is
`N(x) ~ S(x)·(log x)^{-1+o(1)}` with `S ~ x·exp(−2√2·s)`, so an upper bound
on `N` at any constant `C_N > 2√2` is false — `N` decays at the *same*
exponential rate as `S`.

The corrected frame keeps the exponent `C` **equal** on both sides and puts
the whole gap into the *polylogarithmic* exponent:

* singleton lower bound:  `S(x) ≥ x·exp(−C·s)·(log x)^{−A}`;
* non-singleton upper bound: `N(x) ≤ x·exp(−C·s)·(log x)^{−B}`;

with `B > A + 1`.  Then

  `N(x)/S(x) ≤ (log x)^{A−B}`  and  `A − B < −1`,

so for every `ε > 0`, `A − B < −1 < −(1−ε)` and monotonicity of
`L ↦ L^t` on `L ≥ 1` gives `(log x)^{A−B} ≤ (log x)^{−(1−ε)}`, hence

  `N(x) ≤ (log x)^{−(1−ε)}·S(x)`  eventually.

The common factor `x·exp(−C·s)` cancels *exactly* — no limit argument on
`s = √(log x·log log x)` is needed at all; the proof is pure `rpow`
bookkeeping plus `Real.rpow_le_rpow_of_exponent_le`.  In particular the
lemma is **uniform in the exponent `C`**: any future constant (e.g. the
sharp `2√2`, or a larger proved value) plugs in unchanged.

## Contents

* `badNonSingleton_interval_bound_of_sharp` — the general glue at one
  exponent `C`, with `S`-loss `(log x)^{-A}` and `N`-exponent `B > A + 1`.
* `badNonSingleton_interval_bound_of_sharp_razor` — razor-edge variant:
  `N ≤ x·exp(−C·s)·(log x)^{-1-η}` with `η > A`.
* `badNonSingleton_interval_bound_of_sharp_SLB4` — the singleton lower bound
  instantiated from `SmoothLB4.badSingletonCount_eventually_ge_zscale_two`
  (loss-free: `A = 0`), so `hN` is needed only at `B > 1` with `C > 2√2`.
* `badNonSingleton_interval_bound_of_sharp_SLB4_razor` — razor-edge version
  of the previous corollary: `hN` at `N ≤ x·exp(−C·s)·(log x)^{-1-η}` for
  any `η > 0` and `C > 2√2`.
-/

namespace JSP314

open Filter

/-- **Sharp squeeze at equal exponent.**

If `S(x) ≥ x·exp(−C·s)·(log x)^{-A}` and `N(x) ≤ x·exp(−C·s)·(log x)^{-B}`
eventually, at the **same** constant `C`, with `B > A + 1`, then for every
`ε > 0`, eventually `N(x) ≤ (log x)^{-(1-ε)}·S(x)` — the conclusion of
`badNonSingleton_interval_bound` (`Main.lean`).

Proof: split `(log x)^{-B} = (log x)^{-A}·(log x)^{A-B}`; the common factor
`x·exp(−C·s)·(log x)^{-A}` is nonnegative and `≤ S(x)`, while
`(log x)^{A-B} ≤ (log x)^{-(1-ε)}` because `A - B < -1 < -(1-ε)` and
`log x ≥ 1` eventually. -/
theorem badNonSingleton_interval_bound_of_sharp {C A B : ℝ}
    (hAB : A + 1 < B)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-A)
        ≤ (badSingletonCount x : ℝ))
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-B)) :
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
  have hxnn : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  -- split `L^{-B} = L^{-A}·L^{A-B}`.
  have hsplit : L ^ (-B) = L ^ (-A) * L ^ (A - B) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  -- `L^{A-B} ≤ L^{-(1-ε)}` since `A - B < -1 < ε - 1 = -(1-ε)` and `L ≥ 1`.
  have hpow : L ^ (A - B) ≤ L ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  -- the common factor `x·exp(−C·s)·L^{-A}` is nonnegative.
  have hfront : (0 : ℝ) ≤ (x : ℝ) * Real.exp (-C * s) * L ^ (-A) :=
    mul_nonneg (mul_nonneg hxnn (Real.exp_pos _).le)
      (Real.rpow_nonneg hLpos.le _)
  calc (badNonSingletonCount x : ℝ)
      ≤ x * Real.exp (-C * s) * L ^ (-B) := hNx
    _ = (x * Real.exp (-C * s) * L ^ (-A)) * L ^ (A - B) := by
        rw [hsplit]; ring
    _ ≤ (x * Real.exp (-C * s) * L ^ (-A)) * L ^ (-(1 - ε)) :=
        mul_le_mul_of_nonneg_left hpow hfront
    _ = L ^ (-(1 - ε)) * (x * Real.exp (-C * s) * L ^ (-A)) := by ring
    _ ≤ L ^ (-(1 - ε)) * badSingletonCount x :=
        mul_le_mul_of_nonneg_left hSx (Real.rpow_nonneg hLpos.le _)

/-- **Razor-edge variant.**

`hN` has the shape `N(x) ≤ x·exp(−C·s)·(log x)^{-1-η}` — the believed true
rate `N ~ S·(log x)^{-1+o(1)}` — and `hS` loses `(log x)^{-A}` at the same
constant `C`.  The condition `B = 1 + η > A + 1` is `η > A`. -/
theorem badNonSingleton_interval_bound_of_sharp_razor {C A η : ℝ}
    (hAη : A < η)
    (hS : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-A)
        ≤ (badSingletonCount x : ℝ))
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-1 - η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  have hB : A + 1 < 1 + η := by linarith
  refine badNonSingleton_interval_bound_of_sharp (B := 1 + η) hB hS ?_
  filter_upwards [hN] with x hx
  have hexp : (-(1 : ℝ) - η) = -(1 + η) := by ring
  rwa [hexp] at hx

/-- **Corollary: `hN` is the only remaining hypothesis (via `SmoothLB4`).**

The singleton lower bound is already **proved** in this repository at every
constant `C > 2·√2` with *no* polylogarithmic loss
(`SmoothLB4.badSingletonCount_eventually_ge_zscale_two`), i.e. `A = 0`.
Hence the residual `badNonSingleton_interval_bound` follows from `hN` alone:
at any `C > 2√2`, an eventual bound
`N(x) ≤ x·exp(−C·s)·(log x)^{-B}` with `B > 1` suffices. -/
theorem badNonSingleton_interval_bound_of_sharp_SLB4 {C B : ℝ}
    (hC : 2 * Real.sqrt 2 < C) (hB : 1 < B)
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-B)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  have hS0 := SmoothLB4.badSingletonCount_eventually_ge_zscale_two C hC
  refine badNonSingleton_interval_bound_of_sharp (A := 0) (B := B)
    (by linarith) ?_ hN
  -- `x·exp(−C·s)·L^{-0} = x·exp(−C·s)`.
  filter_upwards [hS0] with x hx
  simpa using hx

/-- **Corollary, razor-edge shape.**  At any `C > 2√2`, if eventually
`N(x) ≤ x·exp(−C·s)·(log x)^{-1-η}` for some `η > 0`, then
`badNonSingleton_interval_bound` holds.  (Instance of
`badNonSingleton_interval_bound_of_sharp_SLB4` at `B = 1 + η`.) -/
theorem badNonSingleton_interval_bound_of_sharp_SLB4_razor {C η : ℝ}
    (hC : 2 * Real.sqrt 2 < C) (hη : 0 < η)
    (hN : ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (-1 - η)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  refine badNonSingleton_interval_bound_of_sharp_SLB4 (B := 1 + η) hC
    (by linarith) ?_
  filter_upwards [hN] with x hx
  have hexp : (-(1 : ℝ) - η) = -(1 + η) := by ring
  rwa [hexp] at hx

end JSP314
