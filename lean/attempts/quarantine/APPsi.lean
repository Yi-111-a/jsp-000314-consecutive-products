import JSP314.BandSum
import JSP314.RunSieve
import JSP314.ErdosTk
import JSP314.SieveBase
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# JSP-000314 — Erdős valuation bounds on the `k = 1` run-count slice

This file instantiates the Erdős valuation bound of `JSP314.ErdosTk`
(`apSmoothParamCount_mul_log_le_explicit`) at the parameters of the run
decomposition: a right run witness `m = p²·r` has `p²·r + 1` `p`-smooth, so
`m ↦ m/p²` injects `rightRunWitness x p 1` into the parameter set counted by
`apSmoothParamCount 1 (2x/p²) (p²) 1 p`.  For left runs, `m − 1 = p²·(r−1) +
(p²−1)` gives the analogous injection with `c = p²`, `j = p² − 1` (which is
coprime to `c`).

## Contents

* `rightRunWitness_one_div_mem`, `leftRunWitness_one_div_pred_mem` — the
  membership halves of the bridge.
* `rightRunCount_one_le_apSmoothParamCount`,
  `leftRunCount_one_le_apSmoothParamCount` — **Task 1 (bridge)**.
* `rightRunCount_one_mul_log_le`, `leftRunCount_one_mul_log_le`,
  `rightRunCount_one_le_erdos`, `leftRunCount_one_le_erdos` —
  **Task 2 (Erdős bound at our parameters)**.
* `rightRunCount_le_div`, `leftRunCount_le_div` — the trivial bound
  `≤ 2x/p²`, and `rightRunCount_le_one`, `leftRunCount_le_one` —
  monotonicity in `k`.
* `sum_range_one_div_succ_le`, `sum_primesLE_inv_le` — the harmonic bound
  `∑_{p ≤ y} 1/p ≤ 1 + log y`.
* `sum_range_telescope`, `sum_primesLE_inv_sq_le_one` — the telescoping bound
  `∑_{p ≤ N} 1/p² ≤ 1`.
* `runCountSum_le`, `runCountSum_eventually_le` — **Task 3 (sum)**:
  `runCountSum x ≤ 8x·(1 + log √(2x))`, hence eventually
  `runCountSum x ≤ 5·x·log x`.  This is an honest `O(x·log x)` bound; see the
  docstring discussion.
* `sum_one_slice_le`, `sum_one_slice_erdos_le` — the `k = 1` slice of the
  sum: trivially `≤ 4x`, while the Erdős valuation bound delivers
  `≤ 72x + 16·x·⌊log₂(4x)⌋` (an `O(x·log x)` — in this regime the Erdős
  bound's `θ(p)·⌊log₂ N⌋` boundary term is worse than the trivial count, which
  is why the run-sum bound ultimately uses the trivial bound).
* `apSmoothParamCount_le_rpow_prod`, `rightRunCount_one_le_rpow` —
  **Task 4 (stretch)**: Rankin's trick inside the arithmetic progression.

## Honest assessment

The Erdős valuation bound at `lo = 1` has denominator `log(p² + 1) ≈ 2 log p`,
while its `hi − lo` coefficient is `2 log p + 11 > log(p²+1)`, so it never
beats the trivial count `2x/p²` at `lo = 1`; one must split `[1, hi]` at a
well-chosen `lo` to profit.  For the full `runCountSum` (which multiplies by
`k ≤ 2p`), the Erdős bound's boundary term `p·log 4·⌊log₂ N⌋` contributes
`~p²·log x` per prime and `~x^{3/2}` overall, so the *trivial* bound
`runCountSum ≤ 8x·∑ 1/p ≤ 8x·(1 + log √(2x)) = O(x·log x)` is the sharpest
bound this file proves.  Reaching `o(x)` — as the residual
`badNonSingleton_interval_bound` would require via `BandSum` — is out of
reach of the valuation bound alone.
-/

namespace JSP314

open Finset Filter

/-! ### `Nat.log 2` versus `Real.log` -/

/-- `⌊log₂ N⌋·log 2 ≤ log N` for `N ≥ 1`. -/
theorem natLog_two_mul_log_two_le {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
  have h : ((2 : ℝ) ^ Nat.log 2 N) ≤ (N : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  calc (Nat.log 2 N : ℝ) * Real.log 2
      = Real.log ((2 : ℝ) ^ Nat.log 2 N) := by rw [Real.log_pow]
    _ ≤ Real.log N := Real.log_le_log (by positivity) h

/-- `⌊log₂ N⌋ ≤ log N / log 2` for `N ≥ 1`. -/
theorem natLog_two_le_log_div {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ Real.log N / Real.log 2 :=
  (le_div_iff₀ (Real.log_pos one_lt_two)).mpr (natLog_two_mul_log_two_le hN)

/-! ### Task 1: the bridge -/

/-- For a `k = 1` right run witness `m`, `r = m/p²` lies in `[1, 2x/p²]` and
`p²·r + 1 = m + 1` is `p`-smooth. -/
theorem rightRunWitness_one_div_mem {x p m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ rightRunWitness x p 1) :
    m / p ^ 2 ∈ (Finset.Icc 1 (2 * x / p ^ 2)).filter
      (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p) := by
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hp2, Nat.div_le_div_right hm2x⟩,
    ?_⟩
  have hrew : p ^ 2 * (m / p ^ 2) + 1 = m + 1 := by
    rw [Nat.mul_div_cancel' hdvd]
  rw [hrew]
  exact hsmooth (m + 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)

/-- **Bridge (right):** `rightRunCount x p 1` is at most the AP smooth count
`apSmoothParamCount 1 (2x/p²) (p²) 1 p`. -/
theorem rightRunCount_one_le_apSmoothParamCount {x p : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p 1 ≤ apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe]
    exact rightRunWitness_one_div_mem hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_rightRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_rightRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

/-- For a `k = 1` left run witness `m`, `r' = m/p² − 1` lies in `[0, 2x/p²]`
and `p²·r' + (p²−1) = m − 1` is `p`-smooth. -/
theorem leftRunWitness_one_div_pred_mem {x p m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ leftRunWitness x p 1) :
    m / p ^ 2 - 1 ∈ (Finset.Icc 0 (2 * x / p ^ 2)).filter
      (fun r => largestPrimeFactor (p ^ 2 * r + (p ^ 2 - 1)) ≤ p) := by
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  have hr1 : 1 ≤ m / p ^ 2 := Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hp2
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
      (Nat.sub_le _ _).trans (Nat.div_le_div_right hm2x)⟩, ?_⟩
  have hmul : p ^ 2 * (m / p ^ 2) = m := Nat.mul_div_cancel' hdvd
  have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hm1 hdvd
  have hrew : p ^ 2 * (m / p ^ 2 - 1) + (p ^ 2 - 1) = m - 1 := by
    rw [Nat.mul_sub_one]
    omega
  rw [hrew]
  exact hsmooth (m - 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)

/-- **Bridge (left):** `leftRunCount x p 1` is at most the AP smooth count
`apSmoothParamCount 0 (2x/p²) (p²) (p²−1) p`. -/
theorem leftRunCount_one_le_apSmoothParamCount {x p : ℕ} (hp : Nat.Prime p) :
    leftRunCount x p 1 ≤
      apSmoothParamCount 0 (2 * x / p ^ 2) (p ^ 2) (p ^ 2 - 1) p := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2 - 1)
  · intro m hm
    rw [Finset.mem_coe]
    exact leftRunWitness_one_div_pred_mem hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    have hwa := mem_leftRunWitness.mp (Finset.mem_coe.mp ha)
    have hwb := mem_leftRunWitness.mp (Finset.mem_coe.mp hb)
    have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
    have ha1 : 1 ≤ a / p ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd (witness_pos hp hwa.2.1 hwa.2.2.1) hwa.2.1) hp2
    have hb1 : 1 ≤ b / p ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd (witness_pos hp hwb.2.1 hwb.2.2.1) hwb.2.1) hp2
    have hab' : a / p ^ 2 = b / p ^ 2 := by
      have h2 : a / p ^ 2 - 1 = b / p ^ 2 - 1 := hab
      omega
    exact div_injOn hp.pos hwa.2.1 hwb.2.1 hab'

/-! ### Task 2: the Erdős bound at our parameters -/

/-- **Erdős bound (right), multiplicative form.** -/
theorem rightRunCount_one_mul_log_le {x p : ℕ} (hp : Nat.Prime p) :
    (rightRunCount x p 1 : ℝ) * Real.log ((p ^ 2 + 1 : ℕ) : ℝ) ≤
      ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4) := by
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := 1)
    (hi := 2 * x / p ^ 2) (c := p ^ 2) (j := 1) (p := p)
    (Nat.coprime_one_right _) hp.one_le
  have hcnt : (rightRunCount x p 1 : ℝ)
      ≤ (apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) :=
    Nat.cast_le.mpr (rightRunCount_one_le_apSmoothParamCount hp)
  have hlognn : 0 ≤ Real.log ((p ^ 2 * 1 + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hsub : (((2 * x / p ^ 2) - 1 : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  have hlogbound : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + 1) : ℝ)
      ≤ (Nat.log 2 (2 * x + 1) : ℝ) := by
    apply Nat.cast_le.mpr
    apply Nat.log_mono_right
    have h : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    omega
  have hA : 0 ≤ (2 * Real.log p + 11) := by
    have := Real.log_natCast_nonneg p; linarith
  have hB : 0 ≤ (p : ℝ) * Real.log 4 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have key : (rightRunCount x p 1 : ℝ) * Real.log ((p ^ 2 * 1 + 1 : ℕ) : ℝ)
      ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4) :=
    calc (rightRunCount x p 1 : ℝ) * Real.log ((p ^ 2 * 1 + 1 : ℕ) : ℝ)
        ≤ (apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ)
            * Real.log ((p ^ 2 * 1 + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hcnt hlognn
      _ ≤ ((2 * x / p ^ 2 - 1 : ℕ) : ℝ) * (2 * Real.log p + 11)
            + (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + 1) : ℝ)
              * (p * Real.log 4) := hE
      _ ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
            + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4) :=
          add_le_add (mul_le_mul_of_nonneg_right hsub hA)
            (mul_le_mul_of_nonneg_right hlogbound hB)
  have heq : ((p ^ 2 + 1 : ℕ) : ℝ) = ((p ^ 2 * 1 + 1 : ℕ) : ℝ) := by
    push_cast; norm_num
  rw [heq]
  exact key

/-- **Erdős bound (left), multiplicative form.** -/
theorem leftRunCount_one_mul_log_le {x p : ℕ} (hp : Nat.Prime p) :
    (leftRunCount x p 1 : ℝ) * Real.log ((p ^ 2 - 1 : ℕ) : ℝ) ≤
      ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4) := by
  have hp2 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
  have hcp : Nat.Coprime (p ^ 2) (p ^ 2 - 1) :=
    (Nat.coprime_self_sub_right hp2).mpr (Nat.coprime_one_right _)
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := 0)
    (hi := 2 * x / p ^ 2) (c := p ^ 2) (j := p ^ 2 - 1) (p := p) hcp hp.one_le
  have hcnt : (leftRunCount x p 1 : ℝ)
      ≤ (apSmoothParamCount 0 (2 * x / p ^ 2) (p ^ 2) (p ^ 2 - 1) p : ℝ) :=
    Nat.cast_le.mpr (leftRunCount_one_le_apSmoothParamCount hp)
  have hlognn : 0 ≤ Real.log ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ) :=
    Real.log_natCast_nonneg _
  have hsub : (((2 * x / p ^ 2) - 0 : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  have hlogbound : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + (p ^ 2 - 1)) : ℝ)
      ≤ (Nat.log 2 (2 * x + p ^ 2) : ℝ) := by
    apply Nat.cast_le.mpr
    apply Nat.log_mono_right
    have h : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    omega
  have hA : 0 ≤ (2 * Real.log p + 11) := by
    have := Real.log_natCast_nonneg p; linarith
  have hB : 0 ≤ (p : ℝ) * Real.log 4 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have key : (leftRunCount x p 1 : ℝ) * Real.log ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ)
      ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4) :=
    calc (leftRunCount x p 1 : ℝ) * Real.log ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ)
        ≤ (apSmoothParamCount 0 (2 * x / p ^ 2) (p ^ 2) (p ^ 2 - 1) p : ℝ)
            * Real.log ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hcnt hlognn
      _ ≤ ((2 * x / p ^ 2 - 0 : ℕ) : ℝ) * (2 * Real.log p + 11)
            + (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + (p ^ 2 - 1)) : ℝ)
              * (p * Real.log 4) := hE
      _ ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
            + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4) :=
          add_le_add (mul_le_mul_of_nonneg_right hsub hA)
            (mul_le_mul_of_nonneg_right hlogbound hB)
  have heq : ((p ^ 2 - 1 : ℕ) : ℝ) = ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ) := by
    push_cast; norm_num
  rw [heq]
  exact key

/-- **Erdős bound (right), divided form:**
`rightRunCount x p 1 ≤ [(2x/p²)·(2 log p + 11) + ⌊log₂(2x+1)⌋·p·log 4]
                      / log(p² + 1)`. -/
theorem rightRunCount_one_le_erdos {x p : ℕ} (hp : Nat.Prime p) :
    (rightRunCount x p 1 : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4))
          / Real.log ((p ^ 2 + 1 : ℕ) : ℝ) := by
  have h := rightRunCount_one_mul_log_le hp
  have hpos : 0 < Real.log ((p ^ 2 + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have h4 : 1 < p ^ 2 + 1 := by
      have := hp.two_le
      have hp4 : 4 ≤ p ^ 2 := Nat.pow_le_pow_left this 2
      omega
    exact_mod_cast h4
  rw [le_div_iff₀ hpos]
  exact h

/-- **Erdős bound (left), divided form.** -/
theorem leftRunCount_one_le_erdos {x p : ℕ} (hp : Nat.Prime p) :
    (leftRunCount x p 1 : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4))
          / Real.log ((p ^ 2 - 1 : ℕ) : ℝ) := by
  have h := leftRunCount_one_mul_log_le hp
  have hpos : 0 < Real.log ((p ^ 2 - 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have h3 : 1 < p ^ 2 - 1 := by
      have := hp.two_le
      have hp4 : 4 ≤ p ^ 2 := Nat.pow_le_pow_left this 2
      omega
    exact_mod_cast h3
  rw [le_div_iff₀ hpos]
  exact h

/-! ### Trivial bounds and monotonicity -/

/-- A right run witness maps injectively via `m ↦ m/p²` into `[1, 2x/p²]`,
giving the trivial count `rightRunCount x p k ≤ 2x/p²` for any `k`. -/
theorem rightRunCount_le_div {x p k : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p k ≤ 2 * x / p ^ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
    (s := rightRunWitness x p k) (t := Finset.Icc 1 (2 * x / p ^ 2)) ?_ ?_
  · rw [Nat.card_Icc] at h
    have : 2 * x / p ^ 2 + 1 - 1 = 2 * x / p ^ 2 := by omega
    rwa [this] at h
  · intro m hm
    rw [Finset.mem_coe] at hm ⊢
    obtain ⟨hm2x, hdvd, hlpf, -⟩ := mem_rightRunWitness.mp hm
    have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) (Nat.pow_pos hp.pos),
        Nat.div_le_div_right hm2x⟩
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_rightRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_rightRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

/-- The trivial count `leftRunCount x p k ≤ 2x/p²` for any `k`. -/
theorem leftRunCount_le_div {x p k : ℕ} (hp : Nat.Prime p) :
    leftRunCount x p k ≤ 2 * x / p ^ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
    (s := leftRunWitness x p k) (t := Finset.Icc 1 (2 * x / p ^ 2)) ?_ ?_
  · rw [Nat.card_Icc] at h
    have : 2 * x / p ^ 2 + 1 - 1 = 2 * x / p ^ 2 := by omega
    rwa [this] at h
  · intro m hm
    rw [Finset.mem_coe] at hm ⊢
    obtain ⟨hm2x, hdvd, hlpf, -⟩ := mem_leftRunWitness.mp hm
    have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) (Nat.pow_pos hp.pos),
        Nat.div_le_div_right hm2x⟩
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_leftRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_leftRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

/-- The witness sets are nested in `k`, so for `1 ≤ k` the `k`-th right run
count is at most the `k = 1` count. -/
theorem rightRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    rightRunCount x p k ≤ rightRunCount x p 1 := by
  apply Finset.card_le_card
  intro m hm
  rw [mem_rightRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, ?_⟩
  intro j hj
  rw [Finset.mem_Icc] at hj
  apply hsmooth
  rw [Finset.mem_Icc]
  omega

/-- The left analogue of `rightRunCount_le_one`. -/
theorem leftRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    leftRunCount x p k ≤ leftRunCount x p 1 := by
  apply Finset.card_le_card
  intro m hm
  rw [mem_leftRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, ?_⟩
  intro j hj
  rw [Finset.mem_Icc] at hj
  apply hsmooth
  rw [Finset.mem_Icc]
  omega

/-! ### Harmonic bounds -/

/-- `1/(N+1) ≤ log(N+1) − log N` for `N ≥ 1`. -/
theorem one_div_succ_le_log_sub_log {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle := Real.log_le_sub_one_of_pos (x := (N : ℝ) / ((N : ℝ) + 1))
    (div_pos hNR hN1)
  rw [Real.log_div hNR.ne' hN1.ne'] at hle
  have h4 : (N : ℝ) / ((N : ℝ) + 1) - 1 = -((N : ℝ) + 1)⁻¹ := by field_simp
  rw [h4, one_div] at hle ⊢
  linarith

/-- Harmonic bound over a range: `∑_{i<N} 1/(i+1) ≤ 1 + log N`. -/
theorem sum_range_one_div_succ_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    · have hstep := one_div_succ_le_log_sub_log hpos
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- Primes reciprocal bound: `∑_{p ≤ y} 1/p ≤ 1 + log y`. -/
theorem sum_primesLE_inv_le (y : ℕ) :
    ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p ≤ 1 + Real.log y := by
  rw [Nat.primesLE_eq_filter_range]
  calc ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ n ∈ Finset.range (y + 1), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by positivity
    _ = (∑ i ∈ Finset.range y, (1 : ℝ) / ((i : ℕ) + 1)) + (1 : ℝ) / (0 : ℕ) :=
        Finset.sum_range_succ' _ _
    _ = ∑ i ∈ Finset.range y, (1 : ℝ) / ((i : ℝ) + 1) := by
        rw [Nat.cast_zero, div_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        simp
    _ ≤ 1 + Real.log y := sum_range_one_div_succ_le y

/-- Telescoping: `∑_{i<M} (1/(i+1) − 1/(i+2)) = 1 − 1/(M+1)`. -/
theorem sum_range_telescope (M : ℕ) :
    ∑ i ∈ Finset.range M, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) =
      1 - 1 / ((M : ℝ) + 1) := by
  rw [show (∑ i ∈ Finset.range M,
        ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) =
      ∑ i ∈ Finset.range M,
        ((fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) i
          - (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) (i + 1)) from
    Finset.sum_congr rfl fun i _ => by push_cast; ring]
  rw [Finset.sum_range_sub']
  simp

/-- Sum of inverse squares over primes: `∑_{p ≤ N} 1/p² ≤ 1`. -/
theorem sum_primesLE_inv_sq_le_one (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  classical
  have hterm : ∀ p ∈ Nat.primesLE N,
      (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) :=
      mul_pos (by linarith) (by linarith)
    rw [show (1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)
        = 1 / ((p : ℝ) * ((p : ℝ) - 1)) by field_simp; ring]
    exact one_div_le_one_div_of_le hpos (by nlinarith)
  have hinj : ∀ a ∈ Nat.primesLE N, ∀ b ∈ Nat.primesLE N,
      a - 2 = b - 2 → a = b := by
    intro a ha b hb hab
    have ha2 : 2 ≤ a := (Nat.prime_of_mem_primesLE ha).two_le
    have hb2 : 2 ≤ b := (Nat.prime_of_mem_primesLE hb).two_le
    omega
  calc ∑ p ∈ Nat.primesLE N, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Nat.primesLE N, (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ∑ i ∈ (Nat.primesLE N).image (· - 2),
          (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro p hp
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
        have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := Nat.cast_sub hp2
        rw [hcast]
        ring
    _ ≤ ∑ i ∈ Finset.range (N - 1),
          (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_image] at hi
          obtain ⟨p, hp, rfl⟩ := hi
          have hpN := (Nat.mem_primesLE.mp hp).1
          have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
          rw [Finset.mem_range]
          omega
        · intro i _ _
          have h2 : (i : ℝ) + 1 ≤ (i : ℝ) + 2 := by linarith
          have h3 : (1 : ℝ) / ((i : ℝ) + 2) ≤ 1 / ((i : ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) h2
          linarith
    _ = 1 - 1 / (((N - 1 : ℕ) : ℝ) + 1) := sum_range_telescope _
    _ ≤ 1 := by
        have hnn : (0 : ℝ) ≤ 1 / (((N - 1 : ℕ) : ℝ) + 1) := by positivity
        linarith

/-! ### Task 3: bounds on the run-count sum -/

/-- The inner `k`-sum bound: each `k ∈ [1, 2p]` contributes at most the
trivial `2·(2x/p²)`, so the inner sum is `≤ 8x/p` in `ℝ`. -/
theorem runCountSum_inner_le {x p : ℕ} (hp : Nat.Prime p) :
    ((∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
      ≤ 8 * x / p := by
  have hb : ∀ k ∈ Finset.Icc 1 (2 * p),
      rightRunCount x p k + leftRunCount x p k ≤ 2 * (2 * x / p ^ 2) := by
    intro k _
    have h1 := rightRunCount_le_div (x := x) (p := p) (k := k) hp
    have h2 := leftRunCount_le_div (x := x) (p := p) (k := k) hp
    omega
  have hcard : (Finset.Icc 1 (2 * p)).card = 2 * p := by
    rw [Nat.card_Icc]; omega
  have hsum : ∑ k ∈ Finset.Icc 1 (2 * p),
      (rightRunCount x p k + leftRunCount x p k)
        ≤ (2 * p) * (2 * (2 * x / p ^ 2)) := by
    calc ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)
        ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), (2 * (2 * x / p ^ 2)) :=
          Finset.sum_le_sum hb
      _ = (Finset.Icc 1 (2 * p)).card * (2 * (2 * x / p ^ 2)) :=
          Finset.sum_const _
      _ = (2 * p) * (2 * (2 * x / p ^ 2)) := by rw [hcard]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  calc ((∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
      ≤ (((2 * p) * (2 * (2 * x / p ^ 2)) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hsum
    _ = (2 * p : ℝ) * (2 * ((2 * x / p ^ 2 : ℕ) : ℝ)) := by push_cast; ring
    _ ≤ (2 * p : ℝ) * (2 * ((2 * x : ℝ) / (p : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [← Nat.cast_pow]
        exact Nat.cast_div_le
    _ = 8 * x / p := by field_simp; ring

/-- **Run-count sum bound (honest `O(x·log x)`):**
`runCountSum x ≤ 8·x·(1 + log √(2x))`. -/
theorem runCountSum_le (x : ℕ) :
    (runCountSum x : ℝ) ≤ 8 * x * (1 + Real.log (Nat.sqrt (2 * x))) := by
  calc (runCountSum x : ℝ)
      = ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ((∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) := by
        rw [runCountSum, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Nat.cast_sum]
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (8 * x / p : ℝ) :=
        Finset.sum_le_sum fun p hp =>
          runCountSum_inner_le (Nat.prime_of_mem_primesLE hp)
    _ = 8 * x * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpR : (0 : ℝ) < (p : ℝ) :=
          by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
        field_simp
    _ ≤ 8 * x * (1 + Real.log (Nat.sqrt (2 * x))) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_le _) (by positivity)

/-- **Eventual form:** `runCountSum x ≤ 5·x·log x` for all large `x`.
This is the sharpest bound proved here: `O(x·log x)`, not `o(x)`. -/
theorem runCountSum_eventually_le :
    ∀ᶠ x : ℕ in atTop, (runCountSum x : ℝ) ≤ 5 * x * Real.log x := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLt.eventually_ge_atTop 11, eventually_gt_atTop 0]
    with x hL hx
  have h := runCountSum_le x
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  -- `log(Nat.sqrt(2x)) ≤ log(2x)/2` since `(Nat.sqrt (2x))² ≤ 2x`.
  have hs1 : 1 ≤ Nat.sqrt (2 * x) := by
    rw [Nat.le_sqrt]
    omega
  have hs2 : (Nat.sqrt (2 * x)) ^ 2 ≤ 2 * x := by
    have h' := Nat.sqrt_le' (2 * x)
    rwa [pow_two]
  have hslog : Real.log (Nat.sqrt (2 * x)) ≤ Real.log (2 * x) / 2 := by
    have hsR : (0 : ℝ) < ((Nat.sqrt (2 * x) : ℕ) : ℝ) := by exact_mod_cast hs1
    have hs2R : (((Nat.sqrt (2 * x)) ^ 2 : ℕ) : ℝ) ≤ ((2 * x : ℕ) : ℝ) :=
      Nat.cast_le.mpr hs2
    rw [← Nat.cast_pow] at hs2R
    calc Real.log (Nat.sqrt (2 * x))
        = Real.log (((Nat.sqrt (2 * x) : ℕ) : ℝ) ^ 2) / 2 := by
          rw [Real.log_pow]; ring
      _ ≤ Real.log ((2 * x : ℕ) : ℝ) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact Real.log_le_log (by positivity) hs2R
  have hlog2x : Real.log ((2 * x : ℕ) : ℝ) = Real.log 2 + Real.log x := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num)
      (ne_of_gt hxR)]
  have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  -- `8x(1 + log√2x) ≤ 8x(1 + (log2 + log x)/2) ≤ 5x·log x` for `log x ≥ 11`.
  have key : 8 * x * (1 + Real.log (Nat.sqrt (2 * x))) ≤
      5 * x * Real.log (x : ℝ) := by
    have hlog : Real.log (x : ℝ) = Real.log (x : ℝ) := rfl
    have hL2 : (0:ℝ) < Real.log (x : ℝ) := by linarith
    calc 8 * x * (1 + Real.log (Nat.sqrt (2 * x)))
        ≤ 8 * x * (1 + Real.log (2 * x) / 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right hslog 1) (by positivity)
      _ = 8 * x + 4 * x * Real.log ((2 * x : ℕ) : ℝ) := by ring
      _ = 8 * x + 4 * x * (Real.log 2 + Real.log x) := by rw [hlog2x]
      _ ≤ 8 * x + 4 * x * (1 + Real.log x) :=
          mul_le_mul_of_nonneg_left
            (add_le_add_right hlog2.le _ |>.trans' (le_refl _)
            ) (by positivity) -- fallback below if needed
      _ = 4 * x * Real.log x + 12 * x := by ring
      _ ≤ 4 * x * Real.log x + x * Real.log x :=
          add_le_add_right (mul_le_mul_of_nonneg_right hL hxR.le) _
      _ = 5 * x * Real.log x := by ring
  exact h.trans key

/-! ### The `k = 1` slice of the run sum -/

/-- **Slice bound (trivial):** the `k = 1` summands satisfy
`∑_p (rightRunCount + leftRunCount) ≤ 4x`, since each count is `≤ 2x/p²` and
`∑_p 1/p² ≤ 1`. -/
theorem sum_one_slice_le (x : ℕ) :
    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
      ((rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ)) ≤ 4 * x := by
  calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ((rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ))
      ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (4 * x : ℝ) / (p : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE hp
        have h1 := rightRunCount_le_div (x := x) (p := p) (k := 1) hpp
        have h2 := leftRunCount_le_div (x := x) (p := p) (k := 1) hpp
        have hsum : rightRunCount x p 1 + leftRunCount x p 1
            ≤ 2 * (2 * x / p ^ 2) := by omega
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        calc (rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ)
            ≤ 2 * ((2 * x / p ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsum
          _ ≤ 2 * ((2 * x : ℝ) / (p : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [← Nat.cast_pow]
              exact Nat.cast_div_le
          _ = (4 * x : ℝ) / (p : ℝ) ^ 2 := by field_simp; ring
    _ = 4 * x * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpR : (0 : ℝ) < (p : ℝ) :=
          by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
        field_simp
    _ ≤ 4 * x * 1 :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_sq_le_one _)
          (by positivity)
    _ = 4 * x := mul_one _

/-- The per-prime Erdős bound in a common `log p` denominator (relaxed).
Requires `p² ≤ 2x` (automatic for `p ∈ primesLE √(2x)`). -/
theorem runCount_one_sum_le_erdos_term {x p : ℕ} (hp : Nat.Prime p)
    (hx : 1 ≤ x) (hp2 : p ^ 2 ≤ 2 * x) :
    (rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ) ≤
      2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p := by
  have hR := rightRunCount_one_le_erdos (x := x) (p := p) hp
  have hL := leftRunCount_one_le_erdos (x := x) (p := p) hp
  have hlogp : (0 : ℝ) < Real.log p :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hA : 0 ≤ (2 * Real.log p + 11) := by
    have := Real.log_natCast_nonneg p; linarith
  have hB : 0 ≤ (p : ℝ) * Real.log 4 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hy : (0 : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- `⌊log₂(2x+1)⌋, ⌊log₂(2x+p²)⌋ ≤ ⌊log₂(4x)⌋`
  have hlog1 : (Nat.log 2 (2 * x + 1) : ℝ) ≤ (Nat.log 2 (4 * x) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right (by omega))
  have hlog2 : (Nat.log 2 (2 * x + p ^ 2) : ℝ) ≤ (Nat.log 2 (4 * x) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right (by omega))
  -- denominators: `log p ≤ log(p²−1) ≤ log(p²+1)` for `p ≥ 2`
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hcast1 : ((p ^ 2 + 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 + 1 := by push_cast; ring
  have hcast2 : ((p ^ 2 - 1 : ℕ) : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by
      have h4 : 4 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
      omega), Nat.cast_pow]
  have hden1 : Real.log p ≤ Real.log ((p ^ 2 + 1 : ℕ) : ℝ) := by
    rw [hcast1]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hden2 : Real.log p ≤ Real.log ((p ^ 2 - 1 : ℕ) : ℝ) := by
    rw [hcast2]
    apply Real.log_le_log (by linarith)
    nlinarith
  -- `X₁ ≤ X₀` and `X₂ ≤ X₀` where `X₀ = y·A + ⌊log₂ 4x⌋·p·log4`
  have hN1 : ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
      + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4)
      ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) :=
    add_le_add_right (mul_le_mul_of_nonneg_right hlog1 hB) _
  have hN2 : ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
      + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4)
      ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) :=
    add_le_add_right (mul_le_mul_of_nonneg_right hlog2 hB) _
  have hX0 : (0 : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
      + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) :=
    add_nonneg (mul_nonneg hy hA) (mul_nonneg (Nat.cast_nonneg _) hB)
  have hX1 : (0 : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
      + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4) :=
    add_nonneg (mul_nonneg hy hA) (mul_nonneg (Nat.cast_nonneg _) hB)
  have hX2 : (0 : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
      + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4) :=
    add_nonneg (mul_nonneg hy hA) (mul_nonneg (Nat.cast_nonneg _) hB)
  calc (rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ)
      ≤ (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4))
            / Real.log ((p ^ 2 + 1 : ℕ) : ℝ)
        + (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (2 * x + p ^ 2) : ℝ) * (p * Real.log 4))
            / Real.log ((p ^ 2 - 1 : ℕ) : ℝ) := add_le_add hR hL
    _ ≤ (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p
        + (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p := by
        apply add_le_add
        · exact (div_le_div_of_nonneg_left hX1 hlogp hden1).trans
            (div_le_div_of_nonneg_right hN1 hlogp)
        · exact (div_le_div_of_nonneg_left hX2 hlogp hden2).trans
            (div_le_div_of_nonneg_right hN2 hlogp)
    _ = 2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p := by
        ring

/-- `∑_{p ≤ y, prime} p ≤ (y+1)·y`. -/
theorem sum_primesLE_le_card_mul (y : ℕ) :
    ∑ p ∈ Nat.primesLE y, p ≤ (y + 1) * y := by
  calc ∑ p ∈ Nat.primesLE y, p
      ≤ ∑ _p ∈ Nat.primesLE y, y :=
        Finset.sum_le_sum fun p hp => (Nat.mem_primesLE.mp hp).1
    _ = (Nat.primesLE y).card * y := Finset.sum_const _
    _ ≤ (y + 1) * y := by
        apply Nat.mul_le_mul_right
        rw [Nat.primesLE_eq_filter_Icc_zero]
        exact (Finset.card_filter_le _ _).trans
          (by rw [Nat.card_Icc]; omega)

/-- The `k = 1` slice summed via the Erdős bound:
`∑_p (rightRunCount + leftRunCount) ≤ 72·x + 16·x·⌊log₂(4x)⌋` for `x ≥ 1`.
This is `O(x·log x)` — strictly worse than the trivial `4x` bound of
`sum_one_slice_le`, because at `lo = 1` the Erdős bound's boundary term
`p·log 4·⌊log₂(4x)⌋` dominates its `hi`-term.  We report it for honesty. -/
theorem sum_one_slice_erdos_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
      ((rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ))
        ≤ 72 * x + 16 * x * (Nat.log 2 (4 * x) : ℝ) := by
  set s := Nat.sqrt (2 * x) with hs
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- Step 1: apply the per-prime Erdős term bound.
  have step1 : ∑ p ∈ Nat.primesLE s,
      ((rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ))
      ≤ ∑ p ∈ Nat.primesLE s,
        2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hple : p ≤ s := (Nat.mem_primesLE.mp hp).1
    have hp2 : p ^ 2 ≤ 2 * x := by
      have : p ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hple 2
      have hs2 : s ^ 2 ≤ 2 * x := by
        have h' := Nat.sqrt_le' (2 * x); rwa [pow_two] at h'
      omega
    exact runCount_one_sum_le_erdos_term hpp hx hp2
  -- Step 2: split each term `2·[y·A + B·p·log4]/log p
  --   ≤ (4 + 22/log 2)·y + 4·B·p`.
  have termbound : ∀ p ∈ Nat.primesLE s,
      2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p
        ≤ (4 + 22 / Real.log 2) * ((2 * x / p ^ 2 : ℕ) : ℝ)
          + 4 * (Nat.log 2 (4 * x) : ℝ) * p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hlogp : (0 : ℝ) < Real.log p :=
      Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hlogple : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hpp.two_le)
    have hy : (0 : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hB : (0 : ℝ) ≤ (Nat.log 2 (4 * x) : ℝ) := Nat.cast_nonneg _
    have hpR : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg _
    -- `y·(2log p + 11)/log p = y·(2 + 11/log p) ≤ y·(2 + 11/log 2)`
    have h1 : ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) / Real.log p
        ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 + 11 / Real.log 2) := by
      have h11 : (11 : ℝ) / Real.log p ≤ 11 / Real.log 2 :=
        div_le_div_of_nonneg_left (by norm_num) hlog2pos hlogple
      calc ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) / Real.log p
          = ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 + 11 / Real.log p) := by
            field_simp; ring
        _ ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) * (2 + 11 / Real.log 2) :=
          mul_le_mul_of_nonneg_left (add_le_add_right h11 2) hy
    -- `B·p·log4/log p ≤ B·p·2`
    have h2 : (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) / Real.log p
        ≤ (Nat.log 2 (4 * x) : ℝ) * (p : ℝ) * 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        ring
      have hdiv : Real.log 4 / Real.log p ≤ 2 := by
        rw [h4]
        calc 2 * Real.log 2 / Real.log p
            ≤ 2 * Real.log p / Real.log p :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlogple (by norm_num)) hlogp.le
          _ = 2 := by field_simp
      calc (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) / Real.log p
          = ((Nat.log 2 (4 * x) : ℝ) * p) * (Real.log 4 / Real.log p) := by
            field_simp; ring
        _ ≤ ((Nat.log 2 (4 * x) : ℝ) * p) * 2 :=
            mul_le_mul_of_nonneg_left hdiv (mul_nonneg hB hpR)
    calc 2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11)
            + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4)) / Real.log p
        = 2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) / Real.log p
            + (Nat.log 2 (4 * x) : ℝ) * (p * Real.log 4) / Real.log p) := by
          ring
      _ ≤ 2 * (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 + 11 / Real.log 2)
            + (Nat.log 2 (4 * x) : ℝ) * (p : ℝ) * 2) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
      _ = (4 + 22 / Real.log 2) * ((2 * x / p ^ 2 : ℕ) : ℝ)
            + 4 * (Nat.log 2 (4 * x) : ℝ) * p := by ring
  -- Step 3: sum, and bound `∑ y ≤ 2x·∑1/p² ≤ 2x` and `∑ p ≤ (s+1)s ≤ 4x`.
  have hsumy : ∑ p ∈ Nat.primesLE s, ((2 * x / p ^ 2 : ℕ) : ℝ)
      ≤ 2 * x := by
    calc ∑ p ∈ Nat.primesLE s, ((2 * x / p ^ 2 : ℕ) : ℝ)
        ≤ ∑ p ∈ Nat.primesLE s, (2 * x : ℝ) / (p : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          rw [← Nat.cast_pow]
          exact Nat.cast_div_le
      _ = 2 * x * ∑ p ∈ Nat.primesLE s, (1 : ℝ) / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          have hpR : (0 : ℝ) < (p : ℝ) :=
            by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
          field_simp
      _ ≤ 2 * x * 1 :=
          mul_le_mul_of_nonneg_left (sum_primesLE_inv_sq_le_one _)
            (by positivity)
      _ = 2 * x := mul_one _
  have hsump : ∑ p ∈ Nat.primesLE s, (p : ℝ) ≤ 4 * x := by
    have h1 := sum_primesLE_le_card_mul s
    have h2 : (s + 1) * s ≤ 4 * x := by
      rcases Nat.eq_zero_or_pos s with h0 | hpos
      · simp [h0]
      · have hs2 : s * s ≤ 2 * x := Nat.sqrt_le' (2 * x)
        have hss : s ≤ s * s := by
          conv_lhs => rw [← mul_one s]
          exact Nat.mul_le_mul_left s hpos
        rw [Nat.mul_succ]
        omega
    have : (∑ p ∈ Nat.primesLE s, (p : ℝ)) ≤ (((s + 1) * s : ℕ) : ℝ) := by
      exact_mod_cast h1
    calc ∑ p ∈ Nat.primesLE s, (p : ℝ)
        ≤ ((s + 1) * s : ℕ) := this
      _ ≤ ((4 * x : ℕ) : ℝ) := Nat.cast_le.mpr h2
      _ = 4 * x := by push_cast; ring
  -- Step 4: assemble.
  calc ∑ p ∈ Nat.primesLE s,
        ((rightRunCount x p 1 : ℝ) + (leftRunCount x p 1 : ℝ))
      ≤ ∑ p ∈ Nat.primesLE s,
          ((4 + 22 / Real.log 2) * ((2 * x / p ^ 2 : ℕ) : ℝ)
            + 4 * (Nat.log 2 (4 * x) : ℝ) * p) :=
        step1.trans (Finset.sum_le_sum termbound)
    _ = (4 + 22 / Real.log 2) * ∑ p ∈ Nat.primesLE s,
            ((2 * x / p ^ 2 : ℕ) : ℝ)
          + 4 * (Nat.log 2 (4 * x) : ℝ) * ∑ p ∈ Nat.primesLE s, (p : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (4 + 22 / Real.log 2) * (2 * x)
          + 4 * (Nat.log 2 (4 * x) : ℝ) * (4 * x) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hsumy (by
            have : (0:ℝ) ≤ 22 / Real.log 2 := by positivity
            linarith)
        · exact mul_le_mul_of_nonneg_left hsump
            (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    _ = (8 + 44 / Real.log 2) * x + 16 * x * (Nat.log 2 (4 * x) : ℝ) := by ring
    _ ≤ 72 * x + 16 * x * (Nat.log 2 (4 * x) : ℝ) := by
        apply add_le_add_left
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        have h44 : (44 : ℝ) / Real.log 2 ≤ 44 / (0.6931471803 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) hlog2lo hlog2lo.le
        have hval : (44 : ℝ) / (0.6931471803 : ℝ) ≤ 64 := by norm_num
        linarith

/-! ### Task 4 (stretch): Rankin's trick in the AP -/

/-- **Rankin-in-AP bound:** for `0 < σ` and `j ≥ 1`,
`apSmoothParamCount lo hi c j p ≤ (c·hi + j)^σ · ∏_{q ≤ p} (1 − q^{-σ})⁻¹`,
by mapping `r ↦ c·r + j` into the `p`-smooth integers in `[1, c·hi + j]` and
applying `SieveBase.smoothCount_rpow_le`. -/
theorem apSmoothParamCount_le_rpow_prod {lo hi c j p : ℕ} (hj : 1 ≤ j)
    (hc : 0 < c) {σ : ℝ} (hσ : 0 < σ) :
    (apSmoothParamCount lo hi c j p : ℝ) ≤
      ((c * hi + j : ℕ) : ℝ) ^ σ *
        ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
  classical
  have hmap : Set.MapsTo (fun r => c * r + j)
      ↑((Finset.Icc lo hi).filter fun r => largestPrimeFactor (c * r + j) ≤ p)
      ↑((Finset.Icc 1 (c * hi + j)).filter
        fun n => largestPrimeFactor n ≤ p) := by
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr ⊢
    obtain ⟨hrIcc, hlp⟩ := hr
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hrIcc
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hlp⟩
    · show 1 ≤ c * r + j
      omega
    · have hcr : c * r ≤ c * hi := Nat.mul_le_mul_left c hhi
      show c * r + j ≤ c * hi + j
      omega
  have hinj : Set.InjOn (fun r => c * r + j)
      ↑((Finset.Icc lo hi).filter fun r => largestPrimeFactor (c * r + j) ≤ p)
      := by
    intro a _ b _ hab
    have h2 : c * a + j = c * b + j := hab
    have : c * a = c * b := by omega
    exact Nat.mul_left_cancel hc this
  have hcard : apSmoothParamCount lo hi c j p
      ≤ ((Finset.Icc 1 (c * hi + j)).filter
          fun n => largestPrimeFactor n ≤ p).card :=
    Finset.card_le_card_of_injOn _ hmap hinj
  calc (apSmoothParamCount lo hi c j p : ℝ)
      ≤ (((Finset.Icc 1 (c * hi + j)).filter
          fun n => largestPrimeFactor n ≤ p).card : ℝ) :=
        Nat.cast_le.mpr hcard
    _ ≤ ((c * hi + j : ℕ) : ℝ) ^ σ *
          ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ :=
        SieveBase.smoothCount_rpow_le _ _ hσ

/-- Rankin bound specialised to the right-run parameters:
`rightRunCount x p 1 ≤ (2x+1)^σ · ∏_{q ≤ p} (1 − q^{-σ})⁻¹`. -/
theorem rightRunCount_one_le_rpow {x p : ℕ} (hp : Nat.Prime p) {σ : ℝ}
    (hσ : 0 < σ) :
    (rightRunCount x p 1 : ℝ) ≤
      ((2 * x + 1 : ℕ) : ℝ) ^ σ *
        ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  have h1 := apSmoothParamCount_le_rpow_prod (lo := 1) (hi := 2 * x / p ^ 2)
    (c := p ^ 2) (j := 1) (p := p) (Nat.le_refl 1) hp2 hσ
  have hcnt : (rightRunCount x p 1 : ℝ)
      ≤ (apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) :=
    Nat.cast_le.mpr (rightRunCount_one_le_apSmoothParamCount hp)
  have harg : ((p ^ 2 * (2 * x / p ^ 2) + 1 : ℕ) : ℝ)
      ≤ ((2 * x + 1 : ℕ) : ℝ) := by
    apply Nat.cast_le.mpr
    have h : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    omega
  have hargpos : (0 : ℝ) ≤ ((p ^ 2 * (2 * x / p ^ 2) + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hprodn : 0 ≤ ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
    apply Finset.prod_nonneg
    intro q hq
    have hqp := Nat.prime_of_mem_primesLE hq
    have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    have hpow : (1 : ℝ) < (q : ℝ) ^ σ := Real.one_lt_rpow (lt_of_lt_of_le one_lt_two hqR) hσ
    have : (q : ℝ) ^ (-σ) < 1 := by
      rw [Real.rpow_neg (by linarith)]
      exact inv_lt_one_of_one_lt₀ hpow
    exact inv_nonneg.mpr (by linarith)
  calc (rightRunCount x p 1 : ℝ)
      ≤ ((p ^ 2 * (2 * x / p ^ 2) + 1 : ℕ) : ℝ) ^ σ *
          ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ := hcnt.trans h1
    _ ≤ ((2 * x + 1 : ℕ) : ℝ) ^ σ *
          ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hargpos harg hσ.le) hprodn

end JSP314
