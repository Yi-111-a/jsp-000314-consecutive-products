import JSP314.SingletonLBz
import Mathlib.Tactic

/-!
# Lower bound for `badSingletonCount` with constant `2√2`

We improve `SingletonLBz.badSingletonCount_eventually_ge_zscale` (constant
`C = 10`) to *every* constant `C > 2√2`, i.e.

  `S(x) = badSingletonCount x ≥ x · exp(-C·√(log x · loglog x))` eventually.

## Method

Same injection `(p, T) ↦ p² · ∏T` as in `SingletonLBz` (with
`Z = ⌈exp t⌉₊`), but now `t = s/√2` where `s = √(L·L₂)`, and a tighter
`u = ⌊(L-4)/(t+2)⌋ - 2`-type choice: concretely `u = ⌊w⌋₊` with
`w = (L-4)/(t+2) - 2`.

The bookkeeping: `t + u·t ≥ w·t = L - 2t - 2L/(t+2) - O(1)`, and the
denominator `4(t+2)·(16(t+1))^u·u^u ≤ L·(32L)^u` (since
`16(t+1)·u ≤ 16(t+1)·L/t ≤ 32L`), whose logarithm is
`L₂ + u·(L₂ + log 32) ≤ L₂ + √2·s + o(s)`.  Total loss
`2t + s²/t + o(s) = (2c + 1/c)s` at `t = c·s`, minimized at `c = 1/√2`,
giving `2√2·s + o(s)`.
-/

namespace JSP314

namespace SmoothLB4

open Finset Filter SmoothLB

open scoped Topology

set_option maxHeartbeats 1600000 in
/-- For every `C > 2√2`, eventually
`badSingletonCount x ≥ x·exp(-C·√(log x·loglog x))`. -/
theorem badSingletonCount_eventually_ge_zscale_two :
    ∀ C : ℝ, 2 * Real.sqrt 2 < C → ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) := by
  intro C hC
  -- `√2` facts
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2ge1 : 1 ≤ Real.sqrt 2 := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.sqrt_one] at h
  have hs2le2 : Real.sqrt 2 ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num)
    rwa [h4] at h
  -- `ε = C - 2√2 > 0`
  set ε : ℝ := C - 2 * Real.sqrt 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith [hC]
  -- `L = log x → ∞`, `L2 = log log x → ∞`, `L2/L → 0`
  have hLt : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop
      Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Filter.Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hLt
  have hratio : Filter.Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      Filter.atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hLt).tendsto_div_nhds_zero
  have h64 : ∀ᶠ x : ℕ in Filter.atTop,
      64 * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have h := hratio.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))
    filter_upwards [h, hLt.eventually_ge_atTop 1] with x hx hL1
    have hLpos : (0 : ℝ) < Real.log x := by linarith
    rw [div_lt_iff₀ hLpos] at hx
    linarith
  -- `L2 ≤ (ε/3)²·L` eventually (since `L2/L → 0`)
  have hδ : ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (Real.log (x : ℝ)) ≤ (ε / 3) ^ 2 * Real.log (x : ℝ) := by
    have h := hratio.eventually (Iio_mem_nhds
      (show (0 : ℝ) < (ε / 3) ^ 2 from pow_pos (by linarith [hε]) _))
    filter_upwards [h, hLt.eventually_ge_atTop 1] with x hx hL1
    have hLpos : (0 : ℝ) < Real.log x := by linarith
    rw [div_lt_iff₀ hLpos] at hx
    linarith [hx]
  -- `8·L2 ≤ √(L·L2)` eventually
  have hA8ev : ∀ᶠ x : ℕ in Filter.atTop,
      8 * Real.log (Real.log (x : ℝ)) ≤
        Real.sqrt (Real.log x * Real.log (Real.log x)) := by
    filter_upwards [h64, hL2t.eventually_ge_atTop 0] with x hx hx2
    set L := Real.log (x : ℝ) with hLdef
    set L2 := Real.log L with hL2def
    have h64sq : (8 * L2) ^ 2 ≤ L * L2 := by
      have h := mul_le_mul_of_nonneg_right hx hx2
      nlinarith [h, hx2]
    calc 8 * L2 = Real.sqrt ((8 * L2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt (L * L2) := Real.sqrt_le_sqrt h64sq
  -- `L2 ≤ (ε/3)·A` eventually
  have hL2A : ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (Real.log (x : ℝ)) ≤
        (ε / 3) * Real.sqrt (Real.log x * Real.log (Real.log x)) := by
    filter_upwards [hδ, hL2t.eventually_ge_atTop 0, hLt.eventually_ge_atTop 1]
      with x hδ' hL2ge hL1
    set L := Real.log (x : ℝ) with hLdef
    set L2 := Real.log L with hL2def
    have hLpos : 0 < L := by linarith
    have h1 : L2 ^ 2 ≤ (ε / 3) ^ 2 * (L * L2) := by
      have h := mul_le_mul_of_nonneg_right hδ' hL2ge
      calc L2 ^ 2 = L2 * L2 := by ring
        _ ≤ (ε / 3) ^ 2 * L * L2 := h
        _ = (ε / 3) ^ 2 * (L * L2) := by ring
    calc L2 = Real.sqrt (L2 ^ 2) := (Real.sqrt_sq hL2ge).symm
      _ ≤ Real.sqrt ((ε / 3) ^ 2 * (L * L2)) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt ((ε / 3) ^ 2) * Real.sqrt (L * L2) :=
          Real.sqrt_mul (sq_nonneg _) _
      _ = (ε / 3) * Real.sqrt (L * L2) := by
          rw [Real.sqrt_sq (by linarith [hε])]
  -- `A → ∞` since `L2 ≤ A` eventually
  have hA1ev : ∀ᶠ x : ℕ in Filter.atTop,
      Real.log (Real.log (x : ℝ)) ≤
        Real.sqrt (Real.log x * Real.log (Real.log x)) := by
    filter_upwards [hA8ev, hL2t.eventually_ge_atTop 0] with x h1 h2
    linarith
  have hAt : Filter.Tendsto
      (fun x : ℕ => Real.sqrt (Real.log x * Real.log (Real.log x)))
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' Filter.atTop hA1ev hL2t
  -- `4·L2 ≤ t` eventually (since `A ≥ 8·L2`, `√2 ≥ 1`)
  have ht4ev : ∀ᶠ x : ℕ in Filter.atTop,
      4 * Real.log (Real.log (x : ℝ)) ≤
        Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2 := by
    filter_upwards [hA8ev, hL2t.eventually_ge_atTop 0] with x h1 h2
    set A := Real.sqrt (Real.log x * Real.log (Real.log x)) with hAdef
    set L2 := Real.log (Real.log (x : ℝ)) with hL2def
    have hApos : 0 ≤ A := Real.sqrt_nonneg _
    have hAs2 : A ≤ A * Real.sqrt 2 := by
      have h := mul_le_mul_of_nonneg_left hs2ge1 hApos
      simpa using h
    linarith [h1, hAs2, h2]
  have h4L2t : Filter.Tendsto
      (fun x : ℕ => 4 * Real.log (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' Filter.atTop
      ((hL2t.eventually_ge_atTop 0).mono fun x h => by linarith) hL2t
  -- `exp t → ∞` and `Z = ⌈e^t⌉ → ∞`, `2Z → ∞`
  have hexp_t : Filter.Tendsto
      (fun x : ℕ => Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_atTop_mono' Filter.atTop ht4ev h4L2t)
  have hZt : Filter.Tendsto
      (fun x : ℕ => ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono' Filter.atTop
        (Filter.Eventually.of_forall fun x => Nat.le_ceil _) hexp_t)
  have h2Zt : Filter.Tendsto
      (fun x : ℕ => 2 * ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun n => le_mul_of_one_le_left (Nat.zero_le _) one_le_two) hZt
  -- dyadic Chebyshev lower bounds along `Z` and `2Z`
  have hDZ : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊ : ℝ) /
          (8 * Real.log ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊)
        ≤ ((dyadicPrimes ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊).card : ℝ) :=
    hZt.eventually eventually_dyadicPrimes_card_ge
  have hD2Z : ∀ᶠ x : ℕ in Filter.atTop,
      ((2 * ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (2 * ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊))
        ≤ ((dyadicPrimes (2 * ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) * Real.sqrt 2 / 2)⌉₊)).card : ℝ) := by
    filter_upwards [h2Zt.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  filter_upwards [h64, hL2A, hAt.eventually_ge_atTop (12 / ε),
    hL2t.eventually_ge_atTop (18 * Real.sqrt 2 / ε), hDZ, hD2Z,
    hLt.eventually_ge_atTop 64, hL2t.eventually_ge_atTop 9,
    eventually_ge_atTop 4]
    with x h64' hL2A' hAge' hL2ge' hDZ' hD2Z' hL hL2 hx4
  -- abbreviations
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set L2 : ℝ := Real.log L with hL2def
  set A : ℝ := Real.sqrt (L * L2) with hAdef
  set t : ℝ := A * Real.sqrt 2 / 2 with htdef
  set Z : ℕ := ⌈Real.exp t⌉₊ with hZdef
  set w : ℝ := (L - 4) / (t + 2) - 2 with hwdef
  set u : ℕ := ⌊w⌋₊ with hudef
  -- basic facts
  have hxp : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hLpos : 0 < L := by linarith
  have hL2pos : 0 < L2 := by linarith
  have hLL2 : 0 ≤ L * L2 := mul_nonneg hLpos.le hL2pos.le
  have hAsq : A ^ 2 = L * L2 := Real.sq_sqrt hLL2
  have hA8 : 8 * L2 ≤ A := by
    have h64sq : (8 * L2) ^ 2 ≤ L * L2 := by
      have h := mul_le_mul_of_nonneg_right h64' hL2pos.le
      nlinarith [h, hL2pos.le]
    calc 8 * L2 = Real.sqrt ((8 * L2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ A := Real.sqrt_le_sqrt h64sq
  have hApos : 0 < A := by linarith [hA8, hL2pos]
  have hAle : A ≤ L / 8 := by
    have hsq : L * L2 ≤ (L / 8) ^ 2 := by nlinarith [h64', hLpos]
    calc A = Real.sqrt (L * L2) := rfl
      _ ≤ Real.sqrt ((L / 8) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = L / 8 := Real.sqrt_sq (by linarith)
  have ht_pos : 0 < t := by
    rw [htdef]; exact div_pos (mul_pos hApos hs2pos) (by norm_num)
  have hAs2 : A ≤ A * Real.sqrt 2 := by
    have h := mul_le_mul_of_nonneg_left hs2ge1 hApos.le
    simpa using h
  have ht_lo : 4 * L2 ≤ t := by rw [htdef]; linarith [hA8, hAs2]
  have hAs2' : A * Real.sqrt 2 ≤ (L / 8) * 2 :=
    mul_le_mul hAle hs2le2 hs2pos.le (by linarith [hLpos])
  have ht_hi : t ≤ L / 8 := by rw [htdef]; linarith [hAs2']
  have h2t : 2 * t = Real.sqrt 2 * A := by rw [htdef]; ring
  have htge1 : (1 : ℝ) ≤ t := by linarith [ht_lo, hL2]
  -- `Z` bounds
  have hexpt1 : Real.exp t ≤ (Z : ℝ) := Nat.le_ceil _
  have hexpt2 : (Z : ℝ) ≤ Real.exp (t + 1) := by
    have h1 : (Z : ℝ) ≤ Real.exp t + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg t)).le
    have he2 : (2 : ℝ) ≤ Real.exp 1 :=
      (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans Real.exp_one_gt_d9.le
    have h2 : Real.exp t + 1 ≤ Real.exp (t + 1) := by
      rw [Real.exp_add]
      have hge : 1 ≤ Real.exp t :=
        Real.exp_zero ▸ Real.exp_le_exp.mpr ht_pos.le
      nlinarith [hge, he2, Real.exp_nonneg t]
    exact h1.trans h2
  have hZ2hi : (2 * (Z : ℝ)) ≤ Real.exp (t + 2) := by
    have he2 : (2 : ℝ) ≤ Real.exp 1 :=
      (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans Real.exp_one_gt_d9.le
    calc 2 * (Z : ℝ) ≤ 2 * Real.exp (t + 1) := by linarith [hexpt2]
      _ ≤ Real.exp 1 * Real.exp (t + 1) :=
          mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg _)
      _ = Real.exp (t + 2) := by
          rw [← Real.exp_add]; congr 1; ring
  have hZpos : 0 < Z := by
    have : (0 : ℝ) < Z := lt_of_lt_of_le (Real.exp_pos t) hexpt1
    exact_mod_cast this
  have hlogZ : Real.log Z ≤ t + 1 := by
    have h : Real.log (Z : ℝ) ≤ Real.log (Real.exp (t + 1)) :=
      Real.log_le_log (by exact_mod_cast hZpos) hexpt2
    rwa [Real.log_exp] at h
  have hlogZ_ge : t ≤ Real.log Z := by
    have h : Real.log (Real.exp t) ≤ Real.log (Z : ℝ) :=
      Real.log_le_log (Real.exp_pos t) hexpt1
    rwa [Real.log_exp] at h
  have hlog2Z : Real.log (2 * (Z : ℝ)) ≤ t + 2 := by
    have h2Zpos : (0 : ℝ) < 2 * (Z : ℝ) := by
      have hZpos' : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZpos
      linarith
    have h : Real.log (2 * (Z : ℝ)) ≤ Real.log (Real.exp (t + 2)) :=
      Real.log_le_log h2Zpos hZ2hi
    rwa [Real.log_exp] at h
  -- `u` bounds: `u = ⌊w⌋₊` with `w = (L-4)/(t+2) - 2 ≥ 0`
  have hw0 : (0 : ℝ) ≤ w := by
    have h2 : (2 : ℝ) ≤ (L - 4) / (t + 2) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < t + 2)]
      linarith [ht_hi, hL]
    rw [hwdef]; linarith
  have huw : (u : ℝ) ≤ w := Nat.floor_le hw0
  have huw1 : w < (u : ℝ) + 1 := Nat.lt_floor_add_one w
  -- `(u+2)(t+2) ≤ L - 4`
  have hu2t2 : ((u : ℝ) + 2) * (t + 2) ≤ L - 4 := by
    have hne : (t + 2 : ℝ) ≠ 0 := ne_of_gt (by linarith [ht_pos])
    have h1 : ((u : ℝ) + 2) * (t + 2) ≤ ((L - 4) / (t + 2)) * (t + 2) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith [ht_pos])
      rw [hwdef] at huw
      linarith [huw]
    rw [div_mul_cancel₀ _ hne] at h1
    exact h1
  -- the admissibility bound `(4Z)²·(2Z)^u ≤ x`
  have hxbound : (4 * Z) ^ 2 * (2 * Z) ^ u ≤ x := by
    have hre : ((4 * Z) ^ 2 * (2 * Z) ^ u : ℝ) ≤ (x : ℝ) := by
      have e16 : (16 : ℝ) ≤ Real.exp 6 := by
        have e6 : Real.exp 6 = Real.exp 1 ^ 6 := by
          have h := Real.exp_nat_mul (1 : ℝ) 6
          rw [Nat.cast_ofNat, mul_one] at h
          exact h
        have e2 : (2 : ℝ) ≤ Real.exp 1 :=
          (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans
            Real.exp_one_gt_d9.le
        calc (16 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
          _ ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) e2 _
          _ = Real.exp 6 := e6.symm
      have step1 : (4 * (Z : ℝ)) ^ 2 * (2 * (Z : ℝ)) ^ u
          ≤ 16 * Real.exp (2 * (t + 1)) * Real.exp ((u : ℝ) * (t + 2)) := by
        have pa : (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (t + 1) ^ 2 := by
          calc (4 * (Z : ℝ)) ^ 2 = 16 * (Z : ℝ) ^ 2 := by ring
            _ ≤ 16 * Real.exp (t + 1) ^ 2 :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (by positivity) hexpt2 _) (by norm_num)
        have pb : (2 * (Z : ℝ)) ^ u ≤ Real.exp ((u : ℝ) * (t + 2)) := by
          calc (2 * (Z : ℝ)) ^ u ≤ Real.exp (t + 2) ^ u :=
                pow_le_pow_left₀ (by positivity) hZ2hi _
            _ = Real.exp ((u : ℝ) * (t + 2)) := (Real.exp_nat_mul _ _).symm
        have pa' : (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (2 * (t + 1)) := by
          calc (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (t + 1) ^ 2 := pa
            _ = 16 * Real.exp (2 * (t + 1)) := by
                rw [show (2 : ℝ) * (t + 1) = ((2 : ℕ) : ℝ) * (t + 1) from
                    by push_cast; ring,
                  Real.exp_nat_mul]
        exact mul_le_mul pa' pb (by positivity) (by positivity)
      calc ((4 * Z) ^ 2 * (2 * Z) ^ u : ℝ)
          = (4 * (Z : ℝ)) ^ 2 * (2 * (Z : ℝ)) ^ u := by ring
        _ ≤ 16 * Real.exp (2 * (t + 1)) * Real.exp ((u : ℝ) * (t + 2)) := step1
        _ = 16 * Real.exp (2 * (t + 1) + (u : ℝ) * (t + 2)) := by
            rw [Real.exp_add]; ring
        _ ≤ 16 * Real.exp (L - 6) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
            apply Real.exp_le_exp.mpr
            have e : 2 * (t + 1) + (u : ℝ) * (t + 2)
                = ((u : ℝ) + 2) * (t + 2) - 2 := by ring
            linarith [e, hu2t2]
        _ ≤ Real.exp L := by
            calc 16 * Real.exp (L - 6)
                ≤ Real.exp 6 * Real.exp (L - 6) :=
                  mul_le_mul_of_nonneg_right e16 (Real.exp_nonneg _)
              _ = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
        _ = (x : ℝ) := Real.exp_log hxp
    exact_mod_cast hre
  -- dyadic bounds at this `x`
  have hcardP : Real.exp t / (4 * (t + 2)) ≤
      ((dyadicPrimes (2 * Z)).card : ℝ) := by
    have hZ2 : ((2 * Z : ℕ) : ℝ) = 2 * (Z : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have hlogpos : 0 < Real.log (2 * (Z : ℝ)) := by
      apply Real.log_pos
      have h1 : (1 : ℝ) < Real.exp t := Real.exp_zero ▸ Real.exp_lt_exp.mpr ht_pos
      linarith [hexpt1]
    have h2 : (2 * Real.exp t) / (8 * (t + 2)) ≤
        ((2 * Z : ℕ) : ℝ) / (8 * Real.log (2 * (Z : ℝ))) := by
      apply div_le_div₀ (by positivity : (0 : ℝ) ≤ ((2 * Z : ℕ) : ℝ))
      · rw [hZ2]; linarith [hexpt1]
      · exact mul_pos (by norm_num) hlogpos
      · linarith [hlog2Z]
    have heq : Real.exp t / (4 * (t + 2)) = (2 * Real.exp t) / (8 * (t + 2)) := by
      have hne : (t + 2 : ℝ) ≠ 0 := by linarith [ht_pos]
      field_simp [hne]; ring
    rw [heq]
    exact h2.trans hD2Z'
  have hcardQ : Real.exp t / (8 * (t + 1)) ≤
      ((dyadicPrimes Z).card : ℝ) := by
    have hlogpos : 0 < Real.log (Z : ℝ) := by
      apply Real.log_pos
      have h1 : (1 : ℝ) < Real.exp t := Real.exp_zero ▸ Real.exp_lt_exp.mpr ht_pos
      linarith [hexpt1]
    have h2 : Real.exp t / (8 * (t + 1)) ≤ (Z : ℝ) / (8 * Real.log Z) :=
      div_le_div₀ (Nat.cast_nonneg _) hexpt1 (mul_pos (by norm_num) hlogpos)
        (by linarith [hlogZ])
    exact h2.trans hDZ'
  -- `e^t ≥ L^4`
  have hexp_L4 : (L : ℝ) ^ 4 ≤ Real.exp t := by
    have h1 : Real.exp (4 * L2) = (L : ℝ) ^ 4 := by
      have e : Real.exp (((4 : ℕ) : ℝ) * L2) = (Real.exp L2) ^ 4 :=
        Real.exp_nat_mul L2 4
      rw [hL2def, Real.exp_log hLpos, Nat.cast_ofNat] at e
      exact e
    calc (L : ℝ) ^ 4 = Real.exp (4 * L2) := h1.symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht_lo
  -- `t + 1 ≤ L` and `t + 2 ≤ L`
  have ht1_L : t + 1 ≤ L := by linarith [ht_hi, hL]
  have ht2_L : t + 2 ≤ L := by linarith [ht_hi, hL]
  -- `2u ≤ #dyadicPrimes Z`
  have hcardQ_L : (L : ℝ) ^ 3 / 8 ≤ ((dyadicPrimes Z).card : ℝ) := by
    calc (L : ℝ) ^ 3 / 8 = (L : ℝ) ^ 4 / (8 * L) := by
          rw [div_eq_div_iff (by norm_num : (8 : ℝ) ≠ 0)
            (mul_ne_zero (by norm_num) hLpos.ne')]
          ring
      _ ≤ Real.exp t / (8 * (t + 1)) :=
          div_le_div₀ (Real.exp_nonneg _) hexp_L4
            (mul_pos (by norm_num) (by linarith [ht_pos])) (by linarith [ht1_L])
      _ ≤ ((dyadicPrimes Z).card : ℝ) := hcardQ
  -- `u ≤ L`, `u·t ≤ L`, `u ≤ L/t`
  have hu_le : (u : ℝ) ≤ (L - 4) / (t + 2) := by linarith [huw]
  have hut_L : (u : ℝ) * t ≤ L := by
    calc (u : ℝ) * t ≤ (L - 4) / (t + 2) * t :=
          mul_le_mul_of_nonneg_right hu_le ht_pos.le
      _ = (L - 4) * t / (t + 2) := by ring
      _ ≤ L := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < t + 2)]
          nlinarith [hLpos, ht_pos]
  have hu_Lt : (u : ℝ) ≤ L / t := by
    calc (u : ℝ) ≤ (L - 4) / (t + 2) := hu_le
      _ ≤ L / t := by
          rw [div_le_div_iff (by linarith : (0 : ℝ) < t + 2) ht_pos]
          nlinarith [hLpos, ht_pos]
  have hu_le_L : (u : ℝ) ≤ L := by
    have h : L / t ≤ L := by
      rw [div_le_iff₀ ht_pos]
      have h' : L * 1 ≤ L * t := mul_le_mul_of_nonneg_left htge1 hLpos.le
      linarith [h']
    exact hu_Lt.trans h
  have h2u : 2 * u ≤ (dyadicPrimes Z).card := by
    have hLsq : (1024 : ℝ) ≤ L ^ 2 :=
      calc (1024 : ℝ) = 32 ^ 2 := by norm_num
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) _
    have h3 : (1024 : ℝ) * L ≤ L ^ 3 := by
      have e : (L : ℝ) ^ 3 = L ^ 2 * L := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hLsq hLpos.le
    have h1 : (2 : ℝ) * u ≤ L ^ 3 / 8 := by linarith [hu_le_L, h3, hLpos]
    have h2 : (2 : ℝ) * u ≤ ((dyadicPrimes Z).card : ℝ) := h1.trans hcardQ_L
    exact_mod_cast h2
  -- key algebra: `L·L2/t = √2·A` and `L/t = √2·A/L2`
  have hkey : Real.sqrt 2 * A * (A * Real.sqrt 2 / 2) = A ^ 2 := by
    have h : Real.sqrt 2 * A * (A * Real.sqrt 2 / 2)
        = (Real.sqrt 2) ^ 2 * A ^ 2 / 2 := by ring
    rw [h, hsq2]; ring
  have hLt_eq : L * L2 / t = Real.sqrt 2 * A := by
    rw [div_eq_iff ht_pos.ne', htdef, hkey]
    exact hAsq.symm
  have hL_t : L / t = Real.sqrt 2 * A / L2 := by
    rw [div_eq_div_iff ht_pos.ne' hL2pos.ne', htdef, hkey]
    exact hAsq.symm
  have huL2 : (u : ℝ) * L2 ≤ Real.sqrt 2 * A := by
    calc (u : ℝ) * L2 ≤ (L / t) * L2 :=
          mul_le_mul_of_nonneg_right hu_Lt hL2pos.le
      _ = L * L2 / t := by ring
      _ = Real.sqrt 2 * A := hLt_eq
  have hu_s : (u : ℝ) ≤ Real.sqrt 2 * A / L2 := by rwa [hL_t] at hu_Lt
  have h4u : 4 * (u : ℝ) ≤ 4 * Real.sqrt 2 * A / L2 := by linarith [hu_s]
  -- numerator bound: `t + u·t ≥ L − √2·A − 2√2·A/L2 − 4`
  have hnum : L - Real.sqrt 2 * A - 2 * Real.sqrt 2 * A / L2 - 4
      ≤ t + (u : ℝ) * t := by
    have e : (L - 4) / (t + 2) * t = (L - 4) - 2 * (L - 4) / (t + 2) := by
      have hne : (t + 2 : ℝ) ≠ 0 := by linarith [ht_pos]
      field_simp
      ring
    have hwt : w * t = (L - 4) - 2 * (L - 4) / (t + 2) - 2 * t := by
      rw [hwdef, sub_mul, e]
    have hut : (w - 1) * t ≤ (u : ℝ) * t :=
      mul_le_mul_of_nonneg_right (by linarith [huw1]) ht_pos.le
    have hfrac : 2 * (L - 4) / (t + 2) ≤ 2 * Real.sqrt 2 * A / L2 := by
      calc 2 * (L - 4) / (t + 2) ≤ 2 * L / (t + 2) :=
            div_le_div₀ (by linarith) (by linarith) (by linarith) le_rfl
        _ ≤ 2 * L / t := div_le_div₀ (by linarith) le_rfl ht_pos (by linarith)
        _ = 2 * Real.sqrt 2 * A / L2 := by
            rw [mul_div_assoc, hL_t, mul_div_assoc]
    linarith [hwt, hut, hfrac, h2t]
  -- denominator bound: `(16(t+1))^u·u^u ≤ (32L)^u`
  have hupos_or : (0 : ℝ) < (u : ℝ) ^ u := by
    rcases Nat.eq_zero_or_pos u with hu0 | hupos
    · simp [hu0]
    · exact pow_pos (by exact_mod_cast hupos) _
  have hden_le : (16 * (t + 1)) ^ u * (u : ℝ) ^ u ≤ (32 * L) ^ u := by
    rw [← mul_pow]
    apply pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith [ht_pos]))
        (Nat.cast_nonneg _))
    have e : 16 * (t + 1) * (u : ℝ) = 16 * ((u : ℝ) * t) + 16 * (u : ℝ) := by
      ring
    rw [e]
    linarith [hut_L, hu_le_L]
  -- the choose bound: `e^{u·t}/(32L)^u ≤ cardQ.choose u`
  have hchoose : Real.exp ((u : ℝ) * t) / (32 * L) ^ u
      ≤ (((dyadicPrimes Z).card.choose u : ℕ) : ℝ) := by
    have h0 := SingletonLBz.choose_ge_quarter
      (D := (dyadicPrimes Z).card) (u := u) h2u
    have hQ2 : Real.exp t / (16 * (t + 1)) ≤ ((dyadicPrimes Z).card : ℝ) / 2 := by
      rw [show (16 : ℝ) * (t + 1) = (8 * (t + 1)) * 2 by ring, ← div_div]
      linarith [hcardQ]
    have hrew : (Real.exp t / (16 * (t + 1))) ^ u =
        Real.exp ((u : ℝ) * t) / (16 * (t + 1)) ^ u := by
      rw [div_pow, Real.exp_nat_mul]
    calc Real.exp ((u : ℝ) * t) / (32 * L) ^ u
        ≤ Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (u : ℝ) ^ u) :=
          div_le_div₀ (Real.exp_nonneg _) le_rfl
            (mul_pos (pow_pos (by linarith [ht_pos]) _) hupos_or) hden_le
      _ = (Real.exp t / (16 * (t + 1))) ^ u / (u : ℝ) ^ u := by
          rw [hrew, div_div]
      _ ≤ (((dyadicPrimes Z).card : ℝ) / 2) ^ u / (u : ℝ) ^ u := by
          apply div_le_div₀ (pow_nonneg (by positivity) _)
          · exact pow_le_pow_left₀
              (div_nonneg (Real.exp_nonneg _) (by linarith [ht_pos])) hQ2 u
          · exact hupos_or
          · exact le_rfl
      _ ≤ _ := h0
  -- product of the two bounds
  have hprod : Real.exp t / (4 * (t + 2)) *
      (Real.exp ((u : ℝ) * t) / (32 * L) ^ u)
      ≤ (badSingletonCount x : ℝ) := by
    calc Real.exp t / (4 * (t + 2)) *
          (Real.exp ((u : ℝ) * t) / (32 * L) ^ u)
        ≤ ((dyadicPrimes (2 * Z)).card : ℝ) *
          (((dyadicPrimes Z).card.choose u : ℕ) : ℝ) :=
          mul_le_mul hcardP hchoose
            (div_nonneg (Real.exp_nonneg _)
              (pow_nonneg (mul_nonneg (by norm_num) hLpos.le) _))
            (Nat.cast_nonneg _)
      _ ≤ (badSingletonCount x : ℝ) := by
          exact_mod_cast SingletonLBz.badSingletonCount_ge_card x Z u hxbound
  -- denominator bound: `L·(32L)^u ≤ e^{L2 + √2·A + 4√2·A/L2}`
  have eL : Real.exp L2 = L := by rw [hL2def]; exact Real.exp_log hLpos
  have e32 : Real.log (32 * L) = Real.log 32 + L2 := by
    rw [hL2def, Real.log_mul (by norm_num) hLpos.ne']
  have hlog32 : Real.log 32 ≤ 4 := by
    have e : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e]
    linarith [Real.log_two_lt_d9]
  have hpow32 : (32 * L) ^ u ≤ Real.exp ((u : ℝ) * (L2 + 4)) := by
    have e : Real.exp ((u : ℝ) * Real.log (32 * L)) = (32 * L) ^ u := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    rw [← e]
    apply Real.exp_le_exp.mpr
    rw [e32]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith [hlog32]
  have hden' : L * (32 * L) ^ u ≤
      Real.exp (L2 + Real.sqrt 2 * A + 4 * Real.sqrt 2 * A / L2) := by
    have h1 : L * (32 * L) ^ u ≤ Real.exp L2 * Real.exp ((u : ℝ) * (L2 + 4)) := by
      calc L * (32 * L) ^ u = Real.exp L2 * (32 * L) ^ u := by rw [eL]
        _ ≤ Real.exp L2 * Real.exp ((u : ℝ) * (L2 + 4)) :=
            mul_le_mul_of_nonneg_left hpow32 (Real.exp_nonneg _)
    rw [← Real.exp_add] at h1
    have h2 : L2 + (u : ℝ) * (L2 + 4) ≤
        L2 + Real.sqrt 2 * A + 4 * Real.sqrt 2 * A / L2 := by
      have e : (u : ℝ) * (L2 + 4) = (u : ℝ) * L2 + 4 * (u : ℝ) := by ring
      rw [e]; linarith [huL2, h4u]
    exact h1.trans (Real.exp_le_exp.mpr h2)
  have h4t2 : 4 * (t + 2) ≤ L := by linarith [ht_hi, hL]
  -- slack: `L2 + 6√2·A/L2 + 4 ≤ ε·A`
  have h1ε : L2 ≤ ε / 3 * A := hL2A'
  have h2ε : 6 * Real.sqrt 2 * A / L2 ≤ ε / 3 * A := by
    have h18 : 18 * Real.sqrt 2 ≤ ε * L2 := by
      rw [div_le_iff₀ hε] at hL2ge'
      linarith [hL2ge']
    rw [div_le_iff₀ hL2pos]
    have h6 : 6 * Real.sqrt 2 ≤ ε * L2 / 3 := by linarith [h18]
    have h := mul_le_mul_of_nonneg_right h6 hApos.le
    linarith [h]
  have h3ε : (4 : ℝ) ≤ ε / 3 * A := by
    rw [div_le_iff₀ hε] at hAge'
    linarith [hAge', hε]
  have hslack : L2 + 6 * Real.sqrt 2 * A / L2 + 4 ≤ ε * A := by
    linarith [h1ε, h2ε, h3ε]
  have hCA : C * A = ε * A + 2 * Real.sqrt 2 * A := by rw [hεdef]; ring
  have hfin : (L - C * A) + (L2 + Real.sqrt 2 * A + 4 * Real.sqrt 2 * A / L2)
      ≤ t + (u : ℝ) * t := by
    linarith [hnum, hslack, hCA]
  -- final assembly
  have hDpos : (0 : ℝ) < 4 * (t + 2) * (32 * L) ^ u :=
    mul_pos (mul_pos (by norm_num) (by linarith [ht_pos]))
      (pow_pos (mul_pos (by norm_num) hLpos) _)
  calc (x : ℝ) * Real.exp (-C * A)
      = Real.exp (L - C * A) := by
        have e : (x : ℝ) = Real.exp L := (Real.exp_log hxp).symm
        rw [e, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (t + (u : ℝ) * t) / (4 * (t + 2) * (32 * L) ^ u) := by
        rw [le_div_iff₀ hDpos]
        calc Real.exp (L - C * A) * (4 * (t + 2) * (32 * L) ^ u)
            ≤ Real.exp (L - C * A) * (L * (32 * L) ^ u) := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
              exact mul_le_mul_of_nonneg_right h4t2
                (pow_nonneg (mul_nonneg (by norm_num) hLpos.le) _)
          _ ≤ Real.exp (L - C * A) *
              Real.exp (L2 + Real.sqrt 2 * A + 4 * Real.sqrt 2 * A / L2) :=
              mul_le_mul_of_nonneg_left hden' (Real.exp_nonneg _)
          _ = Real.exp
              ((L - C * A) + (L2 + Real.sqrt 2 * A + 4 * Real.sqrt 2 * A / L2)) := by
              rw [← Real.exp_add]
          _ ≤ Real.exp (t + (u : ℝ) * t) := Real.exp_le_exp.mpr hfin
    _ = Real.exp t / (4 * (t + 2)) *
          (Real.exp ((u : ℝ) * t) / (32 * L) ^ u) := by
        rw [div_mul_div_comm, ← Real.exp_add]
    _ ≤ (badSingletonCount x : ℝ) := hprod

end SmoothLB4

end JSP314
