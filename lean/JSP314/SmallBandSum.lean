import JSP314.SmallBandZ
import JSP314.AntiSieveCore
import JSP314.QuadMertens
import Mathlib.Tactic

/-!
# JSP-000314 — the small-prime band of `runCountSum` at the `z^{1/2}` scale

This file completes the programme started in `JSP314.SmallBandZ`: a bound on
the small-prime band

  `∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
      (rightRunCount x p k + leftRunCount x p k)`

at the `z^{1/2}`-scale cutoff `Z = zCut x = ⌈exp(√(log x · log log x) / 2)⌉₊`,
of the form `≤ x · exp(-(1/16)·√(L·L₂))` eventually
(`smallBandSum_le_exp_neg_sqrt_ll`).

## Contents

* `rightRunCount_le_smoothCount`, `leftRunCount_le_smoothCount` — the crude
  per-cell bound `T_k ≤ Ψ(2x+1, p)` (each run witness is itself a `p`-smooth
  `m ≤ 2x`).  For the sharper `p²`-saving version used below, see
  `SmallBandZ.rightRunCount_le_lpfCount` (`T_k ≤ Ψ(2x/p², p)`).
* `smallBandSum_le_smoothCount` — `band(Z) ≤ 4·Z·(Z+1)·Ψ(2x+1, Z)` (the naive
  `π(Z)·2Z·Ψ` bound; superseded by the Rankin bound below).
* `smallBandSum_le_runCountSum` — the band at cutoff `Z ≤ √(2x)` is a sub-sum
  of `runCountSum x`.
* `sum_primesLE_rpow_neg_add_le`, `sum_primesLE_gt_rpow_neg_add_le`,
  `sum_primesLE_rpow_neg_add_two_split` — the **two-split bound**
  `∑_{q ≤ Z} q^{-1+η} ≤ T^η·(2 log T + 11)/log 2
                       + Z^η·(2 log Z + 11)/log T`.
  The point: on the top level `T < q ≤ Z` the reciprocal `1/q` is
  `≤ log q/((q-1)·log T)` (`inv_le_log_div_pred_of_le`), so the Mertens bound
  `∑_{p ≤ k} log p/(p-1) ≤ 2 log k + 11`
  (`QuadMertens.sum_log_div_pred_primesLE_le`) buys a `1/log T` discount —
  exactly what is needed to make the Rankin Euler factor `exp(4·Σ q^{-σ})`
  subleading at `σ = 1 - η`, `η = s/(4L)`.
* `smallBandSum_le_euler` — Rankin per prime `p`, keeping the `p^{-2σ}`
  quotient saving:
  `band(Z) ≤ 4·(2x)^{1-η}·exp(4·Σ_{q≤Z} q^{η-1})·Σ_{p≤Z} p^{2η-1}`.
* `smallBandSum_le_two_split` — the same with both prime sums bounded by the
  two-split at level `T`.
* `tCut` — the intermediate cutoff `⌈exp(L^{1/4})⌉₊`.
* `zCut_le_sqrt_eventually`, `smallBandSum_le_runCountSum_eventually` —
  `zCut x ≤ √(2x)` eventually, so the band is a sub-sum of `runCountSum`.
* `smallBandSum_le_exp_neg_sqrt_ll` — **headline**: at `Z = zCut x` the band
  is eventually `≤ x·exp(-(1/16)·√(log x·log log x))`.

## Method (why `Z = z^{1/2}` works)

With `log Z ≈ s/2`, `s = √(L·L₂)`, `η = s/(4L)`:

* `(2x)^{1-η} ≤ 2x·e^{-s/4}` — the Rankin saving;
* `η·log Z ≤ L₂/8 + o(1)`, so `Z^η ≤ 2·L^{1/8}` and `Z^{2η} ≤ 2·L^{1/4}`;
* `η·log T → 0` for `T = ⌈e^{L^{1/4}}⌉`, so `T^η ≤ e`, `T^{2η} ≤ e²`;
* the two-split gives
  `Σ_{q≤Z} q^{η-1} ≤ 3·(5 L^{1/4})/log 2 + 2L^{1/8}·(3s)/L^{1/4}
    = O(L^{1/4} + s·L^{-1/8}) = o(s)`,
  so `exp(4·Σ q^{η-1}) ≤ e^{s/16}` eventually, and similarly
  `Σ_{p≤Z} p^{2η-1} ≤ s² ≤ e^{s/16}`;
* totalling `band ≤ 8·x·e^{-s/8} ≤ x·e^{-s/16}`.

The `p^{-2}` saving from `SmallBandZ.rightRunCount_le_lpfCount` (the quotient
map `m ↦ m/p²`) is essential: the crude `4p·Ψ(2x+1, Z)` bound loses `Z² ≈ e^s`,
which exactly cancels `Ψ(2x, Z) ≈ x·e^{-s}`.
-/

namespace JSP314

open Finset Filter

/-! ### Subgoal 1: crude per-cell `smoothCount` bounds -/

/-- Each right-run witness `m` is itself `p`-smooth and lies in `[1, 2x]`, so
`rightRunCount x p k ≤ Ψ(2x + 1, p) = smoothCount (2*x+1) p` for every `k`
(primality of `p` only ensures `m ≥ 1`).  Strictly weaker than
`SmallBandZ.rightRunCount_le_lpfCount`, which gives `Ψ(2x/p², p)`. -/
theorem rightRunCount_le_smoothCount {x p k : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p k ≤ smoothCount (2 * x + 1) p :=
  (rightRunCount_le_lpfCount hp).trans
    (smoothCount_mono ((Nat.div_le_self _ _).trans (Nat.le_succ _)))

/-- The left analogue of `rightRunCount_le_smoothCount`. -/
theorem leftRunCount_le_smoothCount {x p k : ℕ} (hp : Nat.Prime p) :
    leftRunCount x p k ≤ smoothCount (2 * x + 1) p :=
  (leftRunCount_le_lpfCount hp).trans
    (smoothCount_mono ((Nat.div_le_self _ _).trans (Nat.le_succ _)))

/-! ### Subgoal 2: the `4p·Ψ`-type band bound -/

/-- **Small-band bound, `smoothCount` form** (subgoal 2):
`band(Z) ≤ (Z+1)·4Z·Ψ(2x+1, Z)`. -/
theorem smallBandSum_le_smoothCount (x Z : ℕ) :
    ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) ≤
      (Z + 1) * (4 * Z) * smoothCount (2 * x + 1) Z := by
  calc ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ p ∈ Nat.primesLE Z, ∑ _k ∈ Finset.Icc 1 (2 * p),
          2 * smoothCount (2 * x + 1) Z := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro k _
        have hpp := Nat.prime_of_mem_primesLE hp
        have hpZ : p ≤ Z := Nat.le_of_mem_primesLE hp
        calc rightRunCount x p k + leftRunCount x p k
            ≤ smoothCount (2 * x + 1) p + smoothCount (2 * x + 1) p :=
              Nat.add_le_add (rightRunCount_le_smoothCount hpp)
                (leftRunCount_le_smoothCount hpp)
          _ = 2 * smoothCount (2 * x + 1) p := by ring
          _ ≤ 2 * smoothCount (2 * x + 1) Z :=
              Nat.mul_le_mul (le_refl 2) (smoothCount_mono_y hpZ)
    _ ≤ ∑ _p ∈ Nat.primesLE Z, 4 * Z * smoothCount (2 * x + 1) Z := by
        apply Finset.sum_le_sum
        intro p hp
        have hpZ : p ≤ Z := Nat.le_of_mem_primesLE hp
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        calc (2 * p) * (2 * smoothCount (2 * x + 1) Z)
            = (4 * p) * smoothCount (2 * x + 1) Z := by ring
          _ ≤ (4 * Z) * smoothCount (2 * x + 1) Z :=
              Nat.mul_le_mul (by omega) (le_refl _)
    _ = (Nat.primesLE Z).card * (4 * Z * smoothCount (2 * x + 1) Z) := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ (Z + 1) * (4 * Z * smoothCount (2 * x + 1) Z) :=
        Nat.mul_le_mul (card_primesLE_le Z) (le_refl _)
    _ = (Z + 1) * (4 * Z) * smoothCount (2 * x + 1) Z := by ring

/-- The `Z`-band of `runCountSum` is a sub-sum whenever `Z ≤ √(2x)`. -/
theorem smallBandSum_le_runCountSum (x Z : ℕ) (hZ : Z ≤ Nat.sqrt (2 * x)) :
    ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) ≤ runCountSum x := by
  unfold runCountSum
  apply Finset.sum_le_sum_of_subset
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans hZ, hp.2⟩

/-! ### Subgoal 3a: the two-split bound on `∑ q^{-1+η}` -/

/-- For `2 ≤ T ≤ q`, `1/q ≤ log q / ((q-1)·log T)` — a `log T`-discounted
reciprocal bound (the `T = 2` case is `SmallBandZ.inv_le_log_div_pred`). -/
theorem inv_le_log_div_pred_of_le {q T : ℕ} (hq : 2 ≤ q) (hT : 2 ≤ T)
    (hTq : T ≤ q) :
    (q : ℝ)⁻¹ ≤ Real.log q / ((q - 1 : ℕ) : ℝ) / Real.log T := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
  have hlogq : Real.log T ≤ Real.log q :=
    Real.log_le_log (by positivity : (0 : ℝ) < T) (by exact_mod_cast hTq)
  have hkey : ((q - 1 : ℕ) : ℝ) * Real.log T ≤ q * Real.log q := by
    calc ((q - 1 : ℕ) : ℝ) * Real.log T
        ≤ q * Real.log T := mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.sub_le q 1) hlogT.le
      _ ≤ q * Real.log q :=
          mul_le_mul_of_nonneg_left hlogq (by positivity)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rw [div_div, le_div_iff₀ (mul_pos (by linarith) hlogT)]
  calc (q : ℝ)⁻¹ * (((q - 1 : ℕ) : ℝ) * Real.log T)
      ≤ (q : ℝ)⁻¹ * (q * Real.log q) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Real.log q := inv_mul_cancel_left₀ hq0 _

/-- **Bottom level of the two-split**:
`∑_{q ≤ T} q^{-1+η} ≤ T^η·(2 log T + 11)/log 2`. -/
theorem sum_primesLE_rpow_neg_add_le (T : ℕ) {η : ℝ} (hη : 0 ≤ η) (hT : 1 ≤ T) :
    ∑ q ∈ Nat.primesLE T, (q : ℝ) ^ (-1 + η) ≤
      (T : ℝ) ^ η * (2 * Real.log T + 11) / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  calc ∑ q ∈ Nat.primesLE T, (q : ℝ) ^ (-1 + η)
      = ∑ q ∈ Nat.primesLE T, (q : ℝ)⁻¹ * (q : ℝ) ^ η := by
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq0 : (0 : ℝ) < q := by
          exact_mod_cast (Nat.prime_of_mem_primesLE hq).pos
        rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
    _ ≤ ∑ q ∈ Nat.primesLE T,
          (Real.log q / ((q - 1 : ℕ) : ℝ) / Real.log 2) * (T : ℝ) ^ η := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hqq := Nat.prime_of_mem_primesLE hq
        have hqT : (q : ℝ) ≤ T := by exact_mod_cast Nat.le_of_mem_primesLE hq
        exact mul_le_mul (inv_le_log_div_pred hqq.two_le)
          (Real.rpow_le_rpow (Nat.cast_nonneg q) hqT hη)
          (Real.rpow_nonneg (Nat.cast_nonneg q) _)
          (div_nonneg (div_nonneg
            (Real.log_nonneg (by exact_mod_cast hqq.one_lt.le))
            (Nat.cast_nonneg _)) hlog2.le)
    _ = (T : ℝ) ^ η *
          (∑ q ∈ Nat.primesLE T, Real.log q / ((q - 1 : ℕ) : ℝ)) /
            Real.log 2 := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ ≤ (T : ℝ) ^ η * (2 * Real.log T + 11) / Real.log 2 := by
        refine (div_le_div_iff_of_pos_right hlog2).mpr
          (mul_le_mul_of_nonneg_left
            (SylvesterSchur.sum_log_div_pred_primesLE_le hT)
            (Real.rpow_nonneg (Nat.cast_nonneg T) _))

/-- **Top level of the two-split**: on `T < q ≤ Z` the factor `1/log T` is
gained relative to the Mertens bound. -/
theorem sum_primesLE_gt_rpow_neg_add_le (Z T : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hT : 2 ≤ T) (hZ : 1 ≤ Z) :
    ∑ q ∈ (Nat.primesLE Z).filter (fun q => ¬ q ≤ T), (q : ℝ) ^ (-1 + η) ≤
      (Z : ℝ) ^ η * (2 * Real.log Z + 11) / Real.log T := by
  have hlogT : (0 : ℝ) < Real.log T := Real.log_pos (by exact_mod_cast hT)
  calc ∑ q ∈ (Nat.primesLE Z).filter (fun q => ¬ q ≤ T), (q : ℝ) ^ (-1 + η)
      = ∑ q ∈ (Nat.primesLE Z).filter (fun q => ¬ q ≤ T),
          (q : ℝ)⁻¹ * (q : ℝ) ^ η := by
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq0 : (0 : ℝ) < q := by
          exact_mod_cast
            (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1).pos
        rw [← Real.rpow_neg_one, ← Real.rpow_add hq0]
    _ ≤ ∑ q ∈ (Nat.primesLE Z).filter (fun q => ¬ q ≤ T),
          (Real.log q / ((q - 1 : ℕ) : ℝ) / Real.log T) * (Z : ℝ) ^ η := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨hqZ, hqT⟩ := Finset.mem_filter.mp hq
        have hqq := Nat.prime_of_mem_primesLE hqZ
        have hTq : T ≤ q := (not_le.mp hqT).le
        have hqZR : (q : ℝ) ≤ Z := by
          exact_mod_cast Nat.le_of_mem_primesLE hqZ
        exact mul_le_mul (inv_le_log_div_pred_of_le hqq.two_le hT hTq)
          (Real.rpow_le_rpow (Nat.cast_nonneg q) hqZR hη)
          (Real.rpow_nonneg (Nat.cast_nonneg q) _)
          (div_nonneg (div_nonneg
            (Real.log_nonneg (by exact_mod_cast hqq.one_lt.le))
            (Nat.cast_nonneg _)) hlogT.le)
    _ = (Z : ℝ) ^ η *
          (∑ q ∈ (Nat.primesLE Z).filter (fun q => ¬ q ≤ T),
            Real.log q / ((q - 1 : ℕ) : ℝ)) / Real.log T := by
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ ≤ (Z : ℝ) ^ η * (2 * Real.log Z + 11) / Real.log T := by
        refine (div_le_div_iff_of_pos_right hlogT).mpr
          (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Nat.cast_nonneg Z) _))
        refine (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun q hq _ => ?_).trans
          (SylvesterSchur.sum_log_div_pred_primesLE_le hZ)
        have hqq := Nat.prime_of_mem_primesLE hq
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hqq.one_lt.le))
          (Nat.cast_nonneg _)

/-- **Two-split bound**: `∑_{q ≤ Z} q^{-1+η} ≤
T^η·(2 log T + 11)/log 2 + Z^η·(2 log Z + 11)/log T`. -/
theorem sum_primesLE_rpow_neg_add_two_split (Z T : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hT : 2 ≤ T) (hTZ : T ≤ Z) :
    ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η) ≤
      (T : ℝ) ^ η * (2 * Real.log T + 11) / Real.log 2 +
        (Z : ℝ) ^ η * (2 * Real.log Z + 11) / Real.log T := by
  have hZ : 1 ≤ Z := by omega
  have hsplit : (Nat.primesLE Z).filter (fun q => q ≤ T) = Nat.primesLE T := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hqZ, hqp⟩, hqT⟩; exact ⟨hqT, hqp⟩
    · rintro ⟨hqT, hqp⟩; exact ⟨⟨hqT.trans hTZ, hqp⟩, hqT⟩
  have h := Finset.sum_filter_add_sum_filter_not (s := Nat.primesLE Z)
    (p := fun q => q ≤ T) (f := fun q => (q : ℝ) ^ (-1 + η))
  rw [hsplit] at h
  rw [← h]
  exact add_le_add (sum_primesLE_rpow_neg_add_le T hη (by omega))
    (sum_primesLE_gt_rpow_neg_add_le Z T hη hT hZ)

/-! ### Subgoal 3b: Rankin bound on the band, Euler-product form -/

/-- **Rankin bound on the small band.**  For `η ∈ (0, 1/2]` (writing
`σ = 1 - η`):

`band(Z) ≤ 4·(2x)^{1-η}·exp(4·Σ_{q≤Z} q^{η-1})·Σ_{p≤Z} p^{2η-1}`.

Each `p`-slice contributes `4p·Ψ(2x/p², p)`
(`SmallBandZ.smallBandZ_sum_le`), Rankin gives
`Ψ(2x/p², p) ≤ (2x/p²)^{1-η}·∏_{q≤p}(1-q^{η-1})⁻¹`, the Euler product is
`≤ exp(4·Σ_{q≤p} q^{η-1}) ≤ exp(4·Σ_{q≤Z} q^{η-1})`
(`SmallBandZ.eulerProd_le_exp`), and
`p·(2x/p²)^{1-η} ≤ (2x)^{1-η}·p^{2η-1}`. -/
theorem smallBandSum_le_euler (x Z : ℕ) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2) :
    ((∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) ≤
      4 * (2 * x : ℝ) ^ (1 - η) *
        Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
          ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-1 + 2 * η) := by
  have hσ : (1 : ℝ) / 2 ≤ 1 - η := by linarith
  have hσ1 : 1 - η < 1 := by linarith
  have hσ0 : (0 : ℝ) < 1 - η := by linarith
  have hper : ∀ p ∈ Nat.primesLE Z,
      (p : ℝ) * (lpfCount (2 * x / p ^ 2) p : ℝ) ≤
        (2 * x : ℝ) ^ (1 - η) *
          Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
            (p : ℝ) ^ (-1 + 2 * η) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    have hpZ : p ≤ Z := Nat.le_of_mem_primesLE hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hR : (lpfCount (2 * x / p ^ 2) p : ℝ) ≤
        ((2 * x / p ^ 2 : ℕ) : ℝ) ^ (1 - η) *
          ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-(1 - η)))⁻¹ :=
      SieveBase.smoothCount_rpow_le _ _ hσ0
    have hE := eulerProd_le_exp p hσ hσ1
    have hsub : Nat.primesLE p ⊆ Nat.primesLE Z := by
      intro q hq
      rw [Nat.mem_primesLE] at hq ⊢
      exact ⟨hq.1.trans hpZ, hq.2⟩
    have hSle : (∑ q ∈ Nat.primesLE p, (q : ℝ) ^ (-(1 - η))) ≤
        ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η) := by
      have hcongr : (∑ q ∈ Nat.primesLE p, (q : ℝ) ^ (-(1 - η))) =
          ∑ q ∈ Nat.primesLE p, (q : ℝ) ^ (-1 + η) :=
        Finset.sum_congr rfl fun q _ => by congr 1; ring
      rw [hcongr]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
        Real.rpow_nonneg (Nat.cast_nonneg q) _
    have hE' : (∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-(1 - η)))⁻¹) ≤
        Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) :=
      hE.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hSle (by norm_num)))
    have hNR : ((2 * x / p ^ 2 : ℕ) : ℝ) ^ (1 - η) ≤
        (2 * x : ℝ) ^ (1 - η) * ((p : ℝ) ^ 2) ^ (-(1 - η)) := by
      have hcast : ((2 * x / p ^ 2 : ℕ) : ℝ) ≤
          (2 * x : ℝ) / (p : ℝ) ^ 2 := by
        refine Nat.cast_div_le.trans (le_of_eq ?_)
        norm_cast
      have h1 : ((2 * x / p ^ 2 : ℕ) : ℝ) ^ (1 - η) ≤
          ((2 * x : ℝ) / (p : ℝ) ^ 2) ^ (1 - η) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by linarith)
      rwa [Real.div_rpow (show (0 : ℝ) ≤ 2 * (x : ℝ) by positivity)
          (pow_nonneg (Nat.cast_nonneg _) _) _,
        div_eq_mul_inv,
        ← Real.rpow_neg (pow_nonneg (Nat.cast_nonneg _) _)] at h1
    have hpm : (p : ℝ) * ((p : ℝ) ^ 2) ^ (-(1 - η)) =
        (p : ℝ) ^ (-1 + 2 * η) := by
      have hpsq : ((p : ℝ) ^ 2) ^ (-(1 - η)) = (p : ℝ) ^ (-2 + 2 * η) := by
        rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_mul hp0.le]
        congr 1; ring
      rw [hpsq, mul_comm (p : ℝ) ((p : ℝ) ^ (-2 + 2 * η)),
        ← Real.rpow_add_one hp0.ne']
      congr 1; ring
    calc (p : ℝ) * (lpfCount (2 * x / p ^ 2) p : ℝ)
        ≤ (p : ℝ) * (((2 * x / p ^ 2 : ℕ) : ℝ) ^ (1 - η) *
            Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η))) :=
          mul_le_mul_of_nonneg_left
            (hR.trans (mul_le_mul_of_nonneg_left hE'
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
            hp0.le
      _ ≤ (p : ℝ) * (((2 * x : ℝ) ^ (1 - η) * ((p : ℝ) ^ 2) ^ (-(1 - η))) *
            Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hNR (Real.exp_pos _).le) hp0.le
      _ = ((p : ℝ) * ((p : ℝ) ^ 2) ^ (-(1 - η))) *
            ((2 * x : ℝ) ^ (1 - η) *
              Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η))) := by
          ring
      _ = (2 * x : ℝ) ^ (1 - η) *
            Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
              (p : ℝ) ^ (-1 + 2 * η) := by
          rw [hpm]; ring
  have hsum : ∑ p ∈ Nat.primesLE Z,
        (p : ℝ) * (lpfCount (2 * x / p ^ 2) p : ℝ) ≤
      (2 * x : ℝ) ^ (1 - η) *
        Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
          ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-1 + 2 * η) := by
    calc ∑ p ∈ Nat.primesLE Z, (p : ℝ) * (lpfCount (2 * x / p ^ 2) p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE Z, (2 * x : ℝ) ^ (1 - η) *
            Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
              (p : ℝ) ^ (-1 + 2 * η) :=
          Finset.sum_le_sum fun p hp => hper p hp
      _ = (2 * x : ℝ) ^ (1 - η) *
            Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
              ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-1 + 2 * η) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  calc ((∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
      ≤ ((4 * ∑ p ∈ Nat.primesLE Z,
          p * lpfCount (2 * x / p ^ 2) p : ℕ) : ℝ) := by
        exact_mod_cast smallBandZ_sum_le x Z
    _ = 4 * ∑ p ∈ Nat.primesLE Z,
          (p : ℝ) * (lpfCount (2 * x / p ^ 2) p : ℝ) := by
        norm_cast
    _ ≤ 4 * ((2 * x : ℝ) ^ (1 - η) *
          Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
            ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-1 + 2 * η)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 4 * (2 * x : ℝ) ^ (1 - η) *
          Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-1 + η)) *
            ∑ p ∈ Nat.primesLE Z, (p : ℝ) ^ (-1 + 2 * η) := by ring
