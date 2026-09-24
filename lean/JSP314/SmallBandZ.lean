/-
JSP314: z-scale small-band bound.

The `p`-cell of the run sum is bounded through the quotient map
`m ↦ m / p²`: a right (or left) run witness `m` has `p² ∣ m` and
`largestPrimeFactor m = p`, hence `r = m / p²` is `p`-smooth and
`r ≤ 2x / p²`.  Each cell therefore satisfies

  `T_p(k) ≤ 2 · Ψ(2x / p², p)`,

which is sharper than the `Ψ(2x+1, p)` bound used in `SmallBand.lean`
(the `p²` saving is essential at the `z^{1/2}` scale).

Combining with the Rankin estimate `SieveBase.smoothCount_rpow_le`,
a Mertens-style bound `∑_{q≤Z} log q/(q-1) ≤ 2 log Z + 11`
(`SylvesterSchur.sum_log_div_pred_primesLE_le`, from `QuadMertens.lean`),
and a two-split Rankin tail bound for `∑_{q≤Z} q^{-σ}` with
`σ = 1 - η`, `η = (3/4)·s/L`, we obtain

  `smallBandZ_le` :
    `∑_{p ≤ Z} ∑_{k ≤ 2p} (rightRunCount + leftRunCount)`
      `≤ x · exp (-(1/2)·√(log x · log log x))`   eventually,

with `Z = ⌈exp (½·√(log x · log log x))⌉₊`, i.e. `z^{1/2}`.
-/

import JSP314.BandSum
import JSP314.SieveBase
import JSP314.QuadMertens
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Finset Filter

namespace JSP314

/-! ### Basic objects -/

/-- Number of `n ∈ [1, N]` whose largest prime factor is `≤ p`. -/
noncomputable def lpfCount (N p : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => largestPrimeFactor n ≤ p).card

lemma lpfCount_def (N p : ℕ) :
    lpfCount N p =
      ((Finset.Icc 1 N).filter fun n => largestPrimeFactor n ≤ p).card := rfl

/-- The `z^{1/2}` cutoff for the small-prime band. -/
noncomputable def zCut (x : ℕ) : ℕ :=
  ⌈Real.exp (Real.sqrt (Real.log (x : ℝ) *
    Real.log (Real.log (x : ℝ))) / 2)⌉₊

/-! ### Section 1: per-cell combinatorial bound -/

/-- `largestPrimeFactor (m / p²) ≤ p` when `p² ∣ m` and
`largestPrimeFactor m = p`. -/
theorem lpf_div_sq_le {m p : ℕ} (hdvd : p ^ 2 ∣ m)
    (hp : p.Prime) (hlpf : largestPrimeFactor m = p) :
    largestPrimeFactor (m / p ^ 2) ≤ p := by
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · have : largestPrimeFactor m = 1 :=
        largestPrimeFactor_eq_one_iff.mpr (by omega)
      rw [this] at hlpf
      omega
    · exact h
  rcases Nat.lt_or_ge (m / p ^ 2) 2 with hlt | hge
  · have h1 : largestPrimeFactor (m / p ^ 2) = 1 :=
      largestPrimeFactor_eq_one_iff.mpr (by omega)
    rw [h1]; exact hp.one_le
  · have hd : m / p ^ 2 ∣ m := ⟨p ^ 2, Nat.div_mul_cancel hdvd⟩
    have hq := largestPrimeFactor_prime hge
    have hdq := largestPrimeFactor_dvd hge
    calc largestPrimeFactor (m / p ^ 2)
        ≤ largestPrimeFactor m :=
          prime_dvd_le_largestPrimeFactor hm2 hq (hdq.trans hd)
      _ = p := hlpf

/-- Each right-run cell is bounded by the `p`-smooth count at
`2x / p²`. -/
theorem rightRunCount_le_lpfCount {x p k : ℕ} (hp : p.Prime) :
    rightRunCount x p k ≤ lpfCount (2 * x / p ^ 2) p := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hdvd, hlpf, -⟩ := hm
    have hm1 : 1 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · have : largestPrimeFactor m = 1 :=
          largestPrimeFactor_eq_one_iff.mpr (by omega)
        rw [this] at hlpf; omega
      · exact (by omega : 1 ≤ m)
    have hge : p ^ 2 ≤ m := Nat.le_of_dvd hm1 hdvd
    have hr1 : 1 ≤ m / p ^ 2 := Nat.div_pos hge (Nat.pow_pos hp.pos 2)
    have hr2 : m / p ^ 2 ≤ 2 * x / p ^ 2 := Nat.div_le_div_right hm2x
    rw [lpfCount, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr1, hr2⟩, lpf_div_sq_le hdvd hp hlpf⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    have hda : p ^ 2 ∣ a := ha.2.1
    have hdb : p ^ 2 ∣ b := hb.2.1
    have hA : a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' hda).symm
    have hB : b = p ^ 2 * (b / p ^ 2) := (Nat.mul_div_cancel' hdb).symm
    rw [hA, hab, ← hB]

/-- Each left-run cell is bounded by the `p`-smooth count at
`2x / p²`. -/
theorem leftRunCount_le_lpfCount {x p k : ℕ} (hp : p.Prime) :
    leftRunCount x p k ≤ lpfCount (2 * x / p ^ 2) p := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hdvd, hlpf, -⟩ := hm
    have hm1 : 1 ≤ m := by
      rcases Nat.lt_or_ge m 2 with h | h
      · have : largestPrimeFactor m = 1 :=
          largestPrimeFactor_eq_one_iff.mpr (by omega)
        rw [this] at hlpf; omega
      · exact (by omega : 1 ≤ m)
    have hge : p ^ 2 ≤ m := Nat.le_of_dvd hm1 hdvd
    have hr1 : 1 ≤ m / p ^ 2 := Nat.div_pos hge (Nat.pow_pos hp.pos 2)
    have hr2 : m / p ^ 2 ≤ 2 * x / p ^ 2 := Nat.div_le_div_right hm2x
    rw [lpfCount, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr1, hr2⟩, lpf_div_sq_le hdvd hp hlpf⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    have hda : p ^ 2 ∣ a := ha.2.1
    have hdb : p ^ 2 ∣ b := hb.2.1
    have hA : a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' hda).symm
    have hB : b = p ^ 2 * (b / p ^ 2) := (Nat.mul_div_cancel' hdb).symm
    rw [hA, hab, ← hB]

/-- The full `p`-slice of the run sum is bounded by `4p · Ψ(2x/p², p)`. -/
theorem smallBandZ_sum_le (x Z : ℕ) :
    ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k)
      ≤ 4 * ∑ p ∈ Nat.primesLE Z, p * lpfCount (2 * x / p ^ 2) p := by
  calc ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ p ∈ Nat.primesLE Z, ∑ _k ∈ Finset.Icc 1 (2 * p),
          2 * lpfCount (2 * x / p ^ 2) p := by
        apply Finset.sum_le_sum; intro p hp
        apply Finset.sum_le_sum; intro k _
        have hR := rightRunCount_le_lpfCount (x := x) (p := p) (k := k)
          (Nat.prime_of_mem_primesLE hp)
        have hL := leftRunCount_le_lpfCount (x := x) (p := p) (k := k)
          (Nat.prime_of_mem_primesLE hp)
        omega
    _ = ∑ p ∈ Nat.primesLE Z, (2 * p) * (2 * lpfCount (2 * x / p ^ 2) p) := by
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc]
        congr 1; omega
    _ = 4 * ∑ p ∈ Nat.primesLE Z, p * lpfCount (2 * x / p ^ 2) p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring

/-! ### Section 2: Euler-product bound -/

/-- For `σ ≥ 1/2` and prime `q`, `q^{-σ} ≤ 3/4`. -/
theorem rpow_neg_le_three_quarters {q : ℕ} (hq : q.Prime) {σ : ℝ}
    (hσ : (1 : ℝ) / 2 ≤ σ) : (q : ℝ) ^ (-σ) ≤ 3 / 4 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hσ0 : 0 ≤ σ := by linarith
  have h1 : (q : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ q),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    apply inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
    exact Real.rpow_le_rpow (by norm_num) hq2 hσ0
  have h2 : (2 : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-(1/2 : ℝ)) = (√2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [← Real.sqrt_eq_rpow]
  have h4 : (√2)⁻¹ ≤ 3 / 4 := by
    rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    have : (4/3 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt (by norm_num : (0:ℝ) ≤ 4/3)]
      norm_num
    rw [one_mul]; linarith
  exact h1.trans (h2.trans (by rw [h3]; exact h4))

/-- For `0 ≤ t ≤ 3/4`, `-log(1 - t) ≤ 4t`. -/
theorem neg_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 3 / 4) :
    -Real.log (1 - t) ≤ 4 * t := by
  have h1t : 0 < 1 - t := by linarith
  have h1 : -Real.log (1 - t) = Real.log ((1 - t)⁻¹) := by
    rw [Real.log_inv]
  rw [h1]
  calc Real.log ((1 - t)⁻¹)
      ≤ (1 - t)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1t)
    _ = t / (1 - t) := by field_simp
    _ ≤ 4 * t := by
        rw [div_le_iff₀ h1t]
        nlinarith

/-- Euler-product bound: `∏_{q≤Z} (1-q^{-σ})⁻¹ ≤ exp (4·∑ q^{-σ})`
for `σ ∈ [1/2, 1)`. -/
theorem eulerProd_le_exp (Z : ℕ) {σ : ℝ} (hσ : (1 : ℝ) / 2 ≤ σ)
    (hσ1 : σ < 1) :
    ∏ q ∈ Nat.primesLE Z, (1 - (q : ℝ) ^ (-σ))⁻¹
      ≤ Real.exp (4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-σ)) := by
  have hfac : ∀ q ∈ Nat.primesLE Z,
      0 < 1 - (q : ℝ) ^ (-σ) := by
    intro q hq
    have hqq := Nat.prime_of_mem_primesLE hq
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hqq.one_lt
    have hlt : (q : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    linarith
  have hprod_pos : 0 < ∏ q ∈ Nat.primesLE Z, (1 - (q : ℝ) ^ (-σ))⁻¹ :=
    Finset.prod_pos fun q hq => inv_pos.mpr (hfac q hq)
  rw [← Real.exp_log hprod_pos, Real.exp_le_exp]
  rw [Real.log_prod _ _ (fun q hq => (hfac q hq).ne')]
  calc ∑ q ∈ Nat.primesLE Z, Real.log ((1 - (q : ℝ) ^ (-σ))⁻¹)
      = ∑ q ∈ Nat.primesLE Z, -Real.log (1 - (q : ℝ) ^ (-σ)) := by
        apply Finset.sum_congr rfl; intro q _
        rw [Real.log_inv]
    _ ≤ ∑ q ∈ Nat.primesLE Z, 4 * (q : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum; intro q hq
        exact neg_log_one_sub_le (Real.rpow_nonneg (by positivity) _)
          (rpow_neg_le_three_quarters (Nat.prime_of_mem_primesLE hq) hσ)
    _ = 4 * ∑ q ∈ Nat.primesLE Z, (q : ℝ) ^ (-σ) := by
        rw [Finset.mul_sum]

/-! ### Section 3: the two-split bound for `∑ q^{-σ}` -/

/-- `1/q ≤ log q / ((q-1)·log 2)` for `q ≥ 2`. -/
theorem inv_le_log_div_pred {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ)⁻¹ ≤ Real.log q / ((q - 1 : ℕ) : ℝ) / Real.log 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q :=
    Real.log_le_log (by norm_num) hq2
  -- (q-1)·log 2 ≤ q·log q
  have hkey : ((q - 1 : ℕ) : ℝ) * Real.log 2 ≤ q * Real.log q := by
    have h1 : ((q - 1 : ℕ) : ℝ) * Real.log 2 ≤ q * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hlog2.le
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]; linarith
    calc ((q - 1 : ℕ) : ℝ) * Real.log 2
        ≤ q * Real.log 2 := h1
      _ ≤ q * Real.log q :=
          mul_le_mul_of_nonneg_left hlogq (by positivity)
  rw [div_le_iff₀ (mul_pos (by linarith) hlog2)]
  -- goal: (q:ℝ)⁻¹ · ((q-1)·log 2) ≤ log q  →  via (q-1)log2 ≤ q·logq
  rw [mul_comm, ← div_le_iff₀ (by positivity : (0:ℝ) < q)]
  calc ((q - 1 : ℕ) : ℝ) * Real.log 2 / q
      ≤ q * Real.log q / q :=
        div_le_div_of_nonneg_right? -- placeholder
    _ = Real.log q := by field_simp
  sorry
