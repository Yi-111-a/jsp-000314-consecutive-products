import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# JSP-000314 — the Halász–Montgomery inequality (Tao's Lemma 5.3)

This file proves the Halász–Montgomery large-sieve-type inequality used in
Tao's proof of the Erdős–Graham consecutive-products conjecture
(arXiv:2603.27990, Lemma 5.3): for a complex inner product space `E`,
a vector `ξ : E` and a finite family `φ j : E` indexed by `j ∈ s`,

    ∑_{j ∈ s} |⟨ξ, φ j⟩|² ≤ ‖ξ‖² · max_{j ∈ s} ∑_{j' ∈ s} |⟨φ j, φ j'⟩|.

## Proof sketch

Write `w j := ⟨ξ, φ j⟩` and `S := ∑_j |w_j|²`, and set
`ζ := ∑_{j ∈ s} conj (w j) • φ j`.  Then `⟨ξ, ζ⟩ = ∑_j conj (w_j) w_j = S`,
so by Cauchy–Schwarz `S ≤ ‖ξ‖ · ‖ζ‖` and `S² ≤ ‖ξ‖² · ‖ζ‖²`.  Expanding,

    ‖ζ‖² = |∑_{j,j'} w_j conj(w_{j'}) ⟨φ j, φ j'⟩|
         ≤ ∑_{j,j'} |w_j| |w_{j'}| · |⟨φ j, φ j'⟩|
         ≤ ∑_{j,j'} (|w_j|² + |w_{j'}|²)/2 · |⟨φ j, φ j'⟩|
         = ∑_j |w_j|² · ∑_{j'} |⟨φ j, φ j'⟩|
         ≤ S · T,

where the second inequality is `2ab ≤ a² + b²` and the symmetry
`|⟨φ j, φ j'⟩| = |⟨φ j', φ j⟩|` (`norm_inner_symm`).  Hence
`S² ≤ ‖ξ‖² · S · T`, and cancelling `S` gives `S ≤ ‖ξ‖² · T`.

## Main statements

* `JSP314.halasz_montgomery_of_forall_le`: the inequality relative to an
  explicit bound `T` on the row sums `∑_{j' ∈ s} |⟨φ j, φ j'⟩|`.
* `JSP314.halasz_montgomery`: the inequality with the row-sum maximum
  `s.sup' hs (fun j ↦ ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖)`.

Mathlib's inner product is conjugate-linear in the first argument and linear
in the second (`inner_smul_left`, `inner_smul_right`), which dictates the
placement of `conj` in `ζ`.
-/

namespace JSP314

open ComplexConjugate
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Halász–Montgomery inequality** (bounded-row-sum form).

Let `E` be a complex inner product space, `s` a finite index set,
`φ : ι → E`, `ξ : E`, and `T` a nonnegative bound on every row sum
`∑_{j' ∈ s} |⟨φ j, φ j'⟩|`.  Then
`∑_{j ∈ s} |⟨ξ, φ j⟩|² ≤ ‖ξ‖² · T`. -/
theorem halasz_montgomery_of_forall_le {ι : Type*} (s : Finset ι) (ξ : E)
    (φ : ι → E) (T : ℝ)
    (hT : ∀ j ∈ s, ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ ≤ T) (hT0 : 0 ≤ T) :
    ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * T := by
  classical
  set S : ℝ := ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 with hS
  set ζ : E := ∑ j ∈ s, conj ⟪ξ, φ j⟫_ℂ • φ j with hζ
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Step 1 (duality): `⟪ξ, ζ⟫ = ∑_j conj(⟨ξ, φ j⟩) · ⟨ξ, φ j⟩ = S`.
  have h1 : ⟪ξ, ζ⟫_ℂ = (S : ℂ) := by
    rw [hζ, inner_sum, hS, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, Complex.conj_mul']
    norm_cast
  -- Step 2 (Cauchy–Schwarz): `S ≤ ‖ξ‖ · ‖ζ‖`.
  have hCS : S ≤ ‖ξ‖ * ‖ζ‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) ξ ζ
    rw [h1, Complex.norm_of_nonneg hSnn] at h
    exact h
  -- Step 3: square both sides.
  have hS2 : S ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 := by
    calc S ^ 2 ≤ (‖ξ‖ * ‖ζ‖) ^ 2 := pow_le_pow_left₀ hSnn hCS 2
      _ = ‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 := mul_pow _ _ _
  -- Step 4: expand `⟪ζ, ζ⟫` as a double sum.
  have hz : ⟪ζ, ζ⟫_ℂ =
      ∑ j ∈ s, ∑ j' ∈ s, ⟪ξ, φ j⟫_ℂ * conj ⟪ξ, φ j'⟫_ℂ * ⟪φ j, φ j'⟫_ℂ := by
    rw [hζ, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [inner_smul_left, inner_smul_right]
    simp only [starRingEnd_self_apply]
    ring
  -- Symmetrization: `∑∑ (aⱼ² + aⱼ'²)/2 · g_{jj'} = ∑_j aⱼ² · ∑_{j'} g_{jj'}`.
  have hexp :
      ∑ j ∈ s, ∑ j' ∈ s,
          (‖⟪ξ, φ j⟫_ℂ‖ ^ 2 + ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2) / 2 * ‖⟪φ j, φ j'⟫_ℂ‖
        = ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ := by
    have hA : ∑ j ∈ s, ∑ j' ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖
        = ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    have hB : ∑ j ∈ s, ∑ j' ∈ s, ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖
        = ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [norm_inner_symm (φ j') (φ j)]
    calc ∑ j ∈ s, ∑ j' ∈ s,
            (‖⟪ξ, φ j⟫_ℂ‖ ^ 2 + ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2) / 2 * ‖⟪φ j, φ j'⟫_ℂ‖
        = ∑ j ∈ s, ∑ j' ∈ s,
            (1 / 2) * (‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖
              + ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖) := by
          refine Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun j' _ => ?_
          ring
      _ = (1 / 2) * ∑ j ∈ s, ∑ j' ∈ s,
            (‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖
              + ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖) := by
          simp only [← Finset.mul_sum]
      _ = (1 / 2) * (∑ j ∈ s, ∑ j' ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖
              + ∑ j ∈ s, ∑ j' ∈ s, ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2 * ‖⟪φ j, φ j'⟫_ℂ‖) := by
          simp only [Finset.sum_add_distrib]
      _ = (1 / 2) * (∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖
              + ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖) := by
          rw [hA, hB]
      _ = ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ := by ring
  -- Step 5: `‖ζ‖² ≤ S · T`, using `‖ζ‖² = re ⟪ζ, ζ⟫ ≤ ‖⟪ζ, ζ⟫‖`.
  have hζsq : ‖ζ‖ ^ 2 ≤ S * T := by
    calc ‖ζ‖ ^ 2 = RCLike.re ⟪ζ, ζ⟫_ℂ := norm_sq_eq_re_inner _
      _ ≤ ‖⟪ζ, ζ⟫_ℂ‖ := RCLike.re_le_norm _
      _ = ‖∑ j ∈ s, ∑ j' ∈ s,
            ⟪ξ, φ j⟫_ℂ * conj ⟪ξ, φ j'⟫_ℂ * ⟪φ j, φ j'⟫_ℂ‖ := by
          rw [hz]
      _ ≤ ∑ j ∈ s, ∑ j' ∈ s,
            ‖⟪ξ, φ j⟫_ℂ * conj ⟪ξ, φ j'⟫_ℂ * ⟪φ j, φ j'⟫_ℂ‖ :=
          (norm_sum_le s _).trans (Finset.sum_le_sum fun j _ => norm_sum_le s _)
      _ = ∑ j ∈ s, ∑ j' ∈ s,
            ‖⟪ξ, φ j⟫_ℂ‖ * ‖⟪ξ, φ j'⟫_ℂ‖ * ‖⟪φ j, φ j'⟫_ℂ‖ := by
          refine Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun j' _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj]
      _ ≤ ∑ j ∈ s, ∑ j' ∈ s,
            (‖⟪ξ, φ j⟫_ℂ‖ ^ 2 + ‖⟪ξ, φ j'⟫_ℂ‖ ^ 2) / 2 * ‖⟪φ j, φ j'⟫_ℂ‖ := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ =>
            mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have h := two_mul_le_add_sq ‖⟪ξ, φ j⟫_ℂ‖ ‖⟪ξ, φ j'⟫_ℂ‖
          linarith
      _ = ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖ := hexp
      _ ≤ ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 * T :=
          Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hT j hj) (sq_nonneg _)
      _ = S * T := by rw [hS, Finset.sum_mul]
  -- Step 6: `S² ≤ ‖ξ‖² · S · T`, then cancel `S ≥ 0`.
  have hfin : S * S ≤ S * (‖ξ‖ ^ 2 * T) := by
    calc S * S = S ^ 2 := by ring
      _ ≤ ‖ξ‖ ^ 2 * ‖ζ‖ ^ 2 := hS2
      _ ≤ ‖ξ‖ ^ 2 * (S * T) := mul_le_mul_of_nonneg_left hζsq (sq_nonneg _)
      _ = S * (‖ξ‖ ^ 2 * T) := by ring
  rcases eq_or_lt_of_le hSnn with hS0 | hSpos
  · rw [← hS0]
    exact mul_nonneg (sq_nonneg _) hT0
  · exact le_of_mul_le_mul_left hfin hSpos

/-- **Halász–Montgomery inequality** (Tao, arXiv:2603.27990, Lemma 5.3).

For `s` a nonempty finite index set, `ξ : E`, and `φ : ι → E` in a complex
inner product space,

    ∑_{j ∈ s} |⟨ξ, φ j⟩|²
      ≤ ‖ξ‖² · max_{j ∈ s} ∑_{j' ∈ s} |⟨φ j, φ j'⟩|,

where the maximum is `Finset.sup'` over the nonempty finset `s`. -/
theorem halasz_montgomery {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (ξ : E)
    (φ : ι → E) :
    ∑ j ∈ s, ‖⟪ξ, φ j⟫_ℂ‖ ^ 2 ≤
      ‖ξ‖ ^ 2 * s.sup' hs (fun j => ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖) := by
  classical
  apply halasz_montgomery_of_forall_le
  · intro j hj
    exact Finset.le_sup' (f := fun j => ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖) hj
  · obtain ⟨j0, hj0⟩ := hs
    exact (Finset.sum_nonneg fun j' _ => norm_nonneg _).trans
      (Finset.le_sup' (f := fun j => ∑ j' ∈ s, ‖⟪φ j, φ j'⟫_ℂ‖) hj0)

end JSP314
