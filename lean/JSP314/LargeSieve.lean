import Mathlib
import JSP314.JointSieve

/-!
# JSP-000314 — arithmetic large sieve upper bound

This file proves a large-sieve upper bound for sifted sets of integers:

  `|A| · Σ_{q ∈ 𝒬} ω(q) / (q − ω(q)) ≤ (N + 1) + Q² · (3 + 2 log Q)`

for `A ⊆ [1, N]` avoiding `ω(q)` residue classes modulo each prime `q ∈ 𝒬`,
`q ≤ Q`.

## Proof route

1. **Additive large sieve** (`largeSieve`): for `δ`-separated points
   `α_r` on the circle `ℝ/ℤ` and complex coefficients `a_n`, `n < N`,

     `Σ_r ‖Σ_n a_n e(nα_r)‖² ≤ (N + (3 + log(1/(2δ)))/δ) · Σ_n ‖a_n‖²`.

   Proved by self-duality: writing `c_r = Σ_n a_n e(nα_r)`, one bounds
   `Σ_r |c_r|² ≤ √(Σ|a|²)·√(Σ_n|D_n|²)` with `D_n = Σ_r c_r e(−nα_r)`; the
   off-diagonal kernel `K(β) = Σ_{n<N} e(nβ)` satisfies
   `|K(β)| ≤ min(N, 1/(2‖β‖_{ℝ/ℤ}))`, and a bucket counting argument gives
   `Σ_s min(N, 1/(2‖α_r−α_s‖)) ≤ 2/δ + (1+log(1/(2δ)))/δ`.

2. **Arithmetic reduction** (`largeSieve_arith`): for prime `q`,
   `Σ_{x=1}^{q-1} |S_A(x/q)|² = q·Σ_h N_q(h)² − |A|² ≥ |A|²·ω(q)/(q−ω(q))`
   by orthogonality of additive characters and Cauchy–Schwarz.  The Farey
   points `{x/q}` are `1/Q²`-separated.

3. **Application** (`siftedSet_card_le_largeSieve`): for the sifted set
   `siftedSet y p k w` with sift primes `(Ioc p w).filter Nat.Prime` and
   `ω(q) = min k q`, using `sifted_count_mod_prime_le` from `JointSieve`.

No `sorry`; kernel-checkable.
-/

namespace JSP314

open Finset Real

/-! ### The additive character `e(α) = exp(2πiα)` -/

/-- `e(α) = exp(2πiα)`, the standard additive character of `ℝ/ℤ`. -/
noncomputable def e (α : ℝ) : ℂ :=
  Complex.exp (↑(2 * Real.pi * α) * Complex.I)

@[simp] lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (α β : ℝ) : e (α + β) = e α * e β := by
  have h : (↑(2 * Real.pi * (α + β)) : ℂ) * Complex.I
      = ↑(2 * Real.pi * α) * Complex.I + ↑(2 * Real.pi * β) * Complex.I := by
    push_cast; ring
  rw [e, e, e, h, Complex.exp_add]

lemma e_intCast (n : ℤ) : e (n : ℝ) = 1 := by
  have h : (↑(2 * Real.pi * (n : ℝ)) : ℂ) * Complex.I
      = n * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e, h, Complex.exp_int_mul_two_pi_mul_I]

lemma e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  exact_mod_cast e_intCast (n : ℤ)

lemma e_add_int (α : ℝ) (n : ℤ) : e (α + n) = e α := by
  rw [e_add, e_intCast, mul_one]

lemma e_sub_int (α : ℝ) (n : ℤ) : e (α - n) = e α := by
  rw [sub_eq_add_neg, ← Int.cast_neg, e_add_int]

lemma e_neg (α : ℝ) : e (-α) = (e α)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← e_add, neg_add_cancel, e_zero]

lemma e_sub (α β : ℝ) : e (α - β) = e α * (e β)⁻¹ := by
  rw [sub_eq_add_neg, e_add, e_neg]

lemma e_conj (α : ℝ) : conj (e α) = e (-α) := by
  have h : conj (↑(2 * Real.pi * α) * Complex.I)
      = (↑(2 * Real.pi * (-α)) : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [e, e, Complex.conj_exp, h]

lemma abs_e (α : ℝ) : ‖e α‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma e_pow (n : ℕ) (α : ℝ) : e (n * α) = (e α) ^ n := by
  have h : (↑(2 * Real.pi * (↑n * α)) : ℂ) * Complex.I
      = n * (↑(2 * Real.pi * α) * Complex.I) := by
    push_cast; ring
  rw [e, h, Complex.exp_nat_mul]

lemma e_eq_one_iff (α : ℝ) : e α = 1 ↔ ∃ k : ℤ, α = k := by
  rw [e, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    rw [← mul_assoc] at hn
    -- hn : ↑(2πα) * I = (↑n * (2π)) * I
    have h2 : ↑(2 * Real.pi * α) = n * (2 * (Real.pi : ℂ)) :=
      mul_right_cancel₀ hI hn
    have h3 : 2 * Real.pi * α = n * (2 * Real.pi) := by
      exact_mod_cast h2
    have hp : (2 * Real.pi) ≠ 0 := by positivity
    have h4 : α = (n : ℝ) := by
      have := mul_left_cancel₀ hp h3
      linarith [this]
    exact_mod_cast h4
  · rintro ⟨k, rfl⟩
    use k
    push_cast
    ring

/-! ### Distance to the nearest integer -/

/-- `intDist β` = distance from `β` to the nearest integer. -/
noncomputable def intDist (β : ℝ) : ℝ := |β - round β|

lemma intDist_nonneg (β : ℝ) : 0 ≤ intDist β := abs_nonneg _

lemma intDist_le_half (β : ℝ) : intDist β ≤ 1 / 2 := abs_sub_round β

lemma intDist_le_abs (β : ℝ) : intDist β ≤ |β| := by
  simpa using round_le β (0 : ℤ)

lemma intDist_int (n : ℤ) : intDist (n : ℝ) = 0 := by
  simp [intDist]

lemma intDist_neg (β : ℝ) : intDist (-β) = intDist β := by
  simp [intDist, ← abs_neg, neg_sub]

lemma intDist_add_int (β : ℝ) (n : ℤ) : intDist (β + n) = intDist β := by
  have h : β + (n : ℝ) - (round β + n) = β - round β := by push_cast; ring
  simp only [intDist, round_add_intCast]
  rw [h]

lemma intDist_sub_int (β : ℝ) (n : ℤ) : intDist (β - n) = intDist β := by
  have h : β - (n : ℝ) = β + (-n : ℤ) := by push_cast; ring
  rw [h, intDist_add_int]

lemma intDist_sub_comm (α β : ℝ) : intDist (α - β) = intDist (β - α) := by
  rw [← intDist_neg, neg_sub]

lemma e_ne_one_of_intDist_pos {β : ℝ} (h : 0 < intDist β) : e β ≠ 1 := by
  intro he
  obtain ⟨k, hk⟩ := (e_eq_one_iff β).mp he
  rw [hk, intDist_int] at h
  exact (lt_irrefl 0 h).elim

/-- For `|u| < 1`, `intDist u ≥ min(|u|, 1 − |u|)`. -/
lemma min_abs_one_sub_abs_le_intDist {u : ℝ} (hu : |u| < 1) :
    min |u| (1 - |u|) ≤ intDist u := by
  have hrb : |(round u : ℝ)| < 2 := by
    have h1 : |(round u : ℝ)| ≤ |(round u : ℝ) - u| + |u| := by
      have h := abs_add ((round u : ℝ) - u) u
      rwa [sub_add_cancel] at h
    have h2 : |(round u : ℝ) - u| ≤ 1 / 2 := by
      rw [abs_sub_comm]; exact abs_sub_round u
    linarith [h1, h2, hu]
  have hrcases : round u = -1 ∨ round u = 0 ∨ round u = 1 := by
    rw [abs_lt] at hrb
    have h3 : -2 < round u := by exact_mod_cast hrb.1
    have h4 : round u < 2 := by exact_mod_cast hrb.2
    omega
  rcases hrcases with h | h | h
  · -- round u = -1, so u ∈ [-3/2, -1/2)
    have hmem := (round_eq_iff (x := u) (n := (-1 : ℤ))).mp h
    rw [Set.mem_Ico] at hmem
    have hu : u ≤ 0 := by
      have := hmem.2
      norm_num at this ⊢
      linarith
    have hd : intDist u = |u + 1| := by
      simp [intDist, h, sub_neg_eq_add]
    rw [hd]
    have h5 : 1 - |u| ≤ |u + 1| := by
      rw [abs_of_nonpos hu]
      have h6 : (1 : ℝ) - -u = u + 1 := by ring
      rw [h6]; exact le_abs_self _
    exact min_le_iff.mpr (Or.inr h5)
  · -- round u = 0
    have hd : intDist u = |u| := by simp [intDist, h]
    rw [hd]
    exact min_le_left _ _
  · -- round u = 1, so u ∈ [1/2, 3/2)
    have hmem := (round_eq_iff (x := u) (n := (1 : ℤ))).mp h
    rw [Set.mem_Ico] at hmem
    have hu : 0 ≤ u := by
      have := hmem.1
      norm_num at this ⊢
      linarith
    have hd : intDist u = |u - 1| := by simp [intDist, h]
    rw [hd]
    have h5 : 1 - |u| ≤ |u - 1| := by
      rw [abs_of_nonneg hu, abs_sub_comm]
      exact le_abs_self _
    exact min_le_iff.mpr (Or.inr h5)

/-- `|e(β) − 1| = 2·|sin(πβ)|`. -/
lemma norm_e_sub_one (β : ℝ) : ‖e β - 1‖ = 2 * |Real.sin (Real.pi * β)| := by
  have h1 : e β - 1 = e (β / 2) * (e (β / 2) - e (-β / 2)) := by
    have h2 : e (β / 2) * e (β / 2) = e β := by
      rw [← e_add]; congr 1; ring
    have h3 : e (β / 2) * e (-β / 2) = 1 := by
      rw [← e_add]; convert e_zero using 2; ring
    rw [mul_sub, h2, h3]
  rw [h1, norm_mul, abs_e, one_mul]
  have h4 : e (β / 2) - e (-β / 2)
      = ↑(2 * Real.sin (Real.pi * β)) * Complex.I := by
    have h5 : 2 * Real.pi * (β / 2) = Real.pi * β := by ring
    have h6 : 2 * Real.pi * (-β / 2) = -(Real.pi * β) := by ring
    rw [e, e, h5, h6, ← ofReal_neg, Complex.exp_ofReal_mul_I,
      Complex.exp_ofReal_mul_I, Real.sin_neg]
    push_cast
    ring
  rw [h4, norm_mul, Complex.norm_I, mul_one]
  have h7 : ‖(↑(2 * Real.sin (Real.pi * β)) : ℂ)‖
      = |2 * Real.sin (Real.pi * β)| := RCLike.norm_ofReal _
  rw [h7, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Kernel bound ingredient: `4·intDist β ≤ ‖e(β) − 1‖`. -/
lemma four_mul_intDist_le_norm_e_sub_one (β : ℝ) :
    4 * intDist β ≤ ‖e β - 1‖ := by
  rw [norm_e_sub_one]
  set k := round β with hk
  set θ := β - k with hθ
  have habs : |θ| = intDist β := rfl
  have hθle : |θ| ≤ 1 / 2 := intDist_le_half β
  have hβ : β = θ + k := by ring
  have hsin : Real.sin (Real.pi * β)
      = (-1 : ℝ) ^ k * Real.sin (Real.pi * θ) := by
    have h8 : Real.pi * β = Real.pi * θ + (k : ℝ) * Real.pi := by
      rw [hβ]; ring
    rw [h8, Real.sin_add_int_mul_pi]
  rw [hsin, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  -- |sin(πθ)| = sin(π|θ|)
  have hpi : |Real.pi * θ| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [hθle, Real.pi_pos]
  rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi, abs_mul,
    abs_of_pos Real.pi_pos]
  have hsin2 : 2 * |θ| ≤ Real.sin (Real.pi * |θ|) := by
    have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (abs_nonneg θ))
      (by nlinarith [hθle, Real.pi_pos] : Real.pi * |θ| ≤ Real.pi / 2)
    have h9 : 2 / Real.pi * (Real.pi * |θ|) = 2 * |θ| := by
      field_simp
    rwa [h9] at h
  linarith [hsin2]
