import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# JSP-000314 — an explicit Nagura-type prime gap

This file proves that every `x ≥ 10 ^ 16` admits a prime `p` in the
interval `(x, 3x/2]`:

* `exists_prime_in_band_of_ge`: explicit threshold form,
  `∀ x, 10 ^ 16 ≤ x → ∃ p, p.Prime ∧ x < p ∧ 2 * p ≤ 3 * x`, which is
  exactly the hypothesis shape expected by
  `QuadThin.quadRegimeOpen_thin_of_prime_gap` (applied at `x = n - k` in
  the thin band `n ≤ 3k`).
* `exists_prime_in_band`: the packaged `Filter.atTop` version.

The proof is the classical Erdős/Chebyshev factorial argument.  With

    V(n) = log n! − log⌊n/2⌋! − log⌊n/3⌋! − log⌊n/5⌋! + log⌊n/30⌋!

the periodic coefficient `g(k) = k − ⌊k/2⌋ − ⌊k/3⌋ − ⌊k/5⌋ + ⌊k/30⌋`
satisfies `g(k) ∈ {0, 1}` and `g(k) = 1` for `1 ≤ k < 6`, giving

    ψ(n) − ψ(n/6) ≤ V(n) ≤ ψ(n).

The main term of `V(n)` is `A·n` with
`A = log 2 / 2 + log 3 / 3 + log 5 / 5 − log 30 / 30 ∈ [0.88, 2]`, with
error `O(log n)`; telescoping over powers of `6` yields
`ψ(n) ≤ (6/5)·A·n + O(log² n)`.  Since `3/2 > 6/5`, the difference
`ψ(3x/2) − ψ(x)` has a positive linear main term `(3/10)·A·x`, which
dominates the `O(√x log x)` error in `ψ − θ` (mathlib's
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`) once `x ≥ 10 ^ 16`, so
`θ(3x/2) − θ(x) > 0` — i.e. `primesLE (3x/2) \ primesLE x` is nonempty.
-/

open Finset Real ArithmeticFunction
open scoped Chebyshev

namespace JSP314

private def g (k : ℕ) : ℝ := (k : ℝ) - ((k / 2 : ℕ) : ℝ) - ((k / 3 : ℕ) : ℝ) - ((k / 5 : ℕ) : ℝ) + ((k / 30 : ℕ) : ℝ)

private lemma g_add_30 (k : ℕ) : g (k + 30) = g k := by
  have h2 : (k + 30) / 2 = k / 2 + 15 := by
    rw [show 30 = 15 * 2 from rfl, Nat.add_mul_div_right k 15 (by norm_num)]
  have h3 : (k + 30) / 3 = k / 3 + 10 := by
    rw [show 30 = 10 * 3 from rfl, Nat.add_mul_div_right k 10 (by norm_num)]
  have h5 : (k + 30) / 5 = k / 5 + 6 := by
    rw [show 30 = 6 * 5 from rfl, Nat.add_mul_div_right k 6 (by norm_num)]
  have h30 : (k + 30) / 30 = k / 30 + 1 := by
    rw [show 30 = 1 * 30 from rfl, Nat.add_mul_div_right k 1 (by norm_num)]
  simp only [g, h2, h3, h5, h30]
  push_cast
  ring

private lemma g_mod30 (k : ℕ) : g k = g (k % 30) := by
  conv_lhs => rw [← Nat.div_add_mod k 30]
  generalize k % 30 = r
  generalize k / 30 = q
  induction q with
  | zero => simp
  | succ j ih =>
    have hrw : 30 * (j + 1) + r = (30 * j + r) + 30 := by omega
    rw [hrw, g_add_30]
    exact ih

private lemma g_mem (k : ℕ) : g k = 0 ∨ g k = 1 := by
  rw [g_mod30]
  have h : k % 30 < 30 := Nat.mod_lt _ (by norm_num)
  interval_cases h' : k % 30 <;> norm_num [g]

private lemma g_nonneg (k : ℕ) : 0 ≤ g k := by
  rcases g_mem k with h | h <;> simp [h]

private lemma g_le_one (k : ℕ) : g k ≤ 1 := by
  rcases g_mem k with h | h <;> simp [h]

private lemma g_eq_one {k : ℕ} (h1 : 1 ≤ k) (h6 : k < 6) : g k = 1 := by
  interval_cases k <;> norm_num [g]

/-- `log n! = ∑_{m ≤ n} Λ(m)·⌊n/m⌋`. -/
theorem log_factorial_eq_sum_Λ (n : ℕ) :
    Real.log (n.factorial) = ∑ m ∈ Ioc 0 n, Λ m * ((n / m : ℕ) : ℝ) := by
  have h1 : Real.log (n.factorial) = ∑ k ∈ Ioc 0 n, Real.log (k : ℝ) := by
    have hne : ∀ i ∈ range n, ((i + 1 : ℕ) : ℝ) ≠ 0 :=
      fun i _ ↦ Nat.cast_ne_zero.mpr (by omega)
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod, Real.log_prod hne]
    symm
    refine Finset.sum_nbij' (· - 1) (· + 1) ?_ ?_ ?_ ?_ ?_
    · intro a ha; rw [Finset.mem_range]; rw [Finset.mem_Ioc] at ha; omega
    · intro a ha; rw [Finset.mem_Ioc]; rw [Finset.mem_range] at ha; omega
    · intro a ha; rw [Finset.mem_Ioc] at ha; omega
    · intro a ha; rw [Finset.mem_range] at ha; omega
    · intro a ha; rw [Finset.mem_Ioc] at ha
      rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
  rw [h1]
  have h2 : ∀ k ∈ Ioc 0 n, Real.log (k : ℝ) = ∑ d ∈ k.divisors, Λ d :=
    fun k _ ↦ vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h2]
  have hdiv : ∀ k ∈ Ioc 0 n, k.divisors = (Ioc 0 n).filter (· ∣ k) := by
    intro k hk
    ext d
    rw [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_divisors]
    constructor
    · rintro ⟨hdk, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdk (Finset.mem_Ioc.mp hk).1,
        (Nat.le_of_dvd (Finset.mem_Ioc.mp hk).1 hdk).trans (Finset.mem_Ioc.mp hk).2⟩, hdk⟩
    · rintro ⟨hdioc, hdk⟩
      exact ⟨hdk, (Finset.mem_Ioc.mp hk).1.ne'⟩
  rw [Finset.sum_congr rfl (fun k hk ↦ by rw [hdiv k hk])]
  have swap : ∀ f : ℕ → ℝ,
      ∑ k ∈ Ioc 0 n, ∑ d ∈ (Ioc 0 n).filter (· ∣ k), f d =
        ∑ d ∈ Ioc 0 n, f d * ((Ioc 0 n).filter (d ∣ ·)).card := by
    intro f
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_comm _ _
  rw [swap]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Nat.Ioc_filter_dvd_card_eq_div]

/-- Chebyshev's `V(n) = log n! - log ⌊n/2⌋! - log ⌊n/3⌋! - log ⌊n/5⌋! + log ⌊n/30⌋!`. -/
private noncomputable def V (n : ℕ) : ℝ :=
  Real.log n.factorial - Real.log (n / 2).factorial - Real.log (n / 3).factorial
    - Real.log (n / 5).factorial + Real.log (n / 30).factorial

private lemma log_factorial_div_eq_sum (n c : ℕ) :
    Real.log ((n / c).factorial) = ∑ m ∈ Ioc 0 n, Λ m * ((n / m / c : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum_Λ]
  have key : ∀ m : ℕ, n / c / m = n / m / c := fun m ↦ by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [key]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right (Nat.div_le_self n c))
  intro m hm hnm
  rw [Finset.mem_Ioc] at hm hnm
  push Not at hnm
  have hlt : n / c < m := hnm hm.1
  have hdiv : n / m / c = 0 := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · simp [hc]
    · rw [Nat.div_div_eq_div_mul]
      exact Nat.div_eq_of_lt ((Nat.div_lt_iff_lt_mul hc).mp hlt)
  rw [hdiv]; simp

private lemma V_eq_sum (n : ℕ) :
    V n = ∑ m ∈ Ioc 0 n, Λ m * g (n / m) := by
  rw [V, log_factorial_eq_sum_Λ n,
    log_factorial_div_eq_sum n 2, log_factorial_div_eq_sum n 3,
    log_factorial_div_eq_sum n 5, log_factorial_div_eq_sum n 30]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [g]
  ring

private lemma V_le_psi (n : ℕ) : V n ≤ ψ (n : ℝ) := by
  rw [V_eq_sum]
  show (∑ m ∈ Ioc 0 n, Λ m * g (n / m)) ≤ ∑ m ∈ Ioc 0 ⌊(n : ℝ)⌋₊, Λ m
  rw [Nat.floor_natCast]
  exact Finset.sum_le_sum fun m _ ↦ by
    calc Λ m * g (n / m) ≤ Λ m * 1 :=
        mul_le_mul_of_nonneg_left (g_le_one _) vonMangoldt_nonneg
      _ = Λ m := mul_one _

private lemma psi_sub_le_V (n : ℕ) : ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) ≤ V n := by
  have hsub : Ioc 0 (n / 6) ⊆ Ioc 0 n :=
    Finset.Ioc_subset_Ioc_right (Nat.div_le_self _ _)
  have split : Ioc 0 n \ Ioc 0 (n / 6) = Ioc (n / 6) n := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have hψ : ψ (n : ℝ) - ψ ((n / 6 : ℕ) : ℝ) = ∑ m ∈ Ioc (n / 6) n, Λ m := by
    show (∑ m ∈ Ioc 0 ⌊(n : ℝ)⌋₊, Λ m) - ∑ m ∈ Ioc 0 ⌊((n / 6 : ℕ) : ℝ)⌋₊, Λ m = _
    rw [Nat.floor_natCast, Nat.floor_natCast, ← split]
    have hsd := Finset.sum_sdiff hsub (f := fun m => Λ m)
    linarith
  rw [V_eq_sum, hψ]
  calc ∑ m ∈ Ioc (n / 6) n, Λ m
      = ∑ m ∈ Ioc (n / 6) n, Λ m * g (n / m) := by
        refine Finset.sum_congr rfl fun m hm ↦ ?_
        rw [Finset.mem_Ioc] at hm
        have hmpos : 0 < m := by omega
        have h1 : 1 ≤ n / m := (Nat.one_le_div_iff hmpos).mpr hm.2
        have h6 : n / m < 6 := by
          have hn : n < 6 * m := by
            have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)).mp hm.1
            omega
          exact (Nat.div_lt_iff_lt_mul hmpos).mpr hn
        rw [g_eq_one h1 h6, mul_one]
    _ ≤ ∑ m ∈ Ioc 0 n, Λ m * g (n / m) := by
        rw [← split]
        have hsd := Finset.sum_sdiff hsub (f := fun m => Λ m * g (n / m))
        have hnn : 0 ≤ ∑ m ∈ Ioc 0 (n / 6), Λ m * g (n / m) :=
          Finset.sum_nonneg fun m _ ↦ mul_nonneg vonMangoldt_nonneg (g_nonneg _)
        linarith

private lemma one_add_inv_pow_le_exp (m : ℕ) (hm : 1 ≤ m) :
    (1 + 1/(m:ℝ))^m ≤ rexp 1 := by
  have h : (1:ℝ) + 1/m ≤ rexp (1/m) := by
    have := Real.add_one_le_exp (1/(m:ℝ))
    linarith
  calc (1 + 1/(m:ℝ))^m ≤ (rexp (1/(m:ℝ)))^m := pow_le_pow_left₀ (by positivity) h m
    _ = rexp 1 := by
        rw [← Real.exp_nat_mul,
          mul_one_div_cancel (Nat.cast_ne_zero.mpr (by omega : m ≠ 0))]

private lemma exp_le_one_add_inv_pow (m : ℕ) (hm : 1 ≤ m) :
    rexp 1 ≤ (1 + 1/(m:ℝ))^(m+1) := by
  have hmc : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0:ℝ) < 1 - 1/((m:ℝ)+1) := by
    have hlt : (1:ℝ)/((m:ℝ)+1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    linarith
  have h1 : (1:ℝ) - 1/((m:ℝ)+1) ≤ rexp (-(1/((m:ℝ)+1))) := by
    have := Real.add_one_le_exp (-(1/((m:ℝ)+1)))
    linarith
  rw [Real.exp_neg] at h1
  have h2 : rexp (1/((m:ℝ)+1)) ≤ (1 - 1/((m:ℝ)+1))⁻¹ :=
    (le_inv_comm₀ (Real.exp_pos _) hpos).mpr h1
  have h4 : (1 - 1/((m:ℝ)+1))⁻¹ = 1 + 1/(m:ℝ) := by
    have hm' : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm1' : ((m:ℝ)+1) ≠ 0 := by positivity
    have h5 : (1:ℝ) - 1/((m:ℝ)+1) = (m:ℝ)/((m:ℝ)+1) := by
      rw [eq_div_iff hm1', sub_mul, one_mul, div_mul_cancel₀ _ hm1']
      ring
    rw [h5, inv_div, add_div, div_self hm']
  rw [h4] at h2
  calc rexp 1 = (rexp (1/((m:ℝ)+1)))^(m+1) := by
        rw [← Real.exp_nat_mul]
        push_cast
        rw [mul_one_div_cancel (by positivity : ((m:ℝ)+1) ≠ 0)]
    _ ≤ (1 + 1/(m:ℝ))^(m+1) := pow_le_pow_left₀ (Real.exp_pos _).le h2 _

private lemma pow_le_exp_mul_factorial : ∀ m : ℕ, (m:ℝ)^m ≤ rexp m * m.factorial := by
  intro m
  induction m with
  | zero => simp
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp
    · have key := one_add_inv_pow_le_exp j hj
      have hj' : (j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have e2 : ((j:ℝ)+1)^j = (j:ℝ)^j * (1 + 1/(j:ℝ))^j := by
        rw [← mul_pow]
        congr 1
        rw [mul_add, mul_one_div_cancel hj', mul_one]
      rw [Nat.factorial_succ]
      push_cast
      rw [pow_succ, e2]
      have e3 : rexp (↑j + 1) = rexp ↑j * rexp 1 := by
        rw [← Real.exp_add]
      rw [e3]
      calc (j:ℝ)^j * (1 + 1/(j:ℝ))^j * ((j:ℝ)+1)
          ≤ (rexp ↑j * ↑(Nat.factorial j) * rexp 1) * ((j:ℝ)+1) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul ih key (by positivity) (by positivity)) (by positivity)
        _ = rexp ↑j * rexp 1 * ((↑j + 1) * ↑(Nat.factorial j)) := by ring

private lemma exp_pow_mul_factorial_le : ∀ m : ℕ, 1 ≤ m →
    rexp m * m.factorial ≤ rexp 1 * (m:ℝ)^(m+1) := by
  intro m hm
  induction m with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; simp
    · have key2 := exp_le_one_add_inv_pow j hj
      have hj' : (j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have ih' := ih hj
      have e4 : ((j:ℝ)+1)^(j+1) = (j:ℝ)^(j+1) * (1 + 1/(j:ℝ))^(j+1) := by
        rw [← mul_pow]
        congr 1
        rw [mul_add, mul_one_div_cancel hj', mul_one]
      have core : rexp 1 * (j:ℝ)^(j+1) ≤ ((j:ℝ)+1)^(j+1) := by
        rw [e4]
        rw [mul_comm (rexp 1)]
        exact mul_le_mul_of_nonneg_left key2 (by positivity)
      rw [Nat.factorial_succ]
      push_cast
      have e3 : rexp (↑j + 1) = rexp ↑j * rexp 1 := by
        rw [← Real.exp_add]
      rw [e3]
      calc rexp ↑j * rexp 1 * ((↑j + 1) * ↑(Nat.factorial j))
          = rexp 1 * (↑j + 1) * (rexp ↑j * ↑(Nat.factorial j)) := by ring
        _ ≤ rexp 1 * (↑j + 1) * (rexp 1 * (j:ℝ)^(j+1)) := by
            have hnn : (0:ℝ) ≤ rexp 1 * (↑j + 1) := by positivity
            exact mul_le_mul_of_nonneg_left ih' hnn
        _ ≤ rexp 1 * (↑j + 1) * ((j:ℝ)+1)^(j+1) := by
            have hnn : (0:ℝ) ≤ rexp 1 * (↑j + 1) := by positivity
            exact mul_le_mul_of_nonneg_left core hnn
        _ = rexp 1 * (↑j + 1)^(j+2) := by rw [pow_succ]; ring

private lemma log_factorial_ge (m : ℕ) :
    (m:ℝ) * Real.log m - m ≤ Real.log m.factorial := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have h := pow_le_exp_mul_factorial m
    have hlog := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
    linarith

private lemma log_factorial_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log m.factorial ≤ (m:ℝ) * Real.log m - m + Real.log m + 1 := by
  have h := exp_pow_mul_factorial_le m hm
  have hlog := (Real.log_le_log_iff (by positivity) (by positivity)).mpr h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

private lemma log_factorial_floor_sub (u : ℝ) (hu : 1 ≤ u) :
    |Real.log ⌊u⌋₊.factorial - (u * Real.log u - u)| ≤ 2 * Real.log u + 2 := by
  set m := ⌊u⌋₊ with hm_def
  have hm1 : 1 ≤ m := Nat.floor_pos.mpr hu
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  have hupos : (0:ℝ) < u := by linarith
  have hmu : (m:ℝ) ≤ u := Nat.floor_le (zero_le_one.trans hu)
  have hum : u < (m:ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  have hlogm' : Real.log m ≤ Real.log u := (Real.log_le_log_iff hmpos hupos).mpr hmu
  -- decomposition h(u) - h(m) = m·log(u/m) + (u-m)(log u - 1)
  have h3 : (u * Real.log u - u) - ((m:ℝ) * Real.log m - m)
      = m * Real.log (u/m) + (u - m) * (Real.log u - 1) := by
    rw [Real.log_div hupos.ne' hmpos.ne']
    ring
  have keylow : 0 ≤ (u * Real.log u - u) - ((m:ℝ) * Real.log m - m) := by
    have h1 : m * (1 - m/u) ≤ m * Real.log (u/m) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ m)
      have hsub := Real.one_sub_inv_le_log_of_pos (div_pos hupos hmpos)
      rwa [inv_div] at hsub
    have h2 : (u - m) * (-(1/u)) ≤ (u - m) * (Real.log u - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ u - m)
      have hsub := Real.one_sub_inv_le_log_of_pos hupos
      rw [one_div]
      linarith
    have h4 : m * (1 - m/u) + (u - m) * (-(1/u)) = (u - m) * ((m - 1)/u) := by
      field_simp
      ring
    have h5 : (0:ℝ) ≤ (u - m) * ((m - 1)/u) := by
      have hm1r : (1:ℝ) ≤ m := by exact_mod_cast hm1
      apply mul_nonneg (by linarith)
      exact div_nonneg (by linarith) (by positivity)
    calc (0:ℝ) ≤ (u - m) * ((m - 1)/u) := h5
      _ = m * (1 - m/u) + (u - m) * (-(1/u)) := h4.symm
      _ ≤ m * Real.log (u/m) + (u - m) * (Real.log u - 1) := add_le_add h1 h2
      _ = (u * Real.log u - u) - ((m:ℝ) * Real.log m - m) := h3.symm
  have keyupp : (u * Real.log u - u) - ((m:ℝ) * Real.log m - m) ≤ Real.log u + 1 := by
    have h1 : m * Real.log (u/m) ≤ u - m := by
      have hle : Real.log (u/m) ≤ u/m - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hupos hmpos)
      calc m * Real.log (u/m) ≤ m * (u/m - 1) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = u - m := by field_simp
    have h2 : (u - m) * (Real.log u - 1) ≤ Real.log u := by
      have hle1 : (u - m) * (Real.log u - 1) ≤ (u - m) * Real.log u :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hle2 : (u - m) * Real.log u ≤ 1 * Real.log u :=
        mul_le_mul_of_nonneg_right (by linarith) hlogu
      linarith
    calc (u * Real.log u - u) - ((m:ℝ) * Real.log m - m)
        = m * Real.log (u/m) + (u - m) * (Real.log u - 1) := h3
      _ ≤ (u - m) + Real.log u := add_le_add h1 h2
      _ ≤ 1 + Real.log u := by linarith
      _ = Real.log u + 1 := by ring
  have blo := log_factorial_ge m
  have bhi := log_factorial_le m hm1
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith

/-- The main-term constant `A ≈ 0.9213`. -/
private noncomputable def A : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 - Real.log 30 / 30

private lemma V_sub_main (n : ℕ) (hn : 30 ≤ n) :
    |V n - A * n| ≤ 10 * Real.log n + 10 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnc : ∀ c : ℕ, c ∈ ({1, 2, 3, 5, 30} : Finset ℕ) → 1 ≤ (n:ℝ)/c := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [one_le_div (by positivity)]
      exact_mod_cast (by omega)
  have hmain : ((n:ℝ) * Real.log n - n)
      - ((n/2:ℝ) * Real.log (n/2) - n/2)
      - ((n/3:ℝ) * Real.log (n/3) - n/3)
      - ((n/5:ℝ) * Real.log (n/5) - n/5)
      + ((n/30:ℝ) * Real.log (n/30) - n/30) = A * n := by
    rw [Real.log_div hnpos.ne' (by norm_num : (2:ℝ) ≠ 0),
      Real.log_div hnpos.ne' (by norm_num : (3:ℝ) ≠ 0),
      Real.log_div hnpos.ne' (by norm_num : (5:ℝ) ≠ 0),
      Real.log_div hnpos.ne' (by norm_num : (30:ℝ) ≠ 0)]
    unfold A
    ring
  have hpiece : ∀ c : ℕ, c ∈ ({1, 2, 3, 5, 30} : Finset ℕ) →
      |Real.log (n/c).factorial - ((n/c:ℝ) * Real.log (n/c) - n/c)| ≤ 2 * Real.log n + 2 := by
    intro c hc
    have huc : 1 ≤ (n:ℝ)/c := hnc c hc
    have hfl := log_factorial_floor_sub ((n:ℝ)/c) huc
    rw [Nat.floor_div_eq_div] at hfl
    have hcle : (1:ℝ) ≤ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hle : Real.log ((n:ℝ)/c) ≤ Real.log n := by
      apply (Real.log_le_log_iff (by positivity) hnpos).mpr
      exact div_le_self hnpos.le hcle
    have hb : 2 * Real.log (↑n/↑c) + 2 ≤ 2 * Real.log ↑n + 2 := by linarith
    exact hfl.trans hb
  set D := fun c : ℕ ↦
    Real.log (n/c).factorial - ((n/c:ℝ) * Real.log (n/c) - n/c) with hD
  have hD1 : |V n - A * n| = |D 1 - D 2 - D 3 - D 5 + D 30| := by
    congr 1
    rw [V]
    simp only [hD, Nat.div_one, Nat.cast_one, Nat.cast_ofNat, div_one]
    linarith [hmain]
  rw [hD1]
  calc |D 1 - D 2 - D 3 - D 5 + D 30|
      ≤ |D 1| + |D 2| + |D 3| + |D 5| + |D 30| := by
        linarith [abs_add_le (D 1 - D 2 - D 3 - D 5) (D 30),
          abs_sub (D 1 - D 2 - D 3) (D 5), abs_sub (D 1 - D 2) (D 3), abs_sub (D 1) (D 2)]
    _ ≤ (2 * Real.log n + 2) + (2 * Real.log n + 2) + (2 * Real.log n + 2)
        + (2 * Real.log n + 2) + (2 * Real.log n + 2) := by
        have h1 := hpiece 1 (by decide)
        have h2 := hpiece 2 (by decide)
        have h3 := hpiece 3 (by decide)
        have h5 := hpiece 5 (by decide)
        have h30 := hpiece 30 (by decide)
        simp only [hD, Nat.div_one, Nat.cast_one, div_one] at h1 h2 h3 h5 h30 ⊢
        linarith
    _ = 10 * Real.log n + 10 := by ring

private lemma log_two_lt_one : Real.log 2 < 1 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 2)]
  exact lt_trans (by norm_num) Real.exp_one_gt_d9

private lemma log_three_gt_one : (1:ℝ) < Real.log 3 := by
  have h : rexp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) h

private lemma log_five_gt : (8:ℝ)/5 < Real.log 5 := by
  have e8 : rexp (8:ℝ) = (rexp 1)^8 := by
    rw [← Real.exp_nat_mul 1 8]
    norm_num
  have h : rexp (8:ℝ) < (5:ℝ)^5 := by
    rw [e8]
    calc (rexp 1)^8 ≤ (2.7182818286:ℝ)^8 :=
        pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le _
      _ < (5:ℝ)^5 := by norm_num
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 5)]
  have h5 : (rexp (8/5:ℝ))^5 = rexp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) (by rwa [h5])

private lemma log_thirty_lt : Real.log 30 < (7:ℝ)/2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 30)]
  have e7 : rexp (7:ℝ) = (rexp 1)^7 := by
    rw [← Real.exp_nat_mul 1 7]
    norm_num
  have h : (30:ℝ)^2 < rexp 7 := by
    rw [e7]
    calc (30:ℝ)^2 < (2.7182818283:ℝ)^7 := by norm_num
      _ < (rexp 1)^7 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h2 : (rexp (7/2:ℝ))^2 = rexp 7 := by
    rw [← Real.exp_nat_mul]
    norm_num
  exact lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le (by rwa [← h2] at h)

private lemma A_gt : (88:ℝ)/100 ≤ A := by
  unfold A
  linarith [Real.log_two_gt_d9, log_three_gt_one, log_five_gt, log_thirty_lt]

private lemma A_nonneg : (0:ℝ) ≤ A := le_trans (by norm_num) A_gt

private lemma A_le_two : A ≤ 2 := by
  have h2 := log_two_lt_one
  have h3 : Real.log 3 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 3)]
    have e2 : rexp (2:ℝ) = (rexp 1)^2 := by
      rw [← Real.exp_nat_mul 1 2]
      norm_num
    rw [e2]
    calc (3:ℝ) < (2.7182818283:ℝ)^2 := by norm_num
      _ < (rexp 1)^2 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h5 : Real.log 5 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 5)]
    have e2 : rexp (2:ℝ) = (rexp 1)^2 := by
      rw [← Real.exp_nat_mul 1 2]
      norm_num
    rw [e2]
    calc (5:ℝ) < (2.7182818283:ℝ)^2 := by norm_num
      _ < (rexp 1)^2 := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h30 : (0:ℝ) ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  unfold A
  linarith

private lemma psi_lower (m : ℕ) (hm : 30 ≤ m) :
    A * m - 10 * Real.log m - 10 ≤ ψ (m:ℝ) := by
  have h1 := V_le_psi m
  have h2 := (abs_le.mp (V_sub_main m hm)).1
  linarith

private lemma V_le_all (m : ℕ) : V m ≤ A * m + 10 * Real.log m + 160 := by
  rcases Nat.lt_or_ge m 30 with hm | hm
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp [V]
    · have hψ := V_le_psi m
      have hb := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg m)
      have hlog4 : Real.log 4 ≤ 1.4 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
        linarith [Real.log_two_lt_d9]
      have hmle : (m:ℝ) ≤ 29 := by exact_mod_cast (by omega : m ≤ 29)
      have hm1 : (1:ℝ) ≤ m := by exact_mod_cast h0
      have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast h0)
      have key : (Real.log 4 + 4) * m ≤ A * m + 10 * Real.log m + 160 := by
        have h1 : (Real.log 4 + 4) * m ≤ 5.4 * 29 :=
          mul_le_mul (by linarith) hmle (Nat.cast_nonneg m) (by norm_num)
        have h2 : ((88:ℝ)/100) * 1 ≤ A * m :=
          mul_le_mul A_gt hm1 zero_le_one (by linarith [A_gt])
        nlinarith
      linarith
  · have hv := (abs_le.mp (V_sub_main m hm)).2
    linarith

private lemma psi_upper (n : ℕ) (hn : 1 ≤ n) :
    ψ (n:ℝ) ≤ (6/5) * A * n + 10 * (Real.log n)^2 + 170 * Real.log n + 160 := by
  set J := Nat.log 6 n + 1 with hJ
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hJ0 : n / 6^J = 0 := Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)
  have h6j : ∀ j < J, 6^j ≤ n := fun j hj ↦
    (Nat.pow_le_pow_right (by norm_num) (by omega)).trans (Nat.pow_log_le_self 6 hn0)
  have fJ' : ψ ((n / 6^J : ℕ):ℝ) = 0 := by
    rw [hJ0, Nat.cast_zero]
    show ψ (0:ℝ) = 0
    rw [show ψ (0:ℝ) = ∑ m ∈ Ioc 0 ⌊(0:ℝ)⌋₊, Λ m from rfl]
    simp
  have tele : ψ (n:ℝ) = ∑ j ∈ range J,
      (ψ ((n / 6^j : ℕ):ℝ) - ψ ((n / 6^(j+1) : ℕ):ℝ)) := by
    rw [Finset.sum_range_sub' (fun j => ψ ((n / 6^j : ℕ):ℝ)) J]
    show ψ (n:ℝ) = ψ ((n / 6^0 : ℕ):ℝ) - ψ ((n / 6^J : ℕ):ℝ)
    rw [fJ', sub_zero]
    simp
  have step : ∀ j < J, ψ ((n/6^j:ℕ):ℝ) - ψ ((n/6^(j+1):ℕ):ℝ) ≤ V (n/6^j) := by
    intro j hj
    have hdiv : (n/6^j)/6 = n/6^(j+1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [← hdiv]
    exact psi_sub_le_V _
  have bound : ∀ j ∈ range J, V (n/6^j) ≤ A * (n/6^j : ℕ) + 10 * Real.log n + 160 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hva := V_le_all (n/6^j)
    have hle : ((n/6^j : ℕ):ℝ) ≤ n := by exact_mod_cast Nat.div_le_self _ _
    have hge : (1:ℝ) ≤ (n/6^j : ℕ) := by
      exact_mod_cast (Nat.one_le_div_iff (pow_pos (by norm_num) j)).mpr (h6j j hj)
    have hlog : Real.log ((n/6^j:ℕ):ℝ) ≤ Real.log n :=
      (Real.log_le_log_iff (by positivity) hnpos).mpr hle
    linarith
  have hgeo : (∑ j ∈ range J, ((n/6^j : ℕ):ℝ)) ≤ n * (6/5) := by
    calc ∑ j ∈ range J, ((n/6^j : ℕ):ℝ) ≤ ∑ j ∈ range J, (n:ℝ)/6^j := by
          apply Finset.sum_le_sum
          intro j _
          exact (Nat.cast_div_le (α := ℝ)).trans_eq (by rw [Nat.cast_pow, Nat.cast_ofNat])
      _ = ∑ j ∈ range J, (n:ℝ) * (1/6)^j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [div_eq_mul_inv, ← inv_pow, inv_eq_one_div]
      _ = (n:ℝ) * ∑ j ∈ range J, (1/6:ℝ)^j := by rw [Finset.mul_sum]
      _ ≤ (n:ℝ) * (6/5) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [geom_sum_eq (by norm_num : (1/6:ℝ) ≠ 1) J]
          rw [div_le_iff_of_neg (by norm_num : (1/6:ℝ) - 1 < 0)]
          have hpow' : (0:ℝ) ≤ (1/6:ℝ)^J := by positivity
          linarith
  have hJle : (J:ℝ) ≤ Real.log n + 1 := by
    have hpow : (6:ℝ)^(Nat.log 6 n) ≤ n := by
      exact_mod_cast Nat.pow_log_le_self 6 hn0
    have hlog6' : (1:ℝ) ≤ Real.log 6 := by
      have h : rexp 1 ≤ 6 := le_trans Real.exp_one_lt_d9.le (by norm_num)
      calc (1:ℝ) = Real.log (rexp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log 6 := (Real.log_le_log_iff (Real.exp_pos 1) (by norm_num)).mpr h
    have h1 : (Nat.log 6 n : ℝ) * Real.log 6 ≤ Real.log n := by
      have h2 := (Real.log_le_log_iff (by positivity) hnpos).mpr hpow
      rwa [Real.log_pow] at h2
    have ha : (0:ℝ) ≤ (Nat.log 6 n : ℝ) := by positivity
    have h4 : (Nat.log 6 n : ℝ) * 1 ≤ (Nat.log 6 n : ℝ) * Real.log 6 :=
      mul_le_mul_of_nonneg_left hlog6' ha
    rw [hJ]
    push_cast
    linarith
  calc ψ (n:ℝ) = ∑ j ∈ range J,
        (ψ ((n/6^j:ℕ):ℝ) - ψ ((n/6^(j+1):ℕ):ℝ)) := tele
    _ ≤ ∑ j ∈ range J, V (n/6^j) :=
        Finset.sum_le_sum (fun j hj ↦ step j (Finset.mem_range.mp hj))
    _ ≤ ∑ j ∈ range J, (A * (n/6^j : ℕ) + 10 * Real.log n + 160) :=
        Finset.sum_le_sum (fun j hj ↦ bound j hj)
    _ = A * (∑ j ∈ range J, ((n/6^j : ℕ):ℝ)) + J * (10 * Real.log n + 160) := by
        calc ∑ j ∈ range J, (A * ↑(n/6^j) + 10 * Real.log n + 160)
            = ∑ j ∈ range J, (A * ↑(n/6^j) + (10 * Real.log n + 160)) :=
              Finset.sum_congr rfl (fun j _ ↦ by ring)
          _ = ∑ j ∈ range J, A * ↑(n/6^j) + ∑ _j ∈ range J, (10 * Real.log n + 160) :=
              Finset.sum_add_distrib
          _ = A * (∑ j ∈ range J, ↑(n/6^j)) + J * (10 * Real.log n + 160) := by
              rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ A * (n * (6/5)) + (Real.log n + 1) * (10 * Real.log n + 160) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hgeo A_nonneg
        · exact mul_le_mul_of_nonneg_right hJle (by linarith)
    _ = (6/5) * A * n + 10 * (Real.log n)^2 + 170 * Real.log n + 160 := by ring

private lemma theta_gap_pos {x : ℕ} (hx : 10 ^ 16 ≤ x) :
    0 < θ ((3 * x / 2 : ℕ) : ℝ) - θ (x : ℝ) := by
  set y : ℕ := 3 * x / 2 with hydef
  have hx1 : 1 ≤ x := by omega
  have hx1r : (1:ℝ) ≤ x := by exact_mod_cast hx1
  have hy1 : 1 ≤ y := by omega
  have hy30 : 30 ≤ y := by omega
  have hyr1 : (1:ℝ) ≤ y := by exact_mod_cast hy1
  have hypos : (0:ℝ) < y := by exact_mod_cast hy1
  set L : ℝ := Real.log x with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hx1r
  have hy_cast_le : (y:ℝ) ≤ 3 * (x:ℝ) / 2 := by
    have h := (Nat.cast_div_le (α := ℝ) : ((3 * x / 2 : ℕ) : ℝ) ≤ ((3 * x : ℕ) : ℝ) / 2)
    rw [← hydef] at h
    push_cast at h
    exact h
  have hy_cast_ge : (3 * (x:ℝ) - 1) / 2 ≤ y := by
    have hdm := Nat.div_add_mod (3 * x) 2
    have hmod : 3 * x % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num))
    have h2y : 3 * x ≤ 2 * y + 1 := by omega
    have h2y' : (3:ℝ) * x ≤ 2 * y + 1 := by exact_mod_cast h2y
    linarith
  have hy2 : (y:ℝ) ≤ 2 * x := by
    have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg _
    linarith [hy_cast_le]
  have hyx2 : (y:ℝ) ≤ x ^ 2 := by
    have hx2 : (2:ℝ) ≤ x := by exact_mod_cast (by omega : 2 ≤ x)
    calc (y:ℝ) ≤ 2 * x := hy2
      _ ≤ x * x := mul_le_mul_of_nonneg_right hx2 (Nat.cast_nonneg _)
      _ = x ^ 2 := by ring
  have hlogy : Real.log y ≤ 2 * L := by
    calc Real.log y ≤ Real.log (x ^ 2) :=
        (Real.log_le_log_iff hypos (by positivity)).mpr hyx2
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
      _ = 2 * L := by rw [hLdef]
  -- s = x^{1/4}
  set s : ℝ := Real.sqrt (Real.sqrt x) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hs4 : s ^ 4 = (x:ℝ) := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (√x) ^ 2 := by rw [hs2]
      _ = x := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs : (10:ℝ) ^ 4 ≤ s := by
    have h1 : (10:ℝ) ^ 8 ≤ √x := by
      rw [Real.le_sqrt (by positivity) (Nat.cast_nonneg _)]
      have h16 : ((10:ℝ) ^ 8) ^ 2 = 10 ^ 16 := by norm_num
      rw [h16]
      exact_mod_cast hx
    have h2 : (10:ℝ) ^ 4 ≤ √(√x) := by
      rw [Real.le_sqrt (by positivity) (Real.sqrt_nonneg _)]
      have h8 : ((10:ℝ) ^ 4) ^ 2 = 10 ^ 8 := by norm_num
      rw [h8]
      exact h1
    exact h2
  have hs1 : (1:ℝ) ≤ s := le_trans (by norm_num) hs
  have hs0' : (0:ℝ) < s := lt_of_lt_of_le one_pos hs1
  have hLle : L ≤ 4 * s - 4 := by
    have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0'
    have hlog : L = 4 * Real.log s := by
      rw [hLdef, ← hs4, Real.log_pow]
      push_cast
      ring
    rw [hlog]; linarith
  have hLs4 : L ≤ 4 * s := le_trans hLle (by linarith [hs0])
  have hL2 : L ^ 2 ≤ 16 * s ^ 2 := by
    have h4s : (0:ℝ) ≤ 4 * s - 4 := by linarith [hs1]
    have h := mul_le_mul hLle hLle hL0 h4s
    linarith [h, hs1]
  have hsqrty : Real.sqrt y ≤ 1.5 * s ^ 2 := by
    have hsqrt2 : Real.sqrt (2:ℝ) ≤ 1.5 := by
      have h : (2:ℝ) ≤ 1.5 ^ 2 := by norm_num
      calc Real.sqrt 2 ≤ Real.sqrt (1.5 ^ 2) := Real.sqrt_le_sqrt h
        _ = 1.5 := Real.sqrt_sq (by norm_num)
    calc Real.sqrt y ≤ Real.sqrt (2 * x) := Real.sqrt_le_sqrt hy2
      _ = Real.sqrt 2 * Real.sqrt x := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ 1.5 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg _)
      _ = 1.5 * s ^ 2 := by rw [← hs2]
  -- Chebyshev data
  have hθ1 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (y:ℝ)) hyr1
  have hθ2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (x:ℝ)) hx1r
  rw [← hLdef] at hθ2
  have hlo := psi_lower y hy30
  have hup := psi_upper x hx1
  rw [← hLdef] at hup
  have hAy : A * ((3 * (x:ℝ) - 1) / 2) ≤ A * y := mul_le_mul_of_nonneg_left hy_cast_ge A_nonneg
  have hψd : (3:ℝ)/10 * A * x - A/2 - 10 * Real.log y - 10 - 10 * L^2 - 170 * L - 160
      ≤ ψ (y:ℝ) - ψ (x:ℝ) := by linarith [hlo, hup, hAy]
  have hθd : (3:ℝ)/10 * A * x - A/2 - 10 * Real.log y - 10 - 10 * L^2 - 170 * L - 160
      - 2 * √y * Real.log y - 2 * √x * L
      ≤ θ (y:ℝ) - θ (x:ℝ) := by
    have e1 := (abs_le.mp hθ1).2
    have e2 := (abs_le.mp hθ2).1
    linarith [hψd]
  -- polynomial bounds in s
  have hb1 : 2 * √y * Real.log y ≤ 24 * s^3 := by
    have hlogy' : Real.log y ≤ 8 * s := le_trans hlogy (by linarith [hLs4])
    have h1 : 2 * √y * Real.log y ≤ (3 * s^2) * (8 * s) := by
      apply mul_le_mul _ hlogy' (Real.log_nonneg hyr1)
        (mul_nonneg (by norm_num) (sq_nonneg s))
      calc 2 * √y ≤ 2 * (1.5 * s^2) := mul_le_mul_of_nonneg_left hsqrty (by norm_num)
        _ = 3 * s^2 := by ring
    exact h1.trans_eq (by ring)
  have hb2 : 2 * √x * L ≤ 8 * s^3 := by
    rw [← hs2]
    calc 2 * s^2 * L ≤ (2 * s^2) * (4 * s) :=
        mul_le_mul_of_nonneg_left hLs4 (mul_nonneg (by norm_num) (sq_nonneg s))
      _ = 8 * s^3 := by ring
  have hs2le3 : s^2 ≤ s^3 := by
    have h := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)
    linarith [h]
  have hs1le3 : s ≤ s^3 := by
    have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (add_nonneg hs0 zero_le_one)) hs0
    linarith [h]
  have hc1 : (1:ℝ) ≤ s^3 := le_trans hs1 hs1le3
  have hA4 : (264:ℝ)/1000 * s^4 ≤ (3/10) * A * s^4 := by
    have h := mul_nonneg (sub_nonneg.mpr A_gt) (pow_nonneg hs0 4)
    linarith [h]
  have hA4x : (264:ℝ)/1000 * s^4 ≤ (3/10) * A * (x:ℝ) := by
    calc (264:ℝ)/1000 * s^4 ≤ (3/10) * A * s^4 := hA4
      _ = (3/10) * A * x := by rw [hs4]
  have e1 : A / 2 ≤ s^3 := le_trans (show A / 2 ≤ (1:ℝ) by linarith [A_le_two]) hc1
  have hlogy' : Real.log y ≤ 8 * s := le_trans hlogy (by linarith [hLs4])
  have e2 : 10 * Real.log y ≤ 80 * s^3 :=
    le_trans (show 10 * Real.log y ≤ 80 * s by linarith [hlogy'])
      (show 80 * s ≤ 80 * s^3 by linarith [hs1le3])
  have e3 : (10:ℝ) + 160 ≤ 170 * s^3 := by linarith [hc1]
  have e4 : 10 * L^2 ≤ 160 * s^3 :=
    le_trans (show 10 * L^2 ≤ 160 * s^2 by linarith [hL2])
      (show 160 * s^2 ≤ 160 * s^3 by linarith [hs2le3])
  have e5 : 170 * L ≤ 680 * s^3 :=
    le_trans (show 170 * L ≤ 680 * s by linarith [hLs4])
      (show 680 * s ≤ 680 * s^3 by linarith [hs1le3])
  have hcomp : (264:ℝ)/1000 * s^4 - 1123 * s^3 ≤ θ (y:ℝ) - θ (x:ℝ) := by
    linarith [hθd, hA4x, e1, e2, e3, e4, e5, hb1, hb2]
  have hpos : (0:ℝ) < (264:ℝ)/1000 * s^4 - 1123 * s^3 := by
    have h1 : (1517:ℝ) ≤ (264:ℝ)/1000 * s - 1123 := by linarith [hs]
    have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hs0 3)
    rw [show ((264:ℝ)/1000 * s - 1123) * s^3 = (264:ℝ)/1000 * s^4 - 1123 * s^3 from
      by ring] at h2
    linarith [h2, hc1]
  linarith [hcomp, hpos]

theorem exists_prime_in_band_of_ge : ∀ x : ℕ, 10 ^ 16 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ 2 * p ≤ 3 * x := by
  intro x hx
  have hpos : 0 < θ ((3 * x / 2 : ℕ) : ℝ) - θ (x : ℝ) := theta_gap_pos hx
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log] at hpos
  have hsub : Nat.primesLE x ⊆ Nat.primesLE (3 * x / 2) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (by omega), hp.2⟩
  have hsd := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p : ℝ))
  have hne : (Nat.primesLE (3 * x / 2) \ Nat.primesLE x).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsd
    simp only [zero_add] at hsd
    linarith [hpos]
  obtain ⟨p, hp⟩ := hne
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
  obtain ⟨⟨hpy, hpp⟩, hnx⟩ := hp
  refine ⟨p, hpp, ?_, by omega⟩
  by_contra h
  push Not at h
  exact hnx ⟨h, hpp⟩

theorem exists_prime_in_band :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ 2 * p ≤ 3 * n := by
  filter_upwards [Filter.eventually_ge_atTop (10 ^ 16)] with x hx
  exact exists_prime_in_band_of_ge x hx

end JSP314
