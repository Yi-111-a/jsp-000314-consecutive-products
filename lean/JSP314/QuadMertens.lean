import JSP314.QuadRegime
import Mathlib.NumberTheory.Chebyshev

/-!
# A weak explicit Mertens bound over primes

This file proves the elementary explicit bound

  `∑_{p ∈ primesLE k} (log p)/(p - 1) ≤ 2·log k + 11`,

a "Mertens-type" prime sum needed for the Erdős–Graham/Ta26c
quadratic-regime analysis, together with the glue connecting it to the
master inequality of `JSP314.QuadRegime`.

## What is proved

* `log_factorial_eq_sum_vonMangoldt_mul_div`: Legendre's identity in
  logarithmic form, `log k! = ∑_{d ≤ k} Λ(d)·⌊k/d⌋`.
* `sum_vonMangoldt_div_le_log_add_psi`:
  `∑_{d ≤ k} Λ(d)/d ≤ log k + ψ(k)/k` (since `⌊k/d⌋ ≥ k/d - 1`).
* `sum_log_div_pred_primesLE_le`:
  `∑_{p ≤ k} (log p)/(p-1) ≤ 2·log k + 11`, from
  `(log p)/(p-1) ≤ 2·(log p)/p`, the bound `Λ p = log p` on primes, and
  Mathlib's `Chebyshev.psi_le_const_mul_self` (`ψ k ≤ (log 4 + 4)·k`).
* `quadRegimeOpen_of_mertens`: the conditional quadratic-regime theorem —
  given any bound `B k` on the prime sum together with the strict gap
  `π(k)·log n + k·B k < k·log(n + 1 - k)`, the Sylvester–Schur conclusion
  follows.

## Honest caveat

With `B = 2·log k + 11` the gap hypothesis `hgap` is **not** satisfied in
the quadratic regime (both sides have leading term `2k·log k`, with the
wrong sign on the `π(k)·log n` term).  This matches the classical
analysis: the product-of-consecutive-integers bound
`v_p(∏_{m=n-k+1}^{n} m) ≤ k/(p-1) + log_p n` loses the full `k!`
contribution, so the regime `n ≈ k²` genuinely needs Erdős's sharper
*choose-side* estimate `∑_{p≤k} ⌊log_p n⌋·log p = θ(k) + (ψ(n) - θ(n))`,
whose residual is captured by `SylvesterSchur.quadRegimeOpen_of_smooth_prod_lt`
in `JSP314.QuadRegime`.

No placeholder tactics; kernel-checkable.
-/

namespace SylvesterSchur

open Finset ArithmeticFunction
open scoped Nat

/-- **Legendre's identity**, logarithmic form:
`log k! = ∑_{d=1}^{k} Λ(d)·⌊k/d⌋`, where the inner double count is
`#{m ≤ k : d ∣ m} = k / d`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (k : ℕ) :
    Real.log (k !) = ∑ d ∈ Icc 1 k, Λ d * ((k / d : ℕ) : ℝ) := by
  have hfact : (k ! : ℝ) = ∏ m ∈ Icc 1 k, (m : ℝ) := by
    rw [Nat.cast_prod]
    congr 1
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
      Nat.add_sub_cancel,
      show ∏ i ∈ range k, (1 + i) = ∏ i ∈ range k, (i + 1) from
        Finset.prod_congr rfl fun i _ ↦ add_comm 1 i]
    exact (Finset.prod_range_add_one_eq_factorial k).symm
  have hdiv : ∀ m ∈ Icc 1 k, m.divisors = (Icc 1 k).filter (fun d ↦ d ∣ m) := by
    intro m hm
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    constructor
    · rintro ⟨hdvd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        (Nat.le_of_dvd (by omega) hdvd).trans hm2⟩, hdvd⟩
    · rintro ⟨⟨-, -⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  have hsum : (∑ m ∈ Icc 1 k, Real.log m)
      = ∑ m ∈ Icc 1 k, ∑ d ∈ m.divisors, (Λ d : ℝ) :=
    Finset.sum_congr rfl fun m _ ↦ vonMangoldt_sum.symm
  rw [hfact, Real.log_prod fun m hm ↦ by
        rw [Nat.cast_ne_zero]; exact (Finset.mem_Icc.mp hm).1.ne',
    hsum]
  calc ∑ m ∈ Icc 1 k, ∑ d ∈ m.divisors, (Λ d : ℝ)
      = ∑ m ∈ Icc 1 k, ∑ d ∈ Icc 1 k, (if d ∣ m then Λ d else 0) := by
        refine Finset.sum_congr rfl fun m hm ↦ ?_
        rw [hdiv m hm, Finset.sum_filter]
    _ = ∑ d ∈ Icc 1 k, ∑ m ∈ Icc 1 k, (if d ∣ m then Λ d else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Icc 1 k, ∑ _m ∈ (Icc 1 k).filter (d ∣ ·), Λ d := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        rw [← Finset.sum_filter]
    _ = ∑ d ∈ Icc 1 k, Λ d * ((k / d : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        have hcard : #((Icc 1 k).filter (d ∣ ·)) = k / d := by
          have hIcc : Icc (1 : ℕ) k = Ioc 0 k := by
            ext x; simp only [mem_Icc, mem_Ioc]; omega
          rw [hIcc]
          exact Nat.Ioc_filter_dvd_card_eq_div k d
        rw [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-- `∑_{d=1}^{k} Λ(d)/d ≤ log k + ψ(k)/k`. -/
theorem sum_vonMangoldt_div_le_log_add_psi {k : ℕ} (hk : 1 ≤ k) :
    (∑ d ∈ Icc 1 k, Λ d / (d : ℝ)) ≤ Real.log k + Chebyshev.psi k / k := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hfl : ∀ d ∈ Icc 1 k, (k : ℝ) / d - 1 ≤ ((k / d : ℕ) : ℝ) := by
    intro d hd
    rw [sub_le_iff_le_add]
    have h := Nat.lt_floor_add_one ((k : ℝ) / (d : ℝ))
    rwa [Nat.floor_div_eq_div] at h
  have hexp : ∑ d ∈ Icc 1 k, Λ d * ((k : ℝ) / d - 1)
      = k * ∑ d ∈ Icc 1 k, Λ d / d - ∑ d ∈ Icc 1 k, Λ d := by
    rw [← Finset.sum_sub_distrib, ← Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.mem_Icc.mp hd).1.ne'
    field_simp
    ring
  have hpsi : Chebyshev.psi (k : ℝ) = ∑ d ∈ Icc 1 k, Λ d := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc (zero_le 1) le_rfl)
    intro x hx hnx
    simp only [mem_Icc] at hx hnx
    have : x = 0 := by omega
    simp [this, ArithmeticFunction.vonMangoldt_apply]
  have hstep : ∑ d ∈ Icc 1 k, Λ d * ((k : ℝ) / d - 1) ≤ Real.log (k !) := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div]
    exact Finset.sum_le_sum fun d hd ↦
      mul_le_mul_of_nonneg_left (hfl d hd) ArithmeticFunction.vonMangoldt_nonneg
  have hlogfact : Real.log (k ! : ℝ) ≤ k * Real.log k := by
    have hf : (k ! : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    calc Real.log (k !) ≤ Real.log ((k : ℝ) ^ k) :=
          Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos k)) hf
      _ = k * Real.log k := Real.log_pow
  rw [hexp, hpsi] at hstep
  have key := hstep.trans hlogfact
  rw [div_le_iff₀ hkR, add_mul, div_mul_cancel₀ _ hkR.ne']
  -- goal: `(∑ Λ/d)·k ≤ log k·k + ψ k`; key: `k·∑ Λ/d - ψ k ≤ k·log k`
  nlinarith [mul_comm (∑ d ∈ Icc 1 k, Λ d / (d : ℝ)) (k : ℝ),
    mul_comm (Real.log k) (k : ℝ)]

/-- **Weak explicit Mertens bound**:
`∑_{p ≤ k} (log p)/(p - 1) ≤ 2·log k + 11`. -/
theorem sum_log_div_pred_primesLE_le {k : ℕ} (hk : 1 ≤ k) :
    (∑ p ∈ k.primesLE, Real.log p / ((p - 1 : ℕ) : ℝ)) ≤ 2 * Real.log k + 11 := by
  have h1 : ∑ p ∈ k.primesLE, Real.log p / ((p - 1 : ℕ) : ℝ)
      ≤ 2 * ∑ p ∈ k.primesLE, Real.log p / (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp ↦ ?_
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hpp.two_le
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hp1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_pos]; omega
    rw [div_le_div_iff₀ hp1 (by linarith : (0 : ℝ) < p)]
    have hpp1 : ((p - 1 : ℕ) : ℝ) = p - 1 := by
      rw [← Nat.cast_one, ← Nat.cast_sub hpp.one_le]
    rw [hpp1]
    nlinarith [mul_nonneg hlogp (sub_nonneg.mpr hp2)]
  have hsub : k.primesLE ⊆ Icc 1 k := by
    intro p hp
    obtain ⟨hpk, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.one_le, hpk⟩
  have heq : ∑ p ∈ k.primesLE, Real.log p / (p : ℝ)
      = ∑ p ∈ k.primesLE, Λ p / (p : ℝ) := by
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.mem_primesLE.mp hp).2]
  have h2 : ∑ p ∈ k.primesLE, Real.log p / (p : ℝ)
      ≤ ∑ d ∈ Icc 1 k, Λ d / (d : ℝ) := by
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ ↦
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have h3 : ∑ d ∈ Icc 1 k, Λ d / (d : ℝ) ≤ Real.log k + (Real.log 4 + 4) := by
    refine (sum_vonMangoldt_div_le_log_add_psi hk).trans ?_
    have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hdiv : Chebyshev.psi k / k ≤ Real.log 4 + 4 := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr hk), div_mul_cancel₀ _ (Nat.cast_pos.mpr hk).ne']
      exact hpsi
    linarith
  have h2log : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    simp
  have hlog2 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
  linarith [h1, h2.trans h3]

/-- **Conditional quadratic regime via a Mertens-type bound.**
If `B k` bounds `∑_{p≤k} (log p)/(p-1)` for `k ≥ 38` and the strict gap
`π(k)·log n + k·B k < k·log(n + 1 - k)` holds on `QuadRegimeOpen`, then
`C(n,k)` has a prime divisor `> k` there — discharging `hquad` in
`SylvesterSchur.exists_prime_dvd_choose`. -/
theorem quadRegimeOpen_of_mertens
    (B : ℕ → ℝ)
    (hmertens : ∀ k : ℕ, 38 ≤ k →
      ∑ p ∈ k.primesLE, Real.log p / ((p - 1 : ℕ) : ℝ) ≤ B k)
    (hgap : ∀ n' k' : ℕ, QuadRegimeOpen n' k' →
      (k'.primeCounting : ℝ) * Real.log n' + k' * B k'
        < k' * Real.log (n' + 1 - k' : ℕ))
    {n k : ℕ} (hq : QuadRegimeOpen n k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k :=
    fun q hq2 hqd ↦ le_of_not_gt fun h2 ↦ hcon q hq2 h2 hqd
  have hmaster := log_consecutive_prod_le (by have := hq.1; omega)
    (by have := hq.2.1; omega) hall
  have hb := hmertens k hq.1
  have hg := hgap n k hq
  have hsum : k.primeCounting * Real.log n +
        (k : ℝ) * ∑ p ∈ k.primesLE, Real.log p / ((p - 1 : ℕ) : ℝ)
      ≤ k.primeCounting * Real.log n + k * B k :=
    add_le_add_left (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)) _
  linarith [hmaster.trans hsum]

end SylvesterSchur
