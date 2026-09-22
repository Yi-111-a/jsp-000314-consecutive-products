import JSP314.SylvesterSchur
import Mathlib.NumberTheory.Chebyshev

/-!
# The quadratic regime: valuation bounds and conditional reductions

This file develops the analytic infrastructure for the remaining
"quadratic regime" `38 ≤ k`, `2k + 2 ≤ n ≤ k²` of the Sylvester–Schur
theorem (see `QuadRegimeOpen` in `JSP314.SylvesterSchur`).

## What is proved

* `factorization_descFactorial_le`: for a prime `p`, the `p`-adic
  valuation of the product `n.descFactorial k = (n - k + 1) ⋯ n` of `k`
  consecutive integers satisfies the Erdős-style bound
  `v_p ≤ k / (p - 1) + ⌊log_p n⌋` (Legendre's formula plus the geometric
  series bound `∑_{i≥1} k / p^i ≤ k / (p - 1)`).
* `prod_Icc_consecutive_eq_descFactorial`,
  `factorization_prod_Icc_le`: the same bound stated for
  `∏ m ∈ Finset.Icc (n + 1 - k) n, m`.
* `descFactorial_le_pow_primeCounting_mul`: if every prime divisor of
  `C(n,k)` is `≤ k`, then
  `∏_{m=n-k+1}^{n} m ≤ n^{π k} · ∏_{p ≤ k} p^{k / (p - 1)}`.
* `pow_le_descFactorial`: the lower bound `(n + 1 - k)^k ≤ n.descFactorial k`.
* `log_consecutive_prod_le`: the real-valued master inequality obtained
  by taking logarithms,
  `k·log(n+1-k) ≤ π(k)·log n + k·∑_{p≤k} log p / (p - 1)`.
* `exists_prime_dvd_choose_of_prod_lt`: the conditional
  Sylvester–Schur conclusion — a strict inequality refuting the master
  bound immediately yields a prime `> k` dividing `C(n,k)`.
* `four_pow_mul_pow_le`: the binomial lower bound
  `4^k·n^k ≤ (2k+1)·(2k)^k·C(n,k)` for `2k ≤ n`.
* `exists_prime_dvd_choose_of_smooth_prod_lt`,
  `quadRegimeOpen_of_smooth_prod_lt`: the sharper *choose-side* skeleton —
  if `(2k+1)·(2k)^k·∏_{p≤k} p^{⌊log_p n⌋} < 4^k·n^k` then the conclusion
  holds.  This is the residual estimate that Erdős discharges via his
  iterated primorial bound `∏_j θ(n^{1/j}) ≤ 4^{k + O(√n)}`; proving it
  for all `n ≤ k²` is the one genuinely missing analytic ingredient (see
  the closing comments of `SylvesterSchur.lean`).

All proofs are kernel-checkable; no placeholder tactics used.
-/

namespace SylvesterSchur

open Finset
open scoped Nat

/-- **Erdős's valuation bound.**  For a prime `p`, the `p`-adic valuation
of the product `n.descFactorial k = (n - k + 1) ⋯ n` of `k` consecutive
integers is at most `k / (p - 1) + ⌊log_p n⌋`.

Proof: `descFactorial n k = n! / (n - k)!`, so Legendre's formula gives
`v_p = ∑_{i=1}^{B} (⌊n/p^i⌋ - ⌊(n-k)/p^i⌋)` with `B = ⌊log_p n⌋ + 1`.
Each summand is `≤ k / p^i + 1`, the geometric sum is `≤ k / (p - 1)`
(`Nat.geom_sum_Ico_le`), and `B - 1 = ⌊log_p n⌋`. -/
theorem factorization_descFactorial_le {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    (n.descFactorial k).factorization p ≤ k / (p - 1) + p.log n := by
  have hpos : n.descFactorial k ≠ 0 := (Nat.descFactorial_pos.mpr hkn).ne'
  -- `v_p(descFactorial) = v_p(n!) - v_p((n-k)!)` from `(n-k)! * descFactorial = n!`.
  have hfact : (n.descFactorial k).factorization p =
      (n !).factorization p - ((n - k) !).factorization p := by
    have h := Nat.factorization_mul (Nat.factorial_ne_zero (n - k)) hpos
    rw [Nat.factorial_mul_descFactorial hkn] at h
    have happ := congrArg (· p) h
    simp only [Finsupp.coe_add, Pi.add_apply] at happ
    omega
  have hB : Nat.log p (n - k) < Nat.log p n + 1 :=
    lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le n k)) (Nat.lt_succ_self _)
  rw [hfact, Nat.factorization_factorial hp (Nat.lt_succ_self _),
    Nat.factorization_factorial hp hB,
    ← Finset.sum_tsub_distrib _ fun i _ ↦ Nat.div_le_div_right (Nat.sub_le n k)]
  calc ∑ i ∈ Ico 1 (p.log n + 1), (n / p ^ i - (n - k) / p ^ i)
      ≤ ∑ i ∈ Ico 1 (p.log n + 1), (k / p ^ i + 1) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have h := Nat.add_div_le_div_add_div_add_one (n - k) k (p ^ i)
        rw [Nat.sub_add_cancel hkn] at h
        rw [tsub_le_iff_right,
          Nat.add_comm (k / p ^ i + 1) ((n - k) / p ^ i), ← Nat.add_assoc]
        exact h
    _ = ∑ i ∈ Ico 1 (p.log n + 1), k / p ^ i + p.log n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico]
        simp
    _ ≤ k / (p - 1) + p.log n :=
        Nat.add_le_add_right (Nat.geom_sum_Ico_le hp.two_le k _) _

/-- The product of `k` consecutive integers ending at `n` equals
`n.descFactorial k`. -/
theorem prod_Icc_consecutive_eq_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    ∏ m ∈ Finset.Icc (n + 1 - k) n, m = n.descFactorial k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range,
    Nat.descFactorial_eq_prod_range]
  have hr : n + 1 - (n + 1 - k) = k := by omega
  rw [hr, ← Finset.prod_range_reflect (fun i ↦ n + 1 - k + i) k]
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  have := Finset.mem_range.mp hj
  omega

/-- The valuation bound stated directly for the interval product
`∏_{m = n - k + 1}^{n} m`. -/
theorem factorization_prod_Icc_le {n k p : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    (∏ m ∈ Finset.Icc (n + 1 - k) n, m).factorization p ≤
      k / (p - 1) + p.log n := by
  rw [prod_Icc_consecutive_eq_descFactorial hkn]
  exact factorization_descFactorial_le hp hkn

/-- **Master product bound.**  If every prime divisor of `C(n,k)` is at
most `k`, then the product of the `k` consecutive integers `(n-k+1) ⋯ n`
is at most `n^{π k} · ∏_{p ≤ k} p^{k/(p-1)}`: each prime factor of the
product is `≤ k` (it divides `k! · C(n,k)`), its exponent is bounded by
`factorization_descFactorial_le`, and `∏_{p≤k} p^{⌊log_p n⌋} ≤ n^{π k}`. -/
theorem descFactorial_le_pow_primeCounting_mul {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k) :
    n.descFactorial k ≤
      n ^ k.primeCounting * ∏ p ∈ k.primesLE, p ^ (k / (p - 1)) := by
  have hpos : n.descFactorial k ≠ 0 := (Nat.descFactorial_pos.mpr hkn).ne'
  have hn : n ≠ 0 := by omega
  have hsub : (n.descFactorial k).primeFactors ⊆ k.primesLE := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hpdvd, -⟩ := hp
    rw [Nat.mem_primesLE]
    refine ⟨?_, hpp⟩
    have hdvd : p ∣ k ! * n.choose k := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]
      exact hpdvd
    rcases hpp.dvd_mul.mp hdvd with hpk | hpc
    · exact (hpp.dvd_factorial).mp hpk
    · exact h p hpp hpc
  have hπ : ∏ p ∈ k.primesLE, p ^ (p.log n) ≤ n ^ k.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Finset.prod_const]
    exact Finset.prod_le_prod fun p hp ↦ Nat.pow_log_le_self p hn
  calc n.descFactorial k
      = ∏ p ∈ (n.descFactorial k).primeFactors,
          p ^ (n.descFactorial k).factorization p := by
        conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
        rw [Nat.prod_factorization_eq_prod_primeFactors]
    _ ≤ ∏ p ∈ k.primesLE, p ^ (n.descFactorial k).factorization p :=
        Finset.prod_le_prod_of_subset_of_one_le hsub
          fun p hp _ ↦ Nat.one_le_pow _ _ (Nat.mem_primesLE.mp hp).2.pos
    _ ≤ ∏ p ∈ k.primesLE, (p ^ (k / (p - 1)) * p ^ (p.log n)) := by
        refine Finset.prod_le_prod fun p hp ↦ ?_
        have hpp := (Nat.mem_primesLE.mp hp).2
        rw [← pow_add]
        exact Nat.pow_le_pow_right hpp.pos
          (factorization_descFactorial_le hpp hkn)
    _ = (∏ p ∈ k.primesLE, p ^ (k / (p - 1))) * ∏ p ∈ k.primesLE, p ^ (p.log n) :=
        Finset.prod_mul_distrib
    _ = (∏ p ∈ k.primesLE, p ^ (p.log n)) * ∏ p ∈ k.primesLE, p ^ (k / (p - 1)) :=
        Nat.mul_comm _ _
    _ ≤ n ^ k.primeCounting * ∏ p ∈ k.primesLE, p ^ (k / (p - 1)) :=
        Nat.mul_le_mul_right _ hπ

/-- Each of the `k` consecutive factors `n - i` (`i < k`) is at least
`n + 1 - k`. -/
theorem pow_le_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    (n + 1 - k) ^ k ≤ n.descFactorial k := by
  calc (n + 1 - k) ^ k = ∏ _i ∈ range k, (n + 1 - k) := by
        rw [Finset.prod_const, card_range]
    _ ≤ ∏ i ∈ range k, (n - i) := by
        refine Finset.prod_le_prod fun i hi ↦ ?_
        have hi' := Finset.mem_range.mp hi
        omega
    _ = n.descFactorial k := (Nat.descFactorial_eq_prod_range n k).symm

/-- **Conditional Sylvester–Schur, product form.**  If the master bound
is strict in the direction `(n + 1 - k)^k > n^{π k}·∏_{p≤k} p^{k/(p-1)}`,
then `C(n,k)` has a prime divisor `> k`. -/
theorem exists_prime_dvd_choose_of_prod_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hlt : n ^ k.primeCounting * ∏ p ∈ k.primesLE, p ^ (k / (p - 1))
        < (n + 1 - k) ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k :=
    fun q hq hqd ↦ le_of_not_gt fun h2 ↦ hcon q hq h2 hqd
  have hle := (pow_le_descFactorial hkn).trans
    (descFactorial_le_pow_primeCounting_mul hk hkn hall)
  exact absurd hlt (not_lt_of_ge hle)

/-- **Binomial lower bound.**  For `2k ≤ n`,
`4^k · n^k ≤ (2k+1)·(2k)^k·C(n,k)`, combining `4^k ≤ (2k+1)·C(2k,k)`
(Mathlib's `four_pow_le_two_mul_add_one_mul_centralBinom`) with
`n^k·C(2k,k) ≤ (2k)^k·C(n,k)`, which is the termwise inequality
`n·(2k - i) ≤ 2k·(n - i)` over `i < k`. -/
theorem four_pow_mul_pow_le {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    4 ^ k * n ^ k ≤ (2 * k + 1) * (2 * k) ^ k * n.choose k := by
  have hprod : n ^ k * (2 * k).descFactorial k ≤ (2 * k) ^ k * n.descFactorial k := by
    have e1 : n ^ k = ∏ _i ∈ range k, n := by rw [Finset.prod_const, card_range]
    have e2 : (2 * k) ^ k = ∏ _i ∈ range k, (2 * k) := by
      rw [Finset.prod_const, card_range]
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, e1, e2,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod fun i hi ↦ ?_
    have hi' := Finset.mem_range.mp hi
    rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, mul_comm n (2 * k)]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right i hkn) _
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at hprod
  have h2 : n ^ k * (2 * k).choose k ≤ (2 * k) ^ k * n.choose k := by
    apply Nat.le_of_mul_le_mul_left _ (Nat.factorial_pos k)
    convert hprod using 1 <;> ring
  have h4 : 4 ^ k ≤ (2 * k + 1) * (2 * k).choose k := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
  calc 4 ^ k * n ^ k ≤ ((2 * k + 1) * (2 * k).choose k) * n ^ k :=
        Nat.mul_le_mul_right _ h4
    _ = (2 * k + 1) * (n ^ k * (2 * k).choose k) := by ring
    _ ≤ (2 * k + 1) * ((2 * k) ^ k * n.choose k) := Nat.mul_le_mul_left _ h2
    _ = (2 * k + 1) * (2 * k) ^ k * n.choose k := by ring

/-- **Conditional Sylvester–Schur, choose form.**  If the smooth product
`∏_{p≤k} p^{⌊log_p n⌋}` (the upper bound for `C(n,k)` when all its prime
factors are `≤ k`) satisfies the strict inequality
`(2k+1)·(2k)^k·∏_{p≤k} p^{⌊log_p n⌋} < 4^k·n^k`, then `C(n,k)` has a
prime divisor `> k`. -/
theorem exists_prime_dvd_choose_of_smooth_prod_lt {n k : ℕ} (hk : 1 ≤ k)
    (hkn : 2 * k ≤ n)
    (hlt : (2 * k + 1) * (2 * k) ^ k * ∏ p ∈ k.primesLE, p ^ (p.log n)
        < 4 ^ k * n ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k :=
    fun q hq hqd ↦ le_of_not_gt fun h2 ↦ hcon q hq h2 hqd
  have hc := choose_le_prod_pow_log (show k ≤ n by omega) hall
  have hlb := four_pow_mul_pow_le hk hkn
  exact absurd ((hlb.trans (Nat.mul_le_mul_left _ hc)).trans_lt hlt) (lt_irrefl _)

/-- The packaged reduction: the quadratic regime `QuadRegimeOpen` follows
from the strict smooth-product inequality on that regime.  This is the
residual estimate for which Erdős develops his iterated primorial bound
`∏_j θ(n^{1/j}) ≤ 4^{k + O(√n)}` and the finite verification
`n ≤ 2304`. -/
theorem quadRegimeOpen_of_smooth_prod_lt
    (h : ∀ n' k' : ℕ, QuadRegimeOpen n' k' →
      (2 * k' + 1) * (2 * k') ^ k' * ∏ p ∈ k'.primesLE, p ^ (p.log n')
        < 4 ^ k' * n' ^ k')
    {n k : ℕ} (hq : QuadRegimeOpen n k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  exact exists_prime_dvd_choose_of_smooth_prod_lt (by have := hq.1; omega)
    (by have := hq.2.1; omega) (h n k hq)

/-- **Real-valued master inequality.**  Taking logarithms of
`descFactorial_le_pow_primeCounting_mul`: if every prime divisor of
`C(n,k)` is `≤ k`, then
`k·log(n+1-k) ≤ π(k)·log n + k·∑_{p≤k} (log p)/(p-1)`.  Combined with an
explicit Mertens bound `∑_{p≤k} (log p)/(p-1) ≤ 2·log k + C`
(`QuadMertens.sum_log_div_pred_primesLE_le`), any strict refutation
gives the Sylvester–Schur conclusion (`quadRegimeOpen_of_mertens` in
`JSP314.QuadMertens`). -/
theorem log_consecutive_prod_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k) :
    (k : ℝ) * Real.log (n + 1 - k : ℕ) ≤
      k.primeCounting * Real.log n +
        (k : ℝ) * ∑ p ∈ k.primesLE, Real.log p / (p - 1 : ℕ) := by
  have hprod := (pow_le_descFactorial hkn).trans
    (descFactorial_le_pow_primeCounting_mul hk hkn h)
  have hn1 : (1 : ℝ) ≤ (n + 1 - k : ℕ) := by
    rw [Nat.one_le_cast]; omega
  have hR : ((n + 1 - k : ℕ) : ℝ) ^ k ≤
      (n : ℝ) ^ k.primeCounting *
        ∏ p ∈ k.primesLE, (p : ℝ) ^ (k / (p - 1)) := by
    exact_mod_cast hprod
  have hlog := Real.log_le_log (pow_pos (by positivity) k) hR
  rw [Real.log_pow, Real.log_mul
      (pow_ne_zero _ (Nat.cast_pos.mpr (by omega : 1 ≤ n)).ne')
      (Finset.prod_ne_zero_iff.mpr fun p hp ↦
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primesLE.mp hp).2.pos.ne')),
    Real.log_pow,
    Real.log_prod fun p hp ↦
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mem_primesLE.mp hp).2.pos.ne')] at hlog
  have hterm : ∀ p ∈ k.primesLE,
      Real.log ((p : ℝ) ^ (k / (p - 1))) ≤
        (k : ℝ) * Real.log p / ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    rw [Real.log_pow, ← div_mul_eq_mul_div]
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hlogp : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (Nat.one_le_cast.mpr hpp.one_lt.le)
    exact mul_le_mul_of_nonneg_right Nat.cast_div_le hlogp
  calc (k : ℝ) * Real.log (n + 1 - k : ℕ)
      ≤ k.primeCounting * Real.log n +
          ∑ p ∈ k.primesLE, Real.log ((p : ℝ) ^ (k / (p - 1))) := hlog
    _ ≤ k.primeCounting * Real.log n +
          ∑ p ∈ k.primesLE, (k : ℝ) * Real.log p / ((p - 1 : ℕ) : ℝ) :=
        add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ = k.primeCounting * Real.log n +
          (k : ℝ) * ∑ p ∈ k.primesLE, Real.log p / ((p - 1 : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun p _ ↦ mul_div_assoc _ _ _

end SylvesterSchur
