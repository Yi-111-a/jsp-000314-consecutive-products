import JSP314.PairSmooth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# JSP-000314 — the small-prime part of the near-pair count is polylog-small

This file bounds the contribution of the *small* primes `p ≤ Y` to the sum
`∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p` appearing in
`ShortResidual.badNonSingletonCount_le_nearPair_sum_add_const`.

## What is proved

* `nearPairCoveredCount_le_smoothUpTo` — every `n` counted by
  `nearPairCoveredCount x p` is a nonzero `(p+1)`-smooth number `≤ x`
  (`n = 0` is impossible: `m ≤ j + p` with `j = 0` forces `m ≤ p`,
  contradicting `p^2 ∣ m` and `1 < m`).  Hence
  `nearPairCoveredCount x p ≤ #(Nat.smoothNumbersUpTo x (p + 1))`.
* `smoothUpTo_card_le_log_pow` — the **exponent-vector bound**: a `k`-smooth
  `n ≤ N` is determined by the exponents `e_p = n.factorization p` for
  `p ∈ k.primesBelow`, each at most `Nat.log 2 N`, so
  `#(Nat.smoothNumbersUpTo N k) ≤ (Nat.log 2 N + 1) ^ #k.primesBelow`.
* `nearPair_smallp_sum_le` — summing over `p ∈ Nat.primesLE Y` and using
  monotonicity of smooth numbers in the smoothness parameter,
  `∑ p ∈ primesLE Y, nearPairCoveredCount x p ≤
    (Y + 1) * #(Nat.smoothNumbersUpTo x (Y + 1))`.
* `nearPair_smallp_sum_le_explicit` — the fully explicit version
  `∑ p ∈ primesLE Y, nearPairCoveredCount x p ≤
    (Y + 1) * (Nat.log 2 x + 1) ^ (Y + 1)`.
* `nearPair_smallp_sum_le_rpow_half_eventually` — **payoff**: for the cutoff
  `Y = Nat.log 2 (Nat.log 2 x)` the small-prime part is eventually
  `≤ x^{1/2}` (in fact `≤ 2^{⌊log₂ x⌋/2}`).

## Honest note on the `(log₂ x)²` cutoff

The naive extension of the last statement to `Y = (Nat.log 2 x)^2` is *not*
provable from these bounds, and for a good reason: the bound
`(Y+1)·(log₂x+1)^{Y+1}` with `Y = (log₂x)²` is `exp(Θ((log x)²·log log x))`,
which is *super*-polynomial, and even the true count
`Ψ(x, (log₂x)²) = x^{1/2 + o(1)}` of `(log²x)`-smooth numbers below `x`
slightly exceeds `x^{1/2}`.  Any subpower bound at that cutoff must therefore
exploit the extra near-pair structure, not just smoothness.  The explicit
bound `nearPair_smallp_sum_le_explicit` remains valid at every cutoff.
-/

namespace JSP314

open Classical

section SmoothUpperBound

/-- Every `n` counted by `nearPairCoveredCount x p` is a nonzero `(p+1)`-smooth
number `≤ x`, so `nearPairCoveredCount x p ≤ #(Nat.smoothNumbersUpTo x (p+1))`. -/
theorem nearPairCoveredCount_le_smoothUpTo (x p : ℕ) :
    nearPairCoveredCount x p ≤ (Nat.smoothNumbersUpTo x (p + 1)).card := by
  have hsub : (Finset.range (x + 1)).filter (fun n => nearPairCovered x n p) ⊆
      Nat.smoothNumbersUpTo x (p + 1) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, j, m, hpair, hncase, hjm1, hjm2, hm1, hmsq, hlpf, hm2x⟩ := hn
    have hpos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exfalso
        subst h0
        rcases hncase with hj | hj
        · -- `j = 0`: then `m ≤ p` while `p^2 ∣ m`, so `p^2 ≤ m ≤ p`, hence
          -- `p ≤ 1` and `m ≤ 1`, contradicting `1 < m`.
          have hmp : m ≤ p := by omega
          have hp2m : p ^ 2 ≤ m := Nat.le_of_dvd (by omega) hmsq
          have hp1 : p ≤ 1 := by nlinarith [hp2m.trans hmp]
          omega
        · omega
      · exact hpos
    have hlp : largestPrimeFactor n ≤ p := by
      rcases hncase with h | h
      · subst h; exact hpair.1
      · subst h; exact hpair.2
    rw [Nat.mem_smoothNumbersUpTo]
    exact ⟨Nat.lt_add_one_iff.mp hnx, mem_smoothNumbers_of_lpf_le hpos hlp⟩
  unfold nearPairCoveredCount
  exact Finset.card_le_card hsub

/-- **Exponent-vector bound.**  Inject `n ↦ (p ↦ n.factorization p)` from the
`k`-smooth numbers `≤ N` into `k.primesBelow → Finset.range (Nat.log 2 N + 1)`:
for a prime `p < k`, `p ^ (n.factorization p) ∣ n`, so
`2 ^ (n.factorization p) ≤ n ≤ N`, i.e. `n.factorization p ≤ Nat.log 2 N`;
injectivity on smooth numbers is unique factorization
(`Nat.eq_of_factorization_eq`), since every prime factor of a `k`-smooth
number lies in `k.primesBelow`. -/
theorem smoothUpTo_card_le_log_pow (N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤
      (Nat.log 2 N + 1) ^ k.primesBelow.card := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hempty : Nat.smoothNumbersUpTo 0 k = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro n hn
      rw [Nat.mem_smoothNumbersUpTo] at hn
      exact Nat.ne_zero_of_mem_smoothNumbers hn.2 (Nat.le_zero.mp hn.1)
    simp [hempty]
  have hN0 : N ≠ 0 := hN.ne'
  have key : (Nat.smoothNumbersUpTo N k).card ≤
      (k.primesBelow.pi fun _ => Finset.range (Nat.log 2 N + 1)).card := by
    refine Finset.card_le_card_of_injOn
      (fun n (p : ℕ) (_ : p ∈ k.primesBelow) => n.factorization p) ?_ ?_
    · -- MapsTo: each exponent is `< Nat.log 2 N + 1`.
      intro n hn
      obtain ⟨hnN, hnsm⟩ := Nat.mem_smoothNumbersUpTo.mp (Finset.mem_coe.mp hn)
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnsm
      rw [Finset.mem_coe, Finset.mem_pi]
      intro p hp
      obtain ⟨hpk, hpprime⟩ := Nat.mem_primesBelow.mp hp
      have hdvd : p ^ n.factorization p ∣ n :=
        (hpprime.pow_dvd_iff_le_factorization hn0).mpr le_rfl
      have hle : 2 ^ n.factorization p ≤ N :=
        ((Nat.pow_le_pow_left hpprime.two_le _).trans
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd)).trans hnN
      rw [Finset.mem_range, Nat.lt_succ_iff,
        Nat.le_log_iff_pow_le Nat.one_lt_two hN0]
      exact hle
    · -- InjOn: factorizations agree on `primesBelow k`, hence everywhere.
      intro n hn m hm h
      obtain ⟨hnN, hnsm⟩ := Nat.mem_smoothNumbersUpTo.mp (Finset.mem_coe.mp hn)
      obtain ⟨hmN, hmsm⟩ := Nat.mem_smoothNumbersUpTo.mp (Finset.mem_coe.mp hm)
      have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnsm
      have hm0 : m ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hmsm
      apply Nat.eq_of_factorization_eq hn0 hm0
      intro p
      by_cases hp : p ∈ k.primesBelow
      · exact congrFun (congrFun h p) hp
      · rw [Nat.mem_primesBelow] at hp
        push_neg at hp
        by_cases hpk : p < k
        · rw [Nat.factorization_eq_zero_of_not_prime _ (hp hpk),
            Nat.factorization_eq_zero_of_not_prime _ (hp hpk)]
        · by_cases hpp : p.Prime
          · have hnd : ¬ p ∣ n := fun hd => by
              have := Nat.mem_smoothNumbers'.mp hnsm p hpp hd; omega
            have hmd : ¬ p ∣ m := fun hd => by
              have := Nat.mem_smoothNumbers'.mp hmsm p hpp hd; omega
            rw [Nat.factorization_eq_zero_of_not_dvd hnd,
              Nat.factorization_eq_zero_of_not_dvd hmd]
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp,
              Nat.factorization_eq_zero_of_not_prime _ hpp]
  rw [Finset.card_pi] at key
  simp only [Finset.card_range, Finset.prod_const] at key
  exact key

/-- Weaker cruder form: `#k.primesBelow ≤ k`. -/
theorem smoothUpTo_card_le_log_pow' (N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤ (Nat.log 2 N + 1) ^ k := by
  refine (smoothUpTo_card_le_log_pow N k).trans
    (pow_le_pow_right' (by norm_num) ?_)
  rw [Nat.primesBelow_eq_filter_range]
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- `Nat.smoothNumbersUpTo` is monotone in the smoothness parameter. -/
theorem smoothNumbersUpTo_mono_right {N : ℕ} {k l : ℕ} (h : k ≤ l) :
    Nat.smoothNumbersUpTo N k ⊆ Nat.smoothNumbersUpTo N l := by
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1, Nat.smoothNumbers_mono h hn.2⟩

/-- **Small-prime part bound.**  Every `n` counted for a prime `p ≤ Y` is
`(Y+1)`-smooth, and there are at most `Y + 1` such primes. -/
theorem nearPair_smallp_sum_le (x Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, nearPairCoveredCount x p ≤
      (Y + 1) * (Nat.smoothNumbersUpTo x (Y + 1)).card := by
  calc ∑ p ∈ Nat.primesLE Y, nearPairCoveredCount x p
      ≤ ∑ _p ∈ Nat.primesLE Y, (Nat.smoothNumbersUpTo x (Y + 1)).card := by
        apply Finset.sum_le_sum
        intro p hp
        have hpY : p ≤ Y := Nat.le_of_mem_primesLE hp
        exact (nearPairCoveredCount_le_smoothUpTo x p).trans
          (Finset.card_le_card (smoothNumbersUpTo_mono_right (by omega)))
    _ = (Nat.primesLE Y).card * (Nat.smoothNumbersUpTo x (Y + 1)).card :=
        Finset.sum_const_nat fun _ _ => rfl
    _ ≤ (Y + 1) * (Nat.smoothNumbersUpTo x (Y + 1)).card :=
        Nat.mul_le_mul (primesLE_card_le Y) (le_refl _)

/-- **Fully explicit bound**: inserting the exponent-vector bound gives
`∑ p ∈ primesLE Y, nearPairCoveredCount x p ≤
  (Y + 1) * (Nat.log 2 x + 1) ^ (Y + 1)`. -/
theorem nearPair_smallp_sum_le_explicit (x Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, nearPairCoveredCount x p ≤
      (Y + 1) * (Nat.log 2 x + 1) ^ (Y + 1) := by
  refine (nearPair_smallp_sum_le x Y).trans ?_
  have hcard : (Y + 1).primesBelow.card ≤ Y + 1 := by
    rw [Nat.primesBelow_eq_filter_range]
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))
  have h1 : (Nat.smoothNumbersUpTo x (Y + 1)).card ≤
      (Nat.log 2 x + 1) ^ (Y + 1) :=
    (smoothUpTo_card_le_log_pow x (Y + 1)).trans
      (pow_le_pow_right' (by norm_num) hcard)
  exact Nat.mul_le_mul (le_refl _) h1

end SmoothUpperBound

section Payoff

/-- Auxiliary exponential domination: `2·(M+1)·(M+2) ≤ 2^M` for `M ≥ 10`. -/
theorem two_mul_succ_mul_le_pow {M : ℕ} (hM : 10 ≤ M) :
    2 * (M + 1) * (M + 2) ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) + 2 ≤ 2 * (k + 1) := by omega
    calc 2 * ((k + 1) + 1) * ((k + 1) + 2)
        = 2 * (k + 2) * (k + 3) := by ring
      _ ≤ (2 * (k + 2)) * (2 * (k + 1)) := Nat.mul_le_mul (le_refl _) h1
      _ = 2 * (2 * (k + 1) * (k + 2)) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul (le_refl _) ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- `n + 1 ≤ 2 ^ (n + 1)`. -/
theorem succ_le_two_pow_succ (n : ℕ) : n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    calc k + 1 + 1 ≤ 2 * (k + 1) := by omega
      _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul (le_refl _) ih
      _ = 2 ^ (k + 1 + 1) := by rw [pow_succ]; ring

/-- **Payoff (log–log cutoff).**  For `Y = Nat.log 2 (Nat.log 2 x)`, the
small-prime part of the near-pair sum is eventually at most `x^{1/2}`.
The chain is: the sum is `≤ (M+1)·(L+1)^{M+1}` where `L = log₂ x`,
`M = log₂ L`; then `L + 1 ≤ 2^{M+1}` and `M + 1 ≤ 2^{M+1}` give
`≤ 2^{(M+1)(M+2)} ≤ 2^{L/2} ≤ x^{1/2}` once `M ≥ 10`. -/
theorem nearPair_smallp_sum_le_rpow_half_eventually :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((∑ p ∈ Nat.primesLE (Nat.log 2 (Nat.log 2 x)),
          nearPairCoveredCount x p : ℕ) : ℝ) ≤ (x : ℝ) ^ (1/2 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 1024)] with x hx
  have hx0 : x ≠ 0 := by
    have h : 0 < x := lt_of_lt_of_le (by norm_num) hx
    omega
  set L := Nat.log 2 x with hLdef
  set M := Nat.log 2 L with hMdef
  have hL : 1024 ≤ L := (Nat.le_log_iff_pow_le Nat.one_lt_two hx0).mpr hx
  have hL0 : L ≠ 0 := by omega
  have hM : 10 ≤ M := by
    apply (Nat.le_log_iff_pow_le Nat.one_lt_two hL0).mpr
    calc (2:ℕ) ^ 10 = 1024 := by norm_num
      _ ≤ L := hL
  have hML : 2 ^ M ≤ L := Nat.pow_log_le_self 2 hL0
  have hbound : 2 * (M + 1) * (M + 2) ≤ 2 ^ M := two_mul_succ_mul_le_pow hM
  have hL1 : L + 1 ≤ 2 ^ (M + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two L
  have hM1 : M + 1 ≤ 2 ^ (M + 1) := succ_le_two_pow_succ M
  have hExp : (M + 1) * (M + 2) ≤ L / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    calc (M + 1) * (M + 2) * 2 = 2 * (M + 1) * (M + 2) := by ring
      _ ≤ 2 ^ M := hbound
      _ ≤ L := hML
  have hB : (M + 1) * (L + 1) ^ (M + 1) ≤ 2 ^ (L / 2) := by
    calc (M + 1) * (L + 1) ^ (M + 1)
        ≤ 2 ^ (M + 1) * (2 ^ (M + 1)) ^ (M + 1) :=
          Nat.mul_le_mul hM1 (Nat.pow_le_pow_left hL1 _)
      _ = 2 ^ ((M + 1) * (M + 2)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right (by norm_num) hExp
  have hsum : ∑ p ∈ Nat.primesLE M, nearPairCoveredCount x p ≤
      (M + 1) * (L + 1) ^ (M + 1) := nearPair_smallp_sum_le_explicit x M
  have hcast : ((∑ p ∈ Nat.primesLE M, nearPairCoveredCount x p : ℕ) : ℝ) ≤
      ((2 ^ (L / 2) : ℕ) : ℝ) := by
    exact_mod_cast hsum.trans hB
  refine hcast.trans ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  have h2L : ((2 ^ L : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hx0
  have hhalf : ((L / 2 : ℕ) : ℝ) ≤ (L : ℝ) / 2 := Nat.cast_div_le
  calc (2 : ℝ) ^ ((L / 2 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((L : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalf
    _ = ((2 : ℝ) ^ (L : ℝ)) ^ (1/2 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
    _ = (((2 ^ L : ℕ) : ℝ)) ^ (1/2 : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (x : ℝ) ^ (1/2 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h2L (by norm_num)

end Payoff

end JSP314
