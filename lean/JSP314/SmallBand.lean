import JSP314.RunDecomp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# JSP-000314 — small-prime band of `runCountSum` is polylog-small

This file bounds the *small band* of the run-count double sum from
`BandSum.runCountSum` (defined there; note `BandSum`/`SmoothUB` are currently
broken in this checkout — `SmoothUB` imports the nonexistent
`Mathlib.Analysis.SpecialFunctions.Pow.Nat` — so the needed lemmas
`smoothUpTo_card_le_log_pow` and `smoothNumbersUpTo_mono_right` are
**reproved here**, unchanged, as `smoothUpTo_card_le_log2_pow` and
`smoothNumbersUpTo_mono_right'`):

`∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2*p), (rightRunCount x p k + leftRunCount x p k)`

For a cutoff `Z`, the observation is that a run witness `m` already forces a
single `p`-smooth neighbour: for `k ≥ 1`, `m + 1 ∈ Icc (m+1) (m+k)` is
`p`-smooth (right runs) and `m - 1 ∈ Icc (m-k) (m-1)` is `p`-smooth (left
runs).  So `rightRunCount x p k ≤ #(Nat.smoothNumbersUpTo (2x+1) (p+1))` via
the injection `m ↦ m + 1`, and for `p ≥ 2` (which forces `m ≥ 2` since
`largestPrimeFactor m = p`)
`leftRunCount x p k ≤ #(Nat.smoothNumbersUpTo (2x) (p+1))` via `m ↦ m - 1`.

Applying the exponent-vector bound and summing over `p ≤ Z`, `k ≤ 2p`:

`smallBand ≤ (Z + 1) * (4 * Z) * (Nat.log 2 (2x+1) + 1)^(Z+1)`.

With the log–log cutoff `Z = Nat.log 2 (Nat.log 2 x)` this is eventually
`≤ x^{1/2}` (`smallBand_runSum_le_rpow_half_eventually`), matching the
`SmoothUB` payoff.  (A `z`-scale cutoff `Z ~ exp(c·√(log x · log log x))` is
*not* reachable from the exponent-vector bound, which at that cutoff is
`exp(exp(Θ(√(L·L₂)))·log L)` — super-polynomial.  The cutoff here is limited
to `Z = o(log x / log log x)`; `log₂ log₂ x` is the convenient choice.)
-/

namespace JSP314

open Classical Filter

section SmoothBoundCopy

/-- **Exponent-vector bound** (copy of `SmoothUB.smoothUpTo_card_le_log_pow`,
inlined because `JSP314.SmoothUB` does not compile in this checkout).
Inject `n ↦ (p ↦ n.factorization p)` from the `k`-smooth numbers `≤ N` into
`k.primesBelow → Finset.range (Nat.log 2 N + 1)`: for a prime `p < k`,
`p ^ (n.factorization p) ∣ n`, so `2 ^ (n.factorization p) ≤ n ≤ N`, i.e.
`n.factorization p ≤ Nat.log 2 N`; injectivity on smooth numbers is unique
factorization (`Nat.eq_of_factorization_eq`). -/
theorem smoothUpTo_card_le_log2_pow (N k : ℕ) :
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

/-- `Nat.smoothNumbersUpTo` is monotone in the smoothness parameter
(copy of `SmoothUB.smoothNumbersUpTo_mono_right`). -/
theorem smoothNumbersUpTo_mono_right' {N : ℕ} {k l : ℕ} (h : k ≤ l) :
    Nat.smoothNumbersUpTo N k ⊆ Nat.smoothNumbersUpTo N l := by
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1, Nat.smoothNumbers_mono h hn.2⟩

end SmoothBoundCopy

section WitnessBounds

/-- **Right runs.** For `k ≥ 1`, `m ↦ m + 1` injects `rightRunWitness x p k`
into the `(p+1)`-smooth numbers `≤ 2x + 1`. -/
theorem rightRunCount_le_smoothUpTo {x p k : ℕ} (hk : 1 ≤ k) :
    rightRunCount x p k ≤ (Nat.smoothNumbersUpTo (2 * x + 1) (p + 1)).card := by
  refine Finset.card_le_card_of_injOn (fun m => m + 1) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, _, _, hsmooth⟩ := hm
    have hmem : m + 1 ∈ Finset.Icc (m + 1) (m + k) := by
      rw [Finset.mem_Icc]; omega
    have hlpf := hsmooth (m + 1) hmem
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo]
    exact ⟨by omega, mem_smoothNumbers_of_lpf_le (by omega) hlpf⟩
  · intro a _ b _ h
    exact Nat.add_right_cancel h

/-- **Left runs.** For `k ≥ 1` and `p ≥ 2`, `m ↦ m - 1` injects
`leftRunWitness x p k` into the `(p+1)`-smooth numbers `≤ 2x`
(the hypothesis `p ≥ 2` forces `m ≥ 2`, since `largestPrimeFactor m = 1` for
`m ≤ 1`). -/
theorem leftRunCount_le_smoothUpTo {x p k : ℕ} (hk : 1 ≤ k) (hp : 2 ≤ p) :
    leftRunCount x p k ≤ (Nat.smoothNumbersUpTo (2 * x) (p + 1)).card := by
  have hm2 : ∀ m ∈ leftRunWitness x p k, 2 ≤ m := by
    intro m hm
    rw [mem_leftRunWitness] at hm
    rcases Nat.le_or_lt m 1 with h | h
    · rw [largestPrimeFactor_eq_one_iff.mpr h] at hm
      omega
    · omega
  refine Finset.card_le_card_of_injOn (fun m => m - 1) ?_ ?_
  · intro m hm
    have hm2' := hm2 m (Finset.mem_coe.mp hm)
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, _, _, hsmooth⟩ := hm
    have hmem : m - 1 ∈ Finset.Icc (m - k) (m - 1) := by
      rw [Finset.mem_Icc]; omega
    have hlpf := hsmooth (m - 1) hmem
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo]
    exact ⟨by omega, mem_smoothNumbers_of_lpf_le (by omega) hlpf⟩
  · intro a ha b hb h
    have ha2 := hm2 a (Finset.mem_coe.mp ha)
    have hb2 := hm2 b (Finset.mem_coe.mp hb)
    omega

/-- **Per-cell bound.** For prime `p` and `k ≥ 1`, the two run counts together
are at most twice the number of `(p+1)`-smooth numbers `≤ 2x + 1`. -/
theorem runCount_le_two_mul_smoothUpTo {x p k : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) :
    rightRunCount x p k + leftRunCount x p k ≤
      2 * (Nat.smoothNumbersUpTo (2 * x + 1) (p + 1)).card := by
  have hright := rightRunCount_le_smoothUpTo (x := x) (p := p) (k := k) hk
  have hleft : leftRunCount x p k ≤
      (Nat.smoothNumbersUpTo (2 * x + 1) (p + 1)).card :=
    (leftRunCount_le_smoothUpTo (x := x) (p := p) (k := k) hk hp.two_le).trans
      (Finset.card_le_card fun n hn => by
        rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
        exact ⟨by omega, hn.2⟩)
  omega

/-- **Small-band bound (smooth-number form).**  The `p ≤ Z` part of
`runCountSum x` is at most `(Z+1)·4Z` times the number of `(Z+1)`-smooth
numbers `≤ 2x + 1`. -/
theorem smallBand_runSum_le (x Z : ℕ) :
    ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) ≤
      (Z + 1) * (4 * Z) * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card := by
  calc ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ p ∈ Nat.primesLE Z, ∑ _k ∈ Finset.Icc 1 (2 * p),
          2 * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hp2 : p.Prime := Nat.prime_of_mem_primesLE hp
        have hpZ : p ≤ Z := Nat.le_of_mem_primesLE hp
        calc rightRunCount x p k + leftRunCount x p k
            ≤ 2 * (Nat.smoothNumbersUpTo (2 * x + 1) (p + 1)).card :=
              runCount_le_two_mul_smoothUpTo hk1 hp2
          _ ≤ 2 * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card :=
              Nat.mul_le_mul (le_refl 2)
                (Finset.card_le_card
                  (smoothNumbersUpTo_mono_right' (by omega : p + 1 ≤ Z + 1)))
    _ ≤ ∑ _p ∈ Nat.primesLE Z,
          4 * Z * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card := by
        apply Finset.sum_le_sum
        intro p hp
        have hpZ : p ≤ Z := Nat.le_of_mem_primesLE hp
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_Icc]
        have hcard : 2 * p + 1 - 1 = 2 * p := by omega
        rw [hcard]
        calc (2 * p) * (2 * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card)
            = (4 * p) * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card := by
              ring
          _ ≤ (4 * Z) * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card :=
              Nat.mul_le_mul (by omega) (le_refl _)
    _ = (Nat.primesLE Z).card *
          (4 * Z * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Z + 1) * (4 * Z * (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card) :=
        Nat.mul_le_mul (primesLE_card_le Z) (le_refl _)
    _ = (Z + 1) * (4 * Z) *
          (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card := by ring

/-- **Small-band bound (explicit form).**  Inserting the exponent-vector bound
gives `smallBand ≤ (Z+1)·4Z·(log₂(2x+1)+1)^(Z+1)`. -/
theorem smallBand_runSum_le_explicit (x Z : ℕ) :
    ∑ p ∈ Nat.primesLE Z, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) ≤
      (Z + 1) * (4 * Z) * (Nat.log 2 (2 * x + 1) + 1) ^ (Z + 1) := by
  refine (smallBand_runSum_le x Z).trans ?_
  have hcard : (Z + 1).primesBelow.card ≤ Z + 1 := by
    rw [Nat.primesBelow_eq_filter_range]
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))
  have h1 : (Nat.smoothNumbersUpTo (2 * x + 1) (Z + 1)).card ≤
      (Nat.log 2 (2 * x + 1) + 1) ^ (Z + 1) :=
    (smoothUpTo_card_le_log2_pow (2 * x + 1) (Z + 1)).trans
      (pow_le_pow_right' (by norm_num) hcard)
  exact Nat.mul_le_mul (le_refl _) h1

end WitnessBounds

section Payoff

/-- Auxiliary exponential domination: `4·(M+1)·(M+2) ≤ 2^M` for `M ≥ 11`. -/
theorem four_mul_succ_mul_succ_le_pow {M : ℕ} (hM : 11 ≤ M) :
    4 * (M + 1) * (M + 2) ≤ 2 ^ M := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) + 2 ≤ 2 * (k + 1) := by omega
    calc 4 * ((k + 1) + 1) * ((k + 1) + 2)
        = 4 * (k + 2) * (k + 3) := by ring
      _ ≤ (4 * (k + 2)) * (2 * (k + 1)) := Nat.mul_le_mul (le_refl _) h1
      _ = 2 * (4 * (k + 1) * (k + 2)) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul (le_refl _) ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **Payoff (log–log cutoff).**  For `Z = Nat.log 2 (Nat.log 2 x)`, the
small-prime band of `runCountSum x` is eventually at most `x^{1/2}`.

The chain: the sum is `≤ (M+1)·4M·(Nat.log 2 (2x+1)+1)^(M+1)` where
`L = Nat.log 2 x`, `M = Nat.log 2 L`.  Then `Nat.log 2 (2x+1) + 1 ≤ L + 2 ≤
2^(M+2)`, so the bound is `≤ 4(M+1)M·2^{(M+2)(M+1)} ≤ 2^{M + (M+1)(M+2)}`;
the exponent satisfies `2·(M + (M+1)(M+2)) ≤ 4(M+1)(M+2) ≤ 2^M ≤ L`, i.e. the
bound is `≤ 2^{L/2} ≤ x^{1/2}` once `M ≥ 11`. -/
theorem smallBand_runSum_le_rpow_half_eventually :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((∑ p ∈ Nat.primesLE (Nat.log 2 (Nat.log 2 x)),
          ∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) ≤
        (x : ℝ) ^ (1 / 2 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 2048)] with x hx
  have hx0 : x ≠ 0 := by
    have h : 0 < x := lt_of_lt_of_le (by norm_num) hx
    omega
  set L := Nat.log 2 x with hLdef
  set M := Nat.log 2 L with hMdef
  have hL : 2048 ≤ L := (Nat.le_log_iff_pow_le Nat.one_lt_two hx0).mpr hx
  have hL0 : L ≠ 0 := by omega
  have hM : 11 ≤ M := by
    apply (Nat.le_log_iff_pow_le Nat.one_lt_two hL0).mpr
    calc (2 : ℕ) ^ 11 = 2048 := by norm_num
      _ ≤ L := hL
  have hML : 2 ^ M ≤ L := Nat.pow_log_le_self 2 hL0
  have hlog : Nat.log 2 (2 * x + 1) + 1 ≤ L + 2 := by
    have hlt : 2 * x + 1 < 2 ^ (L + 2) := by
      have h1 : x < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two x
      have h2 : (2 : ℕ) ^ (L + 2) = 2 * 2 ^ (L + 1) := by
        rw [show L + 2 = L + 1 + 1 from rfl, pow_succ]; ring
      omega
    have h3 : Nat.log 2 (2 * x + 1) < L + 2 :=
      (Nat.log_lt_iff_lt_pow Nat.one_lt_two (by omega)).mpr hlt
    omega
  have hL2 : L + 2 ≤ 2 ^ (M + 2) := by
    have h1 : L + 1 ≤ 2 ^ (M + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two L
    have h2 : 1 ≤ 2 ^ (M + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc L + 2 = (L + 1) + 1 := by ring
      _ ≤ 2 ^ (M + 1) + 2 ^ (M + 1) := Nat.add_le_add h1 h2
      _ = 2 ^ (M + 2) := by rw [pow_succ]; ring
  have hsum := smallBand_runSum_le_explicit x M
  have hB : (M + 1) * (4 * M) * (Nat.log 2 (2 * x + 1) + 1) ^ (M + 1) ≤
      2 ^ (L / 2) := by
    have hbase : Nat.log 2 (2 * x + 1) + 1 ≤ 2 ^ (M + 2) := hlog.trans hL2
    have hpow : (Nat.log 2 (2 * x + 1) + 1) ^ (M + 1) ≤
        (2 ^ (M + 2)) ^ (M + 1) := Nat.pow_le_pow_left hbase _
    have hfour : (M + 1) * (4 * M) ≤ 2 ^ M := by
      calc (M + 1) * (4 * M) = 4 * M * (M + 1) := by ring
        _ ≤ 4 * (M + 1) * (M + 2) :=
            Nat.mul_le_mul (le_refl _) (by omega)
        _ ≤ 2 ^ M := four_mul_succ_mul_succ_le_pow hM
    have hexp : M + (M + 2) * (M + 1) ≤ L / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      calc (M + (M + 2) * (M + 1)) * 2
          = 2 * M + 2 * ((M + 1) * (M + 2)) := by ring
        _ ≤ 2 * ((M + 1) * (M + 2)) + 2 * ((M + 1) * (M + 2)) := by
            apply Nat.add_le_add_right
            exact Nat.mul_le_mul (le_refl 2) (by omega)
        _ = 4 * (M + 1) * (M + 2) := by ring
        _ ≤ 2 ^ M := four_mul_succ_mul_succ_le_pow hM
        _ ≤ L := hML
    calc (M + 1) * (4 * M) * (Nat.log 2 (2 * x + 1) + 1) ^ (M + 1)
        ≤ 2 ^ M * (2 ^ (M + 2)) ^ (M + 1) := Nat.mul_le_mul hfour hpow
      _ = 2 ^ (M + (M + 2) * (M + 1)) := by
          rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right (by norm_num) hexp
  have hcast : ((∑ p ∈ Nat.primesLE M, ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) ≤
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
    _ = ((2 : ℝ) ^ (L : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
    _ = (((2 ^ L : ℕ) : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
    _ ≤ (x : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h2L (by norm_num)

end Payoff

end JSP314
