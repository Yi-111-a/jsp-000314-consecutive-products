import JSP314.BandSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# JSP-000314 — unconditional eventual upper bound on `badNonSingletonCount`

This file assembles the **strongest unconditional eventual upper bound** on
`N(x) = badNonSingletonCount x` provable from the already-established pieces.

(`JSP314.APPsi`, which was intended to supply `runCountSum_le`, does not
compile against the pinned mathlib; the needed estimates are therefore
reproved here, self-contained, on top of `JSP314.BandSum`.)

Chain:

* `BandSum.badNonSingletonCount_le_two_mul_runCountSum_add_const`
  (`N(x) ≤ 2·runCountSum(x) + (2·10^16 + 1)` — `RunDecomp` for the short
  branch, `SSBound` for the Sylvester–Schur constant).
* Per-cell bound `rightRunCount x p k + leftRunCount x p k ≤ 2·(2x/p²)`
  (multiples-of-`p²` injection, as in `BandLarge`), so the inner `k`-sum is
  `≤ 8x/p`.
* `∑_{p ≤ √(2x)} 1/p ≤ 1 + log √(2x)` (harmonic bound), giving
  `runCountSum x ≤ 8·x·(1 + log √(2x)) ≤ 4·x·log x + 12·x`.
* Hence eventually `N(x) ≤ (8 + ε)·x·log x` for every `ε > 0`, and in
  particular `N(x) ≤ 9·x·log x`.

The residual `x·log x` factor is exactly the loss in the harmonic bound
(`∑_{p≤y} 1/p ≤ 1 + log y`); a Mertens-type `O(log log y)` bound would
improve the headline to `O(x·log log x)`, but no such bound is currently
proved in the repository.
-/

namespace JSP314

open Filter

/-! ### Per-cell bounds for the run witnesses -/

/-- Auxiliary: a number whose largest prime factor is the prime `p` is
at least `2` (copy of `BandLarge.two_le_of_largestPrimeFactor_eq_prime`,
which is unavailable since `BandLarge` is not imported). -/
private theorem two_le_of_largestPrimeFactor_eq_prime {p m : ℕ} (hp : p.Prime)
    (h : largestPrimeFactor m = p) : 2 ≤ m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have h1 : largestPrimeFactor m = 1 :=
      largestPrimeFactor_eq_one_iff.mpr (by omega)
    have h2 := hp.two_le
    omega
  · exact hm

/-- `rightRunCount x p k ≤ 2x / p²`: witnesses `m` are nonzero multiples of
`p²` below `2x`, and `m ↦ m / p²` is injective on them. -/
private theorem rightRunCount_le_div (x p k : ℕ) (hp : p.Prime) :
    rightRunCount x p k ≤ 2 * x / p ^ 2 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hmaps : Set.MapsTo (· / p ^ 2) (↑(rightRunWitness x p k) : Set ℕ)
      (↑(Finset.Icc 1 (2 * x / p ^ 2)) : Set ℕ) := by
    intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, -⟩ := hm
    have hmpos : 0 < m := by
      have := two_le_of_largestPrimeFactor_eq_prime hp hlpf
      omega
    have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hpdvd
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hm2x⟩
    rw [Nat.le_div_iff_mul_le hp2]
    rwa [one_mul]
  have hinj : Set.InjOn (· / p ^ 2) (↑(rightRunWitness x p k) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    have hab' : a / p ^ 2 = b / p ^ 2 := hab
    have h1 := Nat.div_mul_cancel ha.2.1
    have h2 := Nat.div_mul_cancel hb.2.1
    rw [← h1, ← h2, hab']
  calc rightRunCount x p k = (rightRunWitness x p k).card := rfl
    _ ≤ (Finset.Icc 1 (2 * x / p ^ 2)).card :=
        Finset.card_le_card_of_injOn (· / p ^ 2) hmaps hinj
    _ = 2 * x / p ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- `leftRunCount x p k ≤ 2x / p²`. -/
private theorem leftRunCount_le_div (x p k : ℕ) (hp : p.Prime) :
    leftRunCount x p k ≤ 2 * x / p ^ 2 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hmaps : Set.MapsTo (· / p ^ 2) (↑(leftRunWitness x p k) : Set ℕ)
      (↑(Finset.Icc 1 (2 * x / p ^ 2)) : Set ℕ) := by
    intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, -⟩ := hm
    have hmpos : 0 < m := by
      have := two_le_of_largestPrimeFactor_eq_prime hp hlpf
      omega
    have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hpdvd
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hm2x⟩
    rw [Nat.le_div_iff_mul_le hp2]
    rwa [one_mul]
  have hinj : Set.InjOn (· / p ^ 2) (↑(leftRunWitness x p k) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    have hab' : a / p ^ 2 = b / p ^ 2 := hab
    have h1 := Nat.div_mul_cancel ha.2.1
    have h2 := Nat.div_mul_cancel hb.2.1
    rw [← h1, ← h2, hab']
  calc leftRunCount x p k = (leftRunWitness x p k).card := rfl
    _ ≤ (Finset.Icc 1 (2 * x / p ^ 2)).card :=
        Finset.card_le_card_of_injOn (· / p ^ 2) hmaps hinj
    _ = 2 * x / p ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-! ### Harmonic bounds -/

/-- `1/(N+1) ≤ log(N+1) − log N` for `N ≥ 1`. -/
private theorem one_div_succ_le_log_sub_log {N : ℕ} (hN : 1 ≤ N) :
    (1 : ℝ) / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hle := Real.log_le_sub_one_of_pos (x := (N : ℝ) / ((N : ℝ) + 1))
    (div_pos hNR hN1)
  rw [Real.log_div hNR.ne' hN1.ne'] at hle
  have h4 : (N : ℝ) / ((N : ℝ) + 1) - 1 = -((N : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  rw [h4] at hle
  rw [one_div]
  linarith

/-- Harmonic bound over a range: `∑_{i<N} 1/(i+1) ≤ 1 + log N`. -/
private theorem sum_range_one_div_succ_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    · have hstep := one_div_succ_le_log_sub_log hpos
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- Primes reciprocal bound: `∑_{p ≤ y} 1/p ≤ 1 + log y`. -/
private theorem sum_primesLE_inv_le (y : ℕ) :
    ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p ≤ 1 + Real.log y := by
  rw [Nat.primesLE_eq_filter_range]
  calc ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ n ∈ Finset.range (y + 1), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by positivity
    _ = ∑ i ∈ Finset.range y, (1 : ℝ) / ((i : ℝ) + 1) := by
        rw [Finset.sum_range_succ']
        simp
    _ ≤ 1 + Real.log y := sum_range_one_div_succ_le y

/-! ### The run-count sum bound -/

/-- The inner `k`-sum bound: each `k ∈ [1, 2p]` contributes at most the
trivial `2·(2x/p²)`, so the inner sum is `≤ 8x/p` in `ℝ`. -/
private theorem runCountSum_inner_le {x p : ℕ} (hp : Nat.Prime p) :
    ((∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
      ≤ 8 * x / p := by
  have hb : ∀ k ∈ Finset.Icc 1 (2 * p),
      rightRunCount x p k + leftRunCount x p k ≤ 2 * (2 * x / p ^ 2) := by
    intro k _
    have h1 := rightRunCount_le_div x p k hp
    have h2 := leftRunCount_le_div x p k hp
    omega
  have hcard : (Finset.Icc 1 (2 * p)).card = 2 * p := by
    rw [Nat.card_Icc]; omega
  have hsum : ∑ k ∈ Finset.Icc 1 (2 * p),
      (rightRunCount x p k + leftRunCount x p k)
        ≤ (2 * p) * (2 * (2 * x / p ^ 2)) := by
    calc ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k)
        ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), (2 * (2 * x / p ^ 2)) :=
          Finset.sum_le_sum hb
      _ = (Finset.Icc 1 (2 * p)).card * (2 * (2 * x / p ^ 2)) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
      _ = (2 * p) * (2 * (2 * x / p ^ 2)) := by rw [hcard]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp0 : (p : ℝ) ≠ 0 := hpR.ne'
  calc ((∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ)
      ≤ (((2 * p) * (2 * (2 * x / p ^ 2)) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hsum
    _ = (2 * p : ℝ) * (2 * ((2 * x / p ^ 2 : ℕ) : ℝ)) := by
        push_cast; ring
    _ ≤ (2 * p : ℝ) * (2 * ((2 * x : ℝ) / (p : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h := Nat.cast_div_le (α := ℝ) (m := 2 * x) (n := p ^ 2)
        simpa using h
    _ = 8 * (x : ℝ) / (p : ℝ) := by
        field_simp
        ring

/-- **Run-count sum bound (honest `O(x·log x)`):**
`runCountSum x ≤ 8·x·(1 + log √(2x))`. -/
private theorem runCountSum_le (x : ℕ) :
    (runCountSum x : ℝ) ≤ 8 * x * (1 + Real.log (Nat.sqrt (2 * x))) := by
  calc (runCountSum x : ℝ)
      = ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ((∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) : ℕ) : ℝ) := by
        have hopen : runCountSum x =
            ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
              ∑ k ∈ Finset.Icc 1 (2 * p),
                (rightRunCount x p k + leftRunCount x p k) := rfl
        rw [hopen, Nat.cast_sum]
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (8 * x / p : ℝ) :=
        Finset.sum_le_sum fun p hp =>
          runCountSum_inner_le (Nat.prime_of_mem_primesLE hp)
    _ = 8 * x * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (1 : ℝ) / p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_one_div]
    _ ≤ 8 * x * (1 + Real.log (Nat.sqrt (2 * x))) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_inv_le _) (by positivity)

/-! ### Assembly -/

/-- **Unconditional eventual upper bound, sharp-constant form:** for every
`ε > 0`, `badNonSingletonCount x ≤ (8 + ε)·x·log x` for all sufficiently
large `x`.  The `8` is `2` (short/long + left/right slack) times the
`4 = 8·(1/2)` coming from `log √(2x) ~ (log x)/2`; the `ε` absorbs the
`24·x` linear tail and the Sylvester–Schur constant `2·10^16 + 1`. -/
theorem badNonSingletonCount_eventually_le_add_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (8 + ε) * (x : ℝ) * Real.log (x : ℝ) := by
  have hLt : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLt.eventually_ge_atTop (26 / ε),
    eventually_ge_atTop (2 * 10 ^ 16 + 1)] with x hL hx
  have hx1 : 1 ≤ x := by omega
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  -- Combinatorial decomposition: `N ≤ 2·runCountSum + C₀`.
  have hN : (badNonSingletonCount x : ℝ) ≤
      2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_two_mul_runCountSum_add_const x
  -- `log(Nat.sqrt(2x)) ≤ log(2x)/2` since `(Nat.sqrt (2x))² ≤ 2x`.
  have hs1 : 1 ≤ Nat.sqrt (2 * x) := by
    rw [Nat.le_sqrt]
    omega
  have hs2 : (Nat.sqrt (2 * x)) ^ 2 ≤ 2 * x := Nat.sqrt_le' (2 * x)
  have hs2R : (((Nat.sqrt (2 * x) : ℕ) : ℝ)) ^ 2 ≤ ((2 * x : ℕ) : ℝ) := by
    exact_mod_cast hs2
  have hslog : Real.log ((Nat.sqrt (2 * x) : ℕ) : ℝ) ≤
      Real.log ((2 * x : ℕ) : ℝ) / 2 := by
    have hsR : (0 : ℝ) < ((Nat.sqrt (2 * x) : ℕ) : ℝ) := by
      exact_mod_cast hs1
    have h2 := Real.log_le_log (by positivity) hs2R
    rw [Real.log_pow] at h2
    have h2' : (2 : ℝ) * Real.log ((Nat.sqrt (2 * x) : ℕ) : ℝ) ≤
        Real.log ((2 * x : ℕ) : ℝ) := by
      simpa using h2
    linarith
  have hlog2x : Real.log ((2 * x : ℕ) : ℝ) =
      Real.log 2 + Real.log (x : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num) (ne_of_gt hxR)]
  have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  -- `runCountSum x ≤ 8x(1 + log√(2x)) ≤ 4x·log x + 12x`.
  have hrun : (runCountSum x : ℝ) ≤
      4 * (x : ℝ) * Real.log (x : ℝ) + 12 * (x : ℝ) := by
    calc (runCountSum x : ℝ)
        ≤ 8 * (x : ℝ) * (1 + Real.log ((Nat.sqrt (2 * x) : ℕ) : ℝ)) :=
          runCountSum_le x
      _ ≤ 8 * (x : ℝ) * (1 + Real.log ((2 * x : ℕ) : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 8 * (x : ℝ) + 4 * (x : ℝ) * (Real.log 2 + Real.log (x : ℝ)) := by
          rw [hlog2x]; ring
      _ ≤ 8 * (x : ℝ) + 4 * (x : ℝ) * (1 + Real.log (x : ℝ)) := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 4 * (x : ℝ) * Real.log (x : ℝ) + 12 * (x : ℝ) := by ring
  -- `ε·x·log x` absorbs `24x + C₀`.
  have hεL : (26 : ℝ) ≤ ε * Real.log (x : ℝ) := by
    have h := hL
    rw [div_le_iff₀ hε] at h
    -- h : 26 ≤ Real.log ↑x * ε
    rw [mul_comm]
    exact h
  have hC : ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have habs : 24 * (x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) ≤
      ε * (x : ℝ) * Real.log (x : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hεL hxR.le
    -- h : 26 * ↑x ≤ (ε * log ↑x) * ↑x
    nlinarith [h, hC]
  calc (badNonSingletonCount x : ℝ)
      ≤ 2 * (runCountSum x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := hN
    _ ≤ 2 * (4 * (x : ℝ) * Real.log (x : ℝ) + 12 * x) +
          ((2 * 10 ^ 16 + 1 : ℕ) : ℝ) := by
        linarith [hrun]
    _ = 8 * (x : ℝ) * Real.log (x : ℝ) +
          (24 * (x : ℝ) + ((2 * 10 ^ 16 + 1 : ℕ) : ℝ)) := by ring
    _ ≤ 8 * (x : ℝ) * Real.log (x : ℝ) +
          ε * (x : ℝ) * Real.log (x : ℝ) :=
        add_le_add_right habs _
    _ = (8 + ε) * (x : ℝ) * Real.log (x : ℝ) := by ring

/-- **Headline unconditional bound:** for all sufficiently large `x`,
`badNonSingletonCount x ≤ 9·x·log x` (natural logarithm).

This is `badNonSingletonCount_eventually_le_add_eps` at `ε = 1`. -/
theorem badNonSingletonCount_eventually_le :
    ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤ 9 * (x : ℝ) * Real.log (x : ℝ) := by
  filter_upwards [badNonSingletonCount_eventually_le_add_eps 1 (by norm_num)]
    with x h
  have h9 : (8 + (1 : ℝ)) = 9 := by norm_num
  rw [h9] at h
  exact h

end JSP314
