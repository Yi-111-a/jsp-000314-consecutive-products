import JSP314.PairKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# JSP-000314 — the small-prime band `p ≤ log₂ x` of the near-pair sum

Milestone toward `badNonSingleton_interval_bound` (the sole placeholder in
`Main.lean`).  The residual reduces (ShortResidual + FreshEye) to an
eventual bound on

    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p

This file bounds the **small-prime slice** of that sum, with cutoff

    f x = Nat.log 2 x      (i.e. `p ≤ log₂ x = log x / log 2`),

improving on `SmoothUB.nearPair_smallp_sum_le_rpow_half_eventually`, which
only reached `p ≤ log₂ log₂ x`.

## Method

`PairSmooth.nearPairCoveredCount_le_two_mul_consecSmoothPairCount` gives
`nearPairCoveredCount x p ≤ 2 · consecSmoothPairCount x p`, and the
Pell-kernel bound `PairKernel.consecSmoothPairCount_le_kernel_mul_log'`
gives `consecSmoothPairCount x p ≤ 1 + 4^{π'(p+1)}·(log₂(x+1) + 1)` where
`π'(k) = (Nat.primesBelow k).card`.  The new input is an elementary
*wheel bound* on the prime count:

    primesBelow_card_le_div3 : (Nat.primesBelow n).card ≤ n / 3 + 3

— every prime `≥ 5` is `±1 mod 6`, and `k ↦ k/3` is injective on the
residue classes `{1,5} mod 6` (so at most `n/3 + 1` of them lie below `n`).

Hence `4^{π'(p+1)} ≤ 4^{(p+1)/3 + 3} = O(2^{2p/3})`, and for `p ≤ L =
log₂ x` the band sums to `O(L² · 2^{2L/3}) = O(x^{2/3} · log² x)`,
eventually `≤ x^{3/4}` and in fact `≤ x · (log x)⁻²`.

## Theorems

* `prime_mod_six`, `card_mod_six_residues`, `primesBelow_card_le_div3` —
  the mod-6 wheel bound `π'(n) ≤ n/3 + 3`.
* `nearPairCoveredCount_le_kernel` — per-prime bound via the Pell kernel.
* `nearPair_logBand_sum_le`, `nearPair_logBand_sum_le'` — the band sum is
  `≤ 1024·(L+1)·(L+2)·2^{2⌊L/3⌋}` for `L = log₂ x`.
* `pow_dom_poly` — the elementary domination `1024(12k+12)(12k+13) ≤ 2^k`
  for `k ≥ 42`.
* `nearPair_smallBand_sum_le_rpow_three_quarters_eventually` — headline:
  the `p ≤ log₂ x` slice is eventually `≤ x^{3/4}`.
* `nearPair_smallBand_sum_le_log_sq_eventually` — corollary in the
  requested shape `≤ x · (log x)^{-2}`.

## Why `log₂ x` is (essentially) the limit of this method

The kernel bound contributes `4^{π'(p)} = exp(Θ(p))`; for `p ≤ c·log₂ x`
this is `x^{2c/3 + o(1)}`, sub-polynomial iff `c < 3/2` with the mod-6
wheel (`c < 15/8` with a mod-30 wheel, at the cost of a longer
injection).  A power cutoff `p ≤ x^δ` is *not* reachable from the
Pell-kernel count — `4^{π'(x^δ)}` is super-polynomial — nor from
smooth-number counting alone; sublinear bounds for large `p` are
genuinely the analytic content of Ta26c.  The `log x`-scale cutoff
achieved here is essentially the ceiling of elementary kernel bounds.
-/

namespace JSP314

open Classical Filter

section Wheel

/-- Every prime `≥ 5` is `±1 mod 6`: residues `0, 2, 4` are even and
residue `3` is divisible by `3`. -/
theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := fun hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd) (by omega)
  have h3 : ¬ 3 ∣ p := fun hd =>
    absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 3) hp).mp hd)
      (by omega)
  have h2' : p % 2 ≠ 0 := fun h => h2 (Nat.dvd_of_mod_eq_zero h)
  have h3' : p % 3 ≠ 0 := fun h => h3 (Nat.dvd_of_mod_eq_zero h)
  omega

/-- At most `n/3 + 1` numbers below `n` are `±1 mod 6`: the map
`k ↦ k/3` sends `6q+1 ↦ 2q` and `6q+5 ↦ 2q+1`, hence is injective on the
residue set and lands in `range (n/3 + 1)`. -/
theorem card_mod_six_residues (n : ℕ) :
    ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5).card ≤
      n / 3 + 1 := by
  have h := Finset.card_le_card_of_injOn (fun k => k / 3)
    (s := (Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5)
    (t := Finset.range (n / 3 + 1)) ?_ ?_
  · rwa [Finset.card_range] at h
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_add_one_iff.mpr (Nat.div_le_div_right hk.1.le)
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    obtain ⟨-, ha6⟩ := ha
    obtain ⟨-, hb6⟩ := hb
    change a / 3 = b / 3 at hab
    omega

/-- **Wheel bound mod 6**: `π'(n) = #(Nat.primesBelow n) ≤ n/3 + 3`,
since `primesBelow n ⊆ {2, 3} ∪ {k < n : k ≡ ±1 mod 6}`. -/
theorem primesBelow_card_le_div3 (n : ℕ) :
    (Nat.primesBelow n).card ≤ n / 3 + 3 := by
  have hsub : Nat.primesBelow n ⊆
      insert 2 (insert 3
        ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5)) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    obtain ⟨hpn, hpprime⟩ := hp
    by_cases h5 : 5 ≤ p
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter,
        Finset.mem_range]
      exact Or.inr (Or.inr ⟨hpn, prime_mod_six hpprime h5⟩)
    · have hp2 : 2 ≤ p := hpprime.two_le
      have hp4 : p ≤ 4 := by omega
      interval_cases p
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
      · exact absurd hpprime (by decide)
  calc (Nat.primesBelow n).card
      ≤ (insert 2 (insert 3
          ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5).card + 2 := by
        have h1 := Finset.card_insert_le (2 : ℕ)
          (insert 3 ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5))
        have h2 := Finset.card_insert_le (3 : ℕ)
          ((Finset.range n).filter fun k => k % 6 = 1 ∨ k % 6 = 5)
        omega
    _ ≤ (n / 3 + 1) + 2 := Nat.add_le_add_right (card_mod_six_residues n) 2
    _ = n / 3 + 3 := by omega

end Wheel

section KernelBand

/-- **Per-prime bound (Pell-kernel form).**
`nearPairCoveredCount x p ≤ 2 + 2·4^{π'(p+1)}·(log₂(x+1) + 1)`. -/
theorem nearPairCoveredCount_le_kernel (x p : ℕ) :
    nearPairCoveredCount x p ≤
      2 + 2 * 4 ^ (Nat.primesBelow (p + 1)).card * (Nat.log 2 (x + 1) + 1) := by
  have h1 := nearPairCoveredCount_le_two_mul_consecSmoothPairCount x p
  have h2 := consecSmoothPairCount_le_kernel_mul_log' x p
  calc nearPairCoveredCount x p
      ≤ 2 * consecSmoothPairCount x p := h1
    _ ≤ 2 * (1 + 4 ^ (Nat.primesBelow (p + 1)).card *
          (Nat.log 2 (x + 1) + 1)) := Nat.mul_le_mul (le_refl 2) h2
    _ = 2 + 2 * 4 ^ (Nat.primesBelow (p + 1)).card *
          (Nat.log 2 (x + 1) + 1) := by ring

/-- **Band sum (explicit form).**  For `p ≤ L` the wheel bound gives
`π'(p+1) ≤ L/3 + 4`, so each prime contributes the same kernel bound. -/
theorem nearPair_logBand_sum_le (x L : ℕ) :
    ∑ p ∈ Nat.primesLE L, nearPairCoveredCount x p ≤
      (L + 1) * (2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1)) := by
  calc ∑ p ∈ Nat.primesLE L, nearPairCoveredCount x p
      ≤ ∑ _p ∈ Nat.primesLE L,
          (2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpL : p ≤ L := Nat.le_of_mem_primesLE hp
        have hpi : (Nat.primesBelow (p + 1)).card ≤ L / 3 + 4 := by
          have h := primesBelow_card_le_div3 (p + 1)
          have hdiv : (p + 1) / 3 ≤ L / 3 + 1 := by
            calc (p + 1) / 3 ≤ (L + 1) / 3 :=
                  Nat.div_le_div_right (by omega : p + 1 ≤ L + 1)
              _ ≤ L / 3 + 1 := by omega
          omega
        have h4 : 4 ^ (Nat.primesBelow (p + 1)).card ≤ 4 ^ (L / 3 + 4) :=
          pow_le_pow_right' (by norm_num) hpi
        calc nearPairCoveredCount x p
            ≤ 2 + 2 * 4 ^ (Nat.primesBelow (p + 1)).card *
                (Nat.log 2 (x + 1) + 1) := nearPairCoveredCount_le_kernel x p
          _ ≤ 2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1) :=
              add_le_add (le_refl 2)
                (Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) h4) (le_refl _))
    _ = (Nat.primesLE L).card *
          (2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1)) :=
        Finset.sum_const_nat fun _ _ => rfl
    _ ≤ (L + 1) * (2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1)) :=
        Nat.mul_le_mul (primesLE_card_le L) (le_refl _)

/-- **Band sum (simplified form)** at the cutoff `L = log₂ x`:
the `p ≤ log₂ x` slice of the near-pair sum is at most
`1024·(L+1)·(L+2)·2^{2⌊L/3⌋}`, using `4^{L/3+4} = 256·2^{2⌊L/3⌋}` and
`log₂(x+1) + 1 ≤ L + 2`. -/
theorem nearPair_logBand_sum_le' (x : ℕ) :
    ∑ p ∈ Nat.primesLE (Nat.log 2 x), nearPairCoveredCount x p ≤
      1024 * (Nat.log 2 x + 1) * (Nat.log 2 x + 2) *
        2 ^ (2 * (Nat.log 2 x / 3)) := by
  set L := Nat.log 2 x with hLdef
  have hlog : Nat.log 2 (x + 1) + 1 ≤ L + 2 := by
    have hlt : x + 1 ≤ 2 ^ (L + 1) := Nat.lt_pow_succ_log_self one_lt_two x
    have hlog2 : Nat.log 2 (x + 1) ≤ L + 1 :=
      (Nat.log_mono_right hlt).trans_eq (Nat.log_pow one_lt_two _)
    omega
  have h4pow : (4 : ℕ) ^ (L / 3) = 2 ^ (2 * (L / 3)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h4 : 4 ^ (L / 3 + 4) = 256 * 2 ^ (2 * (L / 3)) := by
    calc 4 ^ (L / 3 + 4) = 4 ^ (L / 3) * 4 ^ 4 := by rw [pow_add]
      _ = 2 ^ (2 * (L / 3)) * 256 := by rw [h4pow]; norm_num
      _ = 256 * 2 ^ (2 * (L / 3)) := by ring
  have hT : 2 ≤ 512 * 2 ^ (2 * (L / 3)) * (L + 2) := by
    have h1 : 1 ≤ 2 ^ (2 * (L / 3)) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ≤ L + 2 := by omega
    calc 2 ≤ 512 * 1 * 2 := by norm_num
      _ ≤ 512 * 2 ^ (2 * (L / 3)) * (L + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 512) h1) h2
  calc ∑ p ∈ Nat.primesLE L, nearPairCoveredCount x p
      ≤ (L + 1) * (2 + 2 * 4 ^ (L / 3 + 4) * (Nat.log 2 (x + 1) + 1)) :=
        nearPair_logBand_sum_le x L
    _ ≤ (L + 1) * (2 + 512 * 2 ^ (2 * (L / 3)) * (L + 2)) := by
        refine Nat.mul_le_mul (le_refl (L + 1)) ?_
        rw [h4]
        apply add_le_add (le_refl 2)
        have heq : 2 * (256 * 2 ^ (2 * (L / 3))) =
            512 * 2 ^ (2 * (L / 3)) := by ring
        exact Nat.mul_le_mul (le_of_eq heq) hlog
    _ = (L + 1) * 2 + (L + 1) * (512 * 2 ^ (2 * (L / 3)) * (L + 2)) := by ring
    _ ≤ (L + 1) * (512 * 2 ^ (2 * (L / 3)) * (L + 2)) +
          (L + 1) * (512 * 2 ^ (2 * (L / 3)) * (L + 2)) :=
        add_le_add (Nat.mul_le_mul (le_refl (L + 1)) hT) (le_refl _)
    _ = 1024 * (L + 1) * (L + 2) * 2 ^ (2 * (L / 3)) := by ring

end KernelBand

section Payoff

/-- **Polynomial-vs-exponential domination:**
`1024·(12k+12)·(12k+13) ≤ 2^k` for `k ≥ 42`.  Base case by `norm_num`;
induction step uses `(12k+24)(12k+25) ≤ 2(12k+12)(12k+13)`, i.e.
`288 ≤ 144k² + 12k`, for `k ≥ 2`. -/
theorem pow_dom_poly {k : ℕ} (hk : 42 ≤ k) :
    1024 * (12 * k + 12) * (12 * k + 13) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (12 * (k + 1) + 12) * (12 * (k + 1) + 13) ≤
        2 * ((12 * k + 12) * (12 * k + 13)) := by
      nlinarith [Nat.mul_le_mul hk hk]
    calc 1024 * (12 * (k + 1) + 12) * (12 * (k + 1) + 13)
        = 1024 * ((12 * (k + 1) + 12) * (12 * (k + 1) + 13)) := by ring
      _ ≤ 1024 * (2 * ((12 * k + 12) * (12 * k + 13))) :=
          Nat.mul_le_mul (le_refl 1024) hstep
      _ = 2 * (1024 * (12 * k + 12) * (12 * k + 13)) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul (le_refl 2) ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **Headline bound (`x^{3/4}` form).**  For `x ≥ 2^{504}`, writing
`L = log₂ x` and `k = ⌊L/12⌋ ≥ 42`, the `p ≤ L` slice of the near-pair
sum is `≤ 1024·(L+1)·(L+2)·2^{2⌊L/3⌋} ≤ x^{1/12}·x^{2/3} = x^{3/4}`. -/
theorem nearPair_smallBand_sum_le_rpow_three_quarters_eventually :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter fun p =>
          p ≤ Nat.log 2 x, nearPairCoveredCount x p : ℕ) : ℝ) ≤
        (x : ℝ) ^ (3 / 4 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ 504)] with x hx
  have hx2le : (2 : ℕ) ≤ 2 ^ 504 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 504 := pow_le_pow_right' (by norm_num) (by norm_num)
  have hxpos_nat : 0 < x := by omega
  have hx0 : x ≠ 0 := hxpos_nat.ne'
  set L := Nat.log 2 x with hLdef
  have hL : 504 ≤ L := (Nat.le_log_iff_pow_le one_lt_two hx0).mpr hx
  set k := L / 12 with hkdef
  have hk : 42 ≤ k := by
    have h : 504 / 12 ≤ L / 12 := Nat.div_le_div_right hL
    rw [hkdef]; omega
  have hLk : L ≤ 12 * k + 11 := by rw [hkdef]; omega
  have hpk : 1024 * (L + 1) * (L + 2) ≤ 2 ^ k := by
    have h1 : L + 1 ≤ 12 * k + 12 := by omega
    have h2 : L + 2 ≤ 12 * k + 13 := by omega
    calc 1024 * (L + 1) * (L + 2)
        ≤ 1024 * (12 * k + 12) * (12 * k + 13) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_refl 1024) h1) h2
      _ ≤ 2 ^ k := pow_dom_poly hk
  -- ℕ bound on the filtered sum
  have hsub : (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => p ≤ L) ⊆
      Nat.primesLE L := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.2, hp.1.2⟩
  have hsum : ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter fun p => p ≤ L,
        nearPairCoveredCount x p ≤
      1024 * (L + 1) * (L + 2) * 2 ^ (2 * (L / 3)) :=
    (Finset.sum_le_sum_of_subset hsub).trans (nearPair_logBand_sum_le' x)
  -- real-valued comparisons
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxpos_nat
  have hxR : (0 : ℝ) ≤ x := hxpos.le
  have h2L : ((2 ^ L : ℕ) : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hx0
  -- `2^{2⌊L/3⌋} ≤ x^{2/3}`
  have hpow23 : ((2 ^ (2 * (L / 3)) : ℕ) : ℝ) ≤ (x : ℝ) ^ (2 / 3 : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    have hexp : ((2 * (L / 3) : ℕ) : ℝ) ≤ (2 / 3) * (L : ℝ) := by
      have h : ((L / 3 : ℕ) : ℝ) ≤ (L : ℝ) / 3 := by
        exact Nat.cast_div_le
      push_cast
      linarith
    calc (2 : ℝ) ^ ((2 * (L / 3) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ ((2 / 3) * (L : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((2 : ℝ) ^ (L : ℝ)) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
      _ = ((2 ^ L : ℕ) : ℝ) ^ (2 / 3 : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
      _ ≤ (x : ℝ) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) h2L
            (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  -- `1024·(L+1)·(L+2) ≤ 2^{⌊L/12⌋} ≤ x^{1/12}`
  have hsmall : ((1024 * (L + 1) * (L + 2) : ℕ) : ℝ) ≤
      (x : ℝ) ^ (1 / 12 : ℝ) := by
    have h2k : ((2 ^ k : ℕ) : ℝ) ≤ (x : ℝ) ^ (1 / 12 : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      have hk12 : (k : ℝ) ≤ (L : ℝ) / 12 := by
        rw [hkdef]
        exact Nat.cast_div_le
      calc (2 : ℝ) ^ (k : ℝ)
          ≤ (2 : ℝ) ^ ((L : ℝ) / 12) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hk12
        _ = ((2 : ℝ) ^ (L : ℝ)) ^ (1 / 12 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring
        _ = ((2 ^ L : ℕ) : ℝ) ^ (1 / 12 : ℝ) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]
        _ ≤ (x : ℝ) ^ (1 / 12 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) h2L
              (show (0 : ℝ) ≤ 1 / 12 by norm_num)
    exact (by exact_mod_cast hpk : ((1024 * (L + 1) * (L + 2) : ℕ) : ℝ) ≤
      ((2 ^ k : ℕ) : ℝ)).trans h2k
  -- combine: `sum ≤ 1024·(L+1)(L+2)·2^{2⌊L/3⌋} ≤ x^{1/12}·x^{2/3} = x^{3/4}`
  have hcast : ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter fun p =>
        p ≤ L, nearPairCoveredCount x p : ℕ) : ℝ) ≤
      ((1024 * (L + 1) * (L + 2) * 2 ^ (2 * (L / 3)) : ℕ) : ℝ) := by
    exact_mod_cast hsum
  refine hcast.trans ?_
  rw [show ((1024 * (L + 1) * (L + 2) * 2 ^ (2 * (L / 3)) : ℕ) : ℝ) =
      ((1024 * (L + 1) * (L + 2) : ℕ) : ℝ) * ((2 ^ (2 * (L / 3)) : ℕ) : ℝ)
      by push_cast; ring]
  calc ((1024 * (L + 1) * (L + 2) : ℕ) : ℝ) * ((2 ^ (2 * (L / 3)) : ℕ) : ℝ)
      ≤ (x : ℝ) ^ (1 / 12 : ℝ) * (x : ℝ) ^ (2 / 3 : ℝ) :=
        mul_le_mul hsmall hpow23 (Nat.cast_nonneg _)
          (Real.rpow_nonneg hxR _)
    _ = (x : ℝ) ^ (1 / 12 + 2 / 3 : ℝ) := by rw [← Real.rpow_add hxpos]
    _ = (x : ℝ) ^ (3 / 4 : ℝ) := by congr 1; norm_num

set_option maxRecDepth 8192 in
/-- **Requested shape** `≤ x · (log x)⁻²`: for `x ≥ 2^{504}` we have
`log x = 16·log(x^{1/16}) ≤ 16·x^{1/16} ≤ x^{1/8}` (since `x^{1/16} ≥ 16`),
so `(log x)² ≤ x^{1/4}` and `x^{3/4} ≤ x·(log x)⁻²`. -/
theorem nearPair_smallBand_sum_le_log_sq_eventually :
    ∀ᶠ x : ℕ in Filter.atTop,
      ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter fun p =>
          p ≤ Nat.log 2 x, nearPairCoveredCount x p : ℕ) : ℝ) ≤
        (x : ℝ) * (Real.log x) ^ (-2 : ℝ) := by
  filter_upwards [nearPair_smallBand_sum_le_rpow_three_quarters_eventually,
    Filter.eventually_ge_atTop (2 ^ 504)] with x hx hxge
  have hx2le : (2 : ℕ) ≤ 2 ^ 504 := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 504 := pow_le_pow_right' (by norm_num) (by norm_num)
  have hx1n : 1 < x := by omega
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx1n
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans hx1
  -- `16 ≤ x^{1/16}` since `16^{16} = 2^{64} ≤ x`
  have h16 : (16 : ℝ) ≤ (x : ℝ) ^ (1 / 16 : ℝ) := by
    have h264 : (2 : ℕ) ^ 64 ≤ 2 ^ 504 :=
      pow_le_pow_right' (by norm_num) (by norm_num)
    have h1616 : (16 : ℕ) ^ 16 = 2 ^ 64 := by norm_num
    have hpow : ((16 ^ 16 : ℕ) : ℝ) ≤ (x : ℝ) := by
      have h' : (16 : ℕ) ^ 16 ≤ x := le_trans (h1616 ▸ h264) hxge
      exact_mod_cast h'
    have heq : (16 : ℝ) = ((16 ^ 16 : ℕ) : ℝ) ^ (1 / 16 : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16),
        show ((16 : ℕ) : ℝ) * (1 / 16) = (1 : ℝ) by norm_num,
        Real.rpow_one]
    conv_lhs => rw [heq]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpow
      (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  -- `log x ≤ x^{1/8}`
  have hlogx : Real.log x ≤ (x : ℝ) ^ (1 / 8 : ℝ) := by
    have h1 : Real.log x = 16 * Real.log ((x : ℝ) ^ (1 / 16 : ℝ)) := by
      have h := Real.log_rpow hxpos (1 / 16 : ℝ)
      linarith
    have h2 : Real.log ((x : ℝ) ^ (1 / 16 : ℝ)) ≤ (x : ℝ) ^ (1 / 16 : ℝ) :=
      (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxpos _)).trans
        (sub_le_self _ zero_le_one)
    calc Real.log x = 16 * Real.log ((x : ℝ) ^ (1 / 16 : ℝ)) := h1
      _ ≤ 16 * (x : ℝ) ^ (1 / 16 : ℝ) := by linarith [h2]
      _ ≤ (x : ℝ) ^ (1 / 16 : ℝ) * (x : ℝ) ^ (1 / 16 : ℝ) :=
          mul_le_mul h16 (le_refl _)
            (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ (1 / 16 + 1 / 16 : ℝ) := by rw [← Real.rpow_add hxpos]
      _ = (x : ℝ) ^ (1 / 8 : ℝ) := by congr 1; norm_num
  -- `(log x)² ≤ x^{1/4}`
  have hnn : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  have hlog2 : (Real.log x) ^ 2 ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    calc (Real.log x) ^ 2 = Real.log x * Real.log x := pow_two _
      _ ≤ (x : ℝ) ^ (1 / 8 : ℝ) * (x : ℝ) ^ (1 / 8 : ℝ) :=
          mul_le_mul hlogx hlogx hnn (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ (1 / 8 + 1 / 8 : ℝ) := by rw [← Real.rpow_add hxpos]
      _ = (x : ℝ) ^ (1 / 4 : ℝ) := by congr 1; norm_num
  -- `x^{3/4} ≤ x·(log x)⁻²`
  have hkey : (x : ℝ) ^ (3 / 4 : ℝ) * (Real.log x) ^ 2 ≤ x := by
    calc (x : ℝ) ^ (3 / 4 : ℝ) * (Real.log x) ^ 2
        ≤ (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul (le_refl _) hlog2 (sq_nonneg _)
            (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ (3 / 4 + 1 / 4 : ℝ) := by rw [← Real.rpow_add hxpos]
      _ = x := by rw [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
  have hshape : (x : ℝ) * (Real.log x) ^ (-2 : ℝ) =
      (x : ℝ) / (Real.log x) ^ 2 := by
    rw [div_eq_mul_inv, Real.rpow_neg hnn,
      show (Real.log x) ^ (2 : ℝ) = (Real.log x) ^ 2 from
        Real.rpow_natCast _ _]
  refine hx.trans ?_
  rw [hshape]
  exact (le_div_iff₀ (pow_pos (Real.log_pos hx1) 2)).mpr hkey

end Payoff

end JSP314
