import JSP314.RunMultiplicity
import JSP314.ErdosTk

/-!
# JSP-000314 — bounds on the pair-quotient counts

This file bounds the quotient counts introduced in `JSP314.RunMultiplicity`:

* `rightPairQuotCount x p`
    `= #{r ≤ 2x / p² : largestPrimeFactor (p²·r + 1) ≤ p}`,
* `leftPairQuotCount x p`
    `= #{r ≤ 2x / p² : largestPrimeFactor (p²·r − 1) ≤ p}`.

These count `p`-smooth values of the arithmetic progression `p²·r ± 1`, so the
Erdős valuation bound of `JSP314.ErdosTk` (`apSmoothParamCount`,
`apSmoothParamCount_mul_log_le_explicit`) applies directly.

## What is proved

* `rightPairQuotCount_le`, `leftPairQuotCount_le` — the trivial bound
  `≤ 2x/p² + 1`.
* `rightPairQuotCount_eq_apSmoothParamCount` — bridge to the Erdős count.
* `rightPairQuotCount_le_add_add`, `leftPairQuotCount_le_add_add` —
  two-level split: for every `R`, the count is at most
  `1 + R + apSmoothParamCount (R+1) B (p²) 1 p` (right) resp.
  `1 + R + apSmoothParamCount R (B−1) (p²) (p²−1) p` (left).
* `rightPairQuotCount_le_erdos`, `leftPairQuotCount_le_erdos` — the explicit
  Erdős bounds
  `rightPairQuotCount x p ≤ 1 + (B·(2 log p + 11) + C)/log (p² + 1)`,
  `leftPairQuotCount x p ≤ 1 + (B·(2 log p + 11) + C)/log (p² − 1)`,
  where `C` is a lower-order `p·log 4·log₂(2x+1)` term.
* `rightPairQuotCount_le_two_level`, `leftPairQuotCount_le_two_level` —
  for every `R`, `≤ 1 + R + (B·A + C)/(2 log p + log (R+1))` (right) and the
  analogous bound with denominator `2 log p + log (R+1) − log 2` (left).
  Choosing `R` near `B·A/log B` gives a genuine `log p / log B` saving:
* `rightPairQuotCount_le_log_saving`, `leftPairQuotCount_le_log_saving` —
  provided `B ≥ 16` (right) resp. `B ≥ 256` (left) and the lower-order term is
  dominated (`4C ≤ B·A`),
  `rightPairQuotCount x p ≤ 2 + B·(12·log p + 66)/log B`.
* `rightPairQuotCount_le_rpow_neg`, `leftPairQuotCount_le_rpow_neg` — the same
  bound written `≤ 2·B·(p:ℝ)^(−c)` with the *explicit* exponent
  `c = log (log B / (12 log p + 66)) / log p`, which is positive whenever
  `12 log p + 66 < log B` (`pairQuot_saving_exp_pos`).

## Honest note on the gap

For `p` in the band `exp(√(L·L₂)/2) < p ≤ x^{1/4}` (where
`B = 2x/p²`, `log B ≈ L − 2 log p`), the saving factor obtained is
`≈ (12·log p)/log B` — polynomial in `u = log B/log p`, i.e.
`≈ 12/u`.  Written as `(p:ℝ)^(−c)` the exponent is
`c ≍ log u / log p → 0`; in particular `c` is *not* bounded below by a fixed
positive constant on this band, so summing `p·(right+left)` over the band
still gives `O(x)`-scale control rather than the `x·exp(−c·s)` required by
`BandSum.hN_of_runCountSum_le`.  Closing that gap needs input beyond the
elementary Erdős valuation bound (e.g. `ρ(u)`-type estimates for smooth
numbers in the residue class `1 mod p²`).  All bounds below are unconditional
and proved.
-/

namespace JSP314

open Finset

section Bridge

/-- `range (B + 1) = Icc 0 B`. -/
theorem range_succ_eq_Icc_zero (B : ℕ) :
    Finset.range (B + 1) = Finset.Icc 0 B := by
  ext r
  simp

/-- The right quotient witnesses, over the interval `Icc 0 B`. -/
theorem rightPairQuotWitness_eq (x p : ℕ) :
    rightPairQuotWitness x p = (Finset.Icc 0 (2 * x / p ^ 2)).filter
      (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p) := by
  unfold rightPairQuotWitness
  rw [range_succ_eq_Icc_zero]

/-- The left quotient witnesses, over the interval `Icc 0 B`. -/
theorem leftPairQuotWitness_eq (x p : ℕ) :
    leftPairQuotWitness x p = (Finset.Icc 0 (2 * x / p ^ 2)).filter
      (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p) := by
  unfold leftPairQuotWitness
  rw [range_succ_eq_Icc_zero]

/-- The right quotient count is exactly the Erdős AP-smooth count on
`[0, B]` with `c = p²`, `j = 1`. -/
theorem rightPairQuotCount_eq_apSmoothParamCount (x p : ℕ) :
    rightPairQuotCount x p =
      apSmoothParamCount 0 (2 * x / p ^ 2) (p ^ 2) 1 p := by
  unfold rightPairQuotCount apSmoothParamCount
  rw [rightPairQuotWitness_eq]

end Bridge

section Trivial

/-- **Trivial bound (right):** the witness set is contained in
`range (2x/p² + 1)`. -/
theorem rightPairQuotCount_le (x p : ℕ) :
    rightPairQuotCount x p ≤ 2 * x / p ^ 2 + 1 := by
  unfold rightPairQuotCount rightPairQuotWitness
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- **Trivial bound (left).** -/
theorem leftPairQuotCount_le (x p : ℕ) :
    leftPairQuotCount x p ≤ 2 * x / p ^ 2 + 1 := by
  unfold leftPairQuotCount leftPairQuotWitness
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

end Trivial

section Split

/-- **Two-level split (right).**  Splitting `Icc 0 B` at `R`: the part
`r ≤ R` contributes at most `1 + R`, the part `r ≥ R + 1` is the Erdős
count on `Icc (R+1) B` with `c = p²`, `j = 1` (coprime trivially). -/
theorem rightPairQuotCount_le_add_add (x p R : ℕ) :
    rightPairQuotCount x p ≤ 1 + R +
      apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p := by
  rw [rightPairQuotCount_eq_apSmoothParamCount]
  set B := 2 * x / p ^ 2 with hB
  have hsub : (Finset.Icc 0 B).filter
        (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p) ⊆
      ({0} ∪ Finset.Icc 1 R) ∪
        (Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨_, hrB⟩, hlpf⟩ := hr
    rcases le_or_gt r R with hle | hgt
    · rcases Nat.eq_zero_or_pos r with h0 | h1
      · subst h0
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_singleton_self 0))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_Icc.mpr ⟨h1, hle⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hgt, hrB⟩, hlpf⟩)
  refine (Finset.card_le_card hsub).trans ?_
  calc ((({0} ∪ Finset.Icc 1 R) ∪
          (Finset.Icc (R + 1) B).filter
            (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)) : Finset ℕ).card
      ≤ ({0} ∪ Finset.Icc 1 R).card +
        ((Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)).card :=
        Finset.card_union_le _ _
    _ ≤ (1 + R) +
        ((Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)).card :=
        Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans
            (by rw [Finset.card_singleton, Nat.card_Icc]; omega)) _
    _ = 1 + R + apSmoothParamCount (R + 1) B (p ^ 2) 1 p := rfl

/-- **Two-level split (left).**  For `p ≥ 2`, `r ↦ r − 1` sends the part
`r ≥ R + 1` of the left witness set into the Erdős count on `Icc R (B−1)`
with `c = p²`, `j = p² − 1` (note `p²(r−1) + (p²−1) = p²r − 1` for `r ≥ 1`). -/
theorem leftPairQuotCount_le_add_add (x p R : ℕ) (hp : 2 ≤ p) :
    leftPairQuotCount x p ≤ 1 + R +
      apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p := by
  unfold leftPairQuotCount
  rw [leftPairQuotWitness_eq]
  set B := 2 * x / p ^ 2 with hB
  have hp2 : 4 ≤ p ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  have hsub : (Finset.Icc 0 B).filter
        (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p) ⊆
      ({0} ∪ Finset.Icc 1 R) ∪
        (Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    obtain ⟨⟨_, hrB⟩, hlpf⟩ := hr
    rcases le_or_gt r R with hle | hgt
    · rcases Nat.eq_zero_or_pos r with h0 | h1
      · subst h0
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_singleton_self 0))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_Icc.mpr ⟨h1, hle⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hgt, hrB⟩, hlpf⟩)
  have hinj : ((Finset.Icc (R + 1) B).filter
        (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)).card ≤
      apSmoothParamCount R (B - 1) (p ^ 2) (p ^ 2 - 1) p := by
    refine Finset.card_le_card_of_injOn (fun r => r - 1) ?_ ?_
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hr
      obtain ⟨⟨hrR, hrB⟩, hlpf⟩ := hr
      have hr1 : 1 ≤ r := by omega
      have hkey : p ^ 2 * (r - 1) + (p ^ 2 - 1) = p ^ 2 * r - 1 := by
        have h : p ^ 2 * (r - 1) + p ^ 2 = p ^ 2 * r := by
          conv_rhs => rw [show r = r - 1 + 1 from (Nat.sub_add_cancel hr1).symm]
          rw [mul_add, mul_one]
        omega
      rw [Finset.mem_coe]
      show r - 1 ∈ (Finset.Icc R (B - 1)).filter
        (fun s => largestPrimeFactor (p ^ 2 * s + (p ^ 2 - 1)) ≤ p)
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [hkey]
      exact hlpf
    · intro a ha b hb hab
      change a - 1 = b - 1 at hab
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at ha hb
      omega
  refine (Finset.card_le_card hsub).trans ?_
  calc ((({0} ∪ Finset.Icc 1 R) ∪
          (Finset.Icc (R + 1) B).filter
            (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)) : Finset ℕ).card
      ≤ ({0} ∪ Finset.Icc 1 R).card +
        ((Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)).card :=
        Finset.card_union_le _ _
    _ ≤ (1 + R) +
        ((Finset.Icc (R + 1) B).filter
          (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)).card :=
        Nat.add_le_add_right
          ((Finset.card_union_le _ _).trans
            (by rw [Finset.card_singleton, Nat.card_Icc]; omega)) _
    _ ≤ (1 + R) + apSmoothParamCount R (B - 1) (p ^ 2) (p ^ 2 - 1) p :=
        Nat.add_le_add_left hinj _

end Split

section Coprime

/-- `p²` and `p² − 1` are coprime (needed to apply the Erdős bound to the
left progression `p²·s + (p² − 1)`). -/
theorem coprime_sq_sub_one {p : ℕ} (hp : 2 ≤ p) :
    Nat.Coprime (p ^ 2) (p ^ 2 - 1) := by
  have h1 : 1 ≤ p ^ 2 := by
    calc (1 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  rw [Nat.coprime_self_sub_right h1]
  exact (Nat.coprime_one_right_iff _).mpr trivial

end Coprime

section Erdos

/-- **Erdős bound (right).**  `p²` and `1` are coprime, so
`apSmoothParamCount_mul_log_le_explicit` on `Icc 1 B` gives

`rightPairQuotCount x p ≤ 1 + (B·(2 log p + 11) + log₂(2x+1)·p·log 4)/log (p²+1)`. -/
theorem rightPairQuotCount_le_erdos (x p : ℕ) (hp : 2 ≤ p) :
    (rightPairQuotCount x p : ℝ) ≤
      1 + (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
          (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4)) /
        Real.log ((p : ℝ) ^ 2 + 1) := by
  have hsplit : rightPairQuotCount x p ≤ 1 +
      apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p := by
    have h := rightPairQuotCount_le_add_add x p 0
    rwa [zero_add, add_zero] at h
  have hcop : Nat.Coprime (p ^ 2) 1 := (Nat.coprime_one_right_iff _).mpr trivial
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := 1)
    (hi := 2 * x / p ^ 2) (c := p ^ 2) (j := 1) (p := p) hcop (by omega)
  have hB1 : ((2 * x / p ^ 2 - 1 : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  have hp2B : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := Nat.mul_div_le _ _
  have hlog2 : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + 1) : ℝ) ≤
      (Nat.log 2 (2 * x + 1) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right (by omega))
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hlogpos : 0 < Real.log ((p : ℝ) ^ 2 + 1) :=
    Real.log_pos (by
      have h : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos (by linarith) 2
      linarith)
  have hlog_eq : Real.log ((p ^ 2 * 1 + 1 : ℕ) : ℝ) =
      Real.log ((p : ℝ) ^ 2 + 1) := by
    congr 1
    push_cast
    ring
  rw [hlog_eq] at hE
  have hap : (apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
        (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4)) /
        Real.log ((p : ℝ) ^ 2 + 1) := by
    rw [le_div_iff₀ hlogpos]
    refine hE.trans ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_right hB1 (by positivity))
      (mul_le_mul_of_nonneg_right hlog2 (by positivity))
  calc (rightPairQuotCount x p : ℝ)
      ≤ 1 + (apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) := by
        exact_mod_cast hsplit
    _ ≤ _ := add_le_add_right hap 1

/-- **Erdős bound (left).**  Writing `p²r − 1 = p²(r−1) + (p²−1)`, the count
is `≤ 1 + apSmoothParamCount 0 (B−1) (p²) (p²−1) p`, and `p², p²−1` are
coprime, so

`leftPairQuotCount x p ≤ 1 + (B·(2 log p + 11) + log₂(2x)·p·log 4)/log (p²−1)`. -/
theorem leftPairQuotCount_le_erdos (x p : ℕ) (hp : 2 ≤ p)
    (hB : 1 ≤ 2 * x / p ^ 2) :
    (leftPairQuotCount x p : ℝ) ≤
      1 + (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
          (Nat.log 2 (2 * x) : ℝ) * (p * Real.log 4)) /
        Real.log ((p : ℝ) ^ 2 - 1) := by
  have hsplit : leftPairQuotCount x p ≤ 1 +
      apSmoothParamCount 0 (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p := by
    have h := leftPairQuotCount_le_add_add x p 0 hp
    rwa [add_zero] at h
  have hcop : Nat.Coprime (p ^ 2) (p ^ 2 - 1) := coprime_sq_sub_one hp
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := 0)
    (hi := 2 * x / p ^ 2 - 1) (c := p ^ 2) (j := p ^ 2 - 1) (p := p)
    hcop (by omega)
  have hp2 : 4 ≤ p ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  have hB1 : ((2 * x / p ^ 2 - 1 - 0 : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  -- `p²·(B−1) + (p²−1) = p²·B − 1 ≤ 2x`
  have haux : p ^ 2 * (2 * x / p ^ 2 - 1) + (p ^ 2 - 1) ≤ 2 * x := by
    have h : p ^ 2 * (2 * x / p ^ 2 - 1) + p ^ 2 = p ^ 2 * (2 * x / p ^ 2) := by
      conv_rhs => rw [show 2 * x / p ^ 2 = 2 * x / p ^ 2 - 1 + 1 from
        (Nat.sub_add_cancel hB).symm]
      rw [mul_add, mul_one]
    have hle := Nat.mul_div_le (2 * x) (p ^ 2)
    omega
  have hlog2 : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2 - 1) + (p ^ 2 - 1)) : ℝ) ≤
      (Nat.log 2 (2 * x) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right haux)
  have hlogpos : 0 < Real.log ((p : ℝ) ^ 2 - 1) := by
    apply Real.log_pos
    have hp2R : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by
      have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      nlinarith [mul_nonneg (sub_nonneg.mpr hp')
        (show (0 : ℝ) ≤ p + 2 by positivity)]
    linarith
  have hlog_eq : Real.log ((p ^ 2 * 0 + (p ^ 2 - 1) : ℕ) : ℝ) =
      Real.log ((p : ℝ) ^ 2 - 1) := by
    congr 1
    rw [show p ^ 2 * 0 + (p ^ 2 - 1) = p ^ 2 - 1 by omega]
    rw [Nat.cast_sub (by omega : 1 ≤ p ^ 2)]
    push_cast
    ring
  rw [hlog_eq] at hE
  have hap : (apSmoothParamCount 0 (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
        (Nat.log 2 (2 * x) : ℝ) * (p * Real.log 4)) /
        Real.log ((p : ℝ) ^ 2 - 1) := by
    rw [le_div_iff₀ hlogpos]
    refine hE.trans ?_
    exact add_le_add
      (mul_le_mul_of_nonneg_right hB1 (by positivity))
      (mul_le_mul_of_nonneg_right hlog2 (by positivity))
  calc (leftPairQuotCount x p : ℝ)
      ≤ 1 + (apSmoothParamCount 0 (2 * x / p ^ 2 - 1) (p ^ 2)
          (p ^ 2 - 1) p : ℝ) := by
        exact_mod_cast hsplit
    _ ≤ _ := add_le_add_right hap 1

end Erdos

section TwoLevel

/-- **Two-level bound (right).**  For every `R`, splitting at `r = R` and
using the Erdős bound on the tail gives

`rightPairQuotCount x p ≤ 1 + R + (B·A + C)/(2 log p + log (R+1))`

where `A = 2 log p + 11` and `C = log₂(2x+1)·p·log 4`. -/
theorem rightPairQuotCount_le_two_level (x p : ℕ) (hp : 2 ≤ p) (R : ℕ) :
    (rightPairQuotCount x p : ℝ) ≤
      1 + (R : ℝ) +
        (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
          (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4)) /
          (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1)) := by
  have hsplit := rightPairQuotCount_le_add_add x p R
  have hcop : Nat.Coprime (p ^ 2) 1 := (Nat.coprime_one_right_iff _).mpr trivial
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := R + 1)
    (hi := 2 * x / p ^ 2) (c := p ^ 2) (j := 1) (p := p) hcop (by omega)
  have hB1 : ((2 * x / p ^ 2 - (R + 1) : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le _ _)
  have hp2B : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := Nat.mul_div_le _ _
  have hlog2 : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2) + 1) : ℝ) ≤
      (Nat.log 2 (2 * x + 1) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right (by omega))
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  -- Denominator bound: `log (p²(R+1)+1) ≥ 2 log p + log (R+1)`.
  have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos (by linarith) 2
  have hR1pos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hcast : ((p ^ 2 * (R + 1) + 1 : ℕ) : ℝ) =
      (p : ℝ) ^ 2 * ((R : ℝ) + 1) + 1 := by push_cast; ring
  have hlogeq : Real.log ((p : ℝ) ^ 2 * ((R : ℝ) + 1)) =
      2 * Real.log p + Real.log ((R : ℝ) + 1) := by
    rw [Real.log_mul hp2pos.ne' hR1pos.ne', Real.log_pow]
    push_cast
    ring
  have hlogge : 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) ≤
      Real.log ((p ^ 2 * (R + 1) + 1 : ℕ) : ℝ) := by
    rw [hcast]
    calc 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1)
        = Real.log ((p : ℝ) ^ 2 * ((R : ℝ) + 1)) := hlogeq.symm
      _ ≤ Real.log ((p : ℝ) ^ 2 * ((R : ℝ) + 1) + 1) :=
          Real.log_le_log (by positivity) (by linarith)
  have hDpos : 0 < 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) := by
    have h1 : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
    have h2 : 0 ≤ Real.log ((R : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  have hap : (apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
        (Nat.log 2 (2 * x + 1) : ℝ) * (p * Real.log 4)) /
        (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1)) := by
    rw [le_div_iff₀ hDpos]
    have hapos : (0 : ℝ) ≤
        (apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) :=
      Nat.cast_nonneg _
    calc (apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) *
          (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1))
        ≤ (apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) *
          Real.log ((p ^ 2 * (R + 1) + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlogge hapos
      _ ≤ _ := hE.trans
          (add_le_add
            (mul_le_mul_of_nonneg_right hB1 (by positivity))
            (mul_le_mul_of_nonneg_right hlog2 (by positivity)))
  calc (rightPairQuotCount x p : ℝ)
      ≤ 1 + (R : ℝ) +
        (apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2) 1 p : ℝ) := by
        have h : (rightPairQuotCount x p : ℝ) ≤
            (1 + R + apSmoothParamCount (R + 1) (2 * x / p ^ 2) (p ^ 2)
              1 p : ℕ) := by exact_mod_cast hsplit
        push_cast at h
        linarith
    _ ≤ _ := add_le_add_right hap _

/-- **Two-level bound (left).**  For every `R`, the shifted count
`apSmoothParamCount R (B−1) (p²) (p²−1) p` has log-weight
`log (p²·R + (p²−1)) ≥ 2 log p + log (R+1) − log 2`. -/
theorem leftPairQuotCount_le_two_level (x p : ℕ) (hp : 2 ≤ p)
    (hB : 1 ≤ 2 * x / p ^ 2) (R : ℕ) :
    (leftPairQuotCount x p : ℝ) ≤
      1 + (R : ℝ) +
        (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
          (Nat.log 2 (2 * x) : ℝ) * (p * Real.log 4)) /
          (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2) := by
  have hsplit := leftPairQuotCount_le_add_add x p R hp
  have hcop : Nat.Coprime (p ^ 2) (p ^ 2 - 1) := coprime_sq_sub_one hp
  have hE := apSmoothParamCount_mul_log_le_explicit (lo := R)
    (hi := 2 * x / p ^ 2 - 1) (c := p ^ 2) (j := p ^ 2 - 1) (p := p)
    hcop (by omega)
  have hp2 : 4 ≤ p ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
  have hB1 : ((2 * x / p ^ 2 - 1 - R : ℕ) : ℝ) ≤ ((2 * x / p ^ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  have haux : p ^ 2 * (2 * x / p ^ 2 - 1) + (p ^ 2 - 1) ≤ 2 * x := by
    have h : p ^ 2 * (2 * x / p ^ 2 - 1) + p ^ 2 = p ^ 2 * (2 * x / p ^ 2) := by
      conv_rhs => rw [show 2 * x / p ^ 2 = 2 * x / p ^ 2 - 1 + 1 from
        (Nat.sub_add_cancel hB).symm]
      rw [mul_add, mul_one]
    have hle := Nat.mul_div_le (2 * x) (p ^ 2)
    omega
  have hlog2 : (Nat.log 2 (p ^ 2 * (2 * x / p ^ 2 - 1) + (p ^ 2 - 1)) : ℝ) ≤
      (Nat.log 2 (2 * x) : ℝ) :=
    Nat.cast_le.mpr (Nat.log_mono_right haux)
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  -- Denominator bound:
  -- `log (p²R + (p²−1)) ≥ log (p²(R+1)/2) = 2 log p + log (R+1) − log 2`.
  have hp2pos : (0 : ℝ) < (p : ℝ) ^ 2 := pow_pos (by linarith) 2
  have hR1pos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hcast : ((p ^ 2 * R + (p ^ 2 - 1) : ℕ) : ℝ) =
      (p : ℝ) ^ 2 * (R : ℝ) + ((p : ℝ) ^ 2 - 1) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (by omega : 1 ≤ p ^ 2)]
    push_cast
    ring
  have hlogeq : Real.log ((p : ℝ) ^ 2 * ((R : ℝ) + 1) / 2) =
      2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2 := by
    rw [Real.log_div (mul_ne_zero hp2pos.ne' hR1pos.ne') (by norm_num),
      Real.log_mul hp2pos.ne' hR1pos.ne', Real.log_pow]
    push_cast
    ring
  have hlogge : 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2 ≤
      Real.log ((p ^ 2 * R + (p ^ 2 - 1) : ℕ) : ℝ) := by
    rw [hcast]
    have hhalf : (p : ℝ) ^ 2 * ((R : ℝ) + 1) / 2 ≤
        (p : ℝ) ^ 2 * (R : ℝ) + ((p : ℝ) ^ 2 - 1) := by
      have h4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by
        have hp' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
        nlinarith [mul_nonneg (sub_nonneg.mpr hp')
          (show (0 : ℝ) ≤ p + 2 by positivity)]
      have hR' : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2
        = Real.log ((p : ℝ) ^ 2 * ((R : ℝ) + 1) / 2) := hlogeq.symm
      _ ≤ Real.log ((p : ℝ) ^ 2 * (R : ℝ) + ((p : ℝ) ^ 2 - 1)) :=
          Real.log_le_log (by positivity) hhalf
  have hDpos : 0 < 2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) -
      Real.log 2 := by
    have h1 : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hpR
    have h2 : 0 ≤ Real.log ((R : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h3 : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
    linarith
  have hap : (apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2)
        (p ^ 2 - 1) p : ℝ) ≤
      (((2 * x / p ^ 2 : ℕ) : ℝ) * (2 * Real.log p + 11) +
        (Nat.log 2 (2 * x) : ℝ) * (p * Real.log 4)) /
        (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2) := by
    rw [le_div_iff₀ hDpos]
    have hapos : (0 : ℝ) ≤
        (apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p : ℝ) :=
      Nat.cast_nonneg _
    calc (apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p : ℝ) *
          (2 * Real.log (p : ℝ) + Real.log ((R : ℝ) + 1) - Real.log 2)
        ≤ (apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2)
            (p ^ 2 - 1) p : ℝ) *
          Real.log ((p ^ 2 * R + (p ^ 2 - 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlogge hapos
      _ ≤ _ := hE.trans
          (add_le_add
            (mul_le_mul_of_nonneg_right hB1 (by positivity))
            (mul_le_mul_of_nonneg_right hlog2 (by positivity)))
  calc (leftPairQuotCount x p : ℝ)
      ≤ 1 + (R : ℝ) +
        (apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2) (p ^ 2 - 1) p : ℝ) := by
        have h : (leftPairQuotCount x p : ℝ) ≤
            (1 + R + apSmoothParamCount R (2 * x / p ^ 2 - 1) (p ^ 2)
              (p ^ 2 - 1) p : ℕ) := by exact_mod_cast hsplit
        push_cast at h
        linarith
    _ ≤ _ := add_le_add_right hap _

end TwoLevel

end JSP314
