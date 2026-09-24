import JSP314.AntiSieve
import JSP314.FreshEye2
import JSP314.RatioGlue
import Mathlib.Tactic

/-!
# JSP-000314 — anti-sieve, part 2: the `−1 (mod p²)` class, the
diagonal/tail split of `runCountSum`, and the conditional closure

This file continues `JSP314.AntiSieve` and shrinks the wall around the sole
remaining placeholder `badNonSingleton_interval_bound` (`JSP314/Main.lean`)
to a minimal, explicitly-named set of analytic hypotheses.

## Unconditional additions

* **Run-length monotonicity** (`rightRunWitness_subset_one`,
  `rightRunCount_le_one`, `leftRunWitness_subset_one`, `leftRunCount_le_one`):
  level-`k` run witnesses are level-`1` witnesses (already in `FreshEye2` as
  `rightRunWitness_anti` etc.; restated here in the form the reduction uses).
* **The left (`≡ −1`) anti-sieve class** `smoothCongruentNegOne N p`: the
  `p`-smooth `s ∈ [2, N]` with `p² ∣ s + 1`.  The mirror of the `+1`
  development gives `leftRunCount_one_le_smoothCongruentNegOne`,
  the cofactor anatomy `cofactorFinsetNeg`, fiber uniqueness
  (`cofactorPairNeg_q_unique`, reusing the general-class cancellation lemma
  `modEq_of_mul_modEq_of_coprime` with `c = p² − 1`), the Rankin recovery
  `leftRunCount_one_le_smoothCount : L₁ ≤ Ψ(2x+1, p−1)`, and the explicit
  bound `leftRunCount_one_le_real : L₁ ≤ (2x+1)/p²·(1 + log(p−1)) + p`.
* **Diagonal/tail split** (`runCountSum_eq_diag_add_tail`):
  `runCountSum x = runDiagSum x + runTailSum x` where `runDiagSum` is the
  `k = 1` diagonal and `runTailSum` is the `k ≥ 2` tail.  This is the sharp
  structural split: `FreshEye.sum_rightRunCount_one_le_shortBadCount` shows
  the diagonal is *tight* (`∑_p R₁ ≤ T_short(2x)`), so all the excess lives
  in the tail.
* `sum_runCount_one_le_two_mul_shortBadCount` — both diagonals together are
  bounded by twice the true covered count.

## The conditional closures

The hypothesis set is organised as three independent, individually-meaningful
inputs (`SmoothEquidistHyp`, `SmoothSqWeightHyp`, `LongRunTailHyp`), followed
by two alternatives (`SmoothWeightHyp`, the `Ψ/p`-weight needed by the cruder
`2p·T₁` diagonal collapse; and the banded `SmallBandEquidistHyp` +
`SmallBandWeightHyp` + `LargeBandRunTailHyp` split suggested for the large-`p`
regime):

* `SmoothEquidistHyp` — the **anti-sieve input proper** (Ta26c
  Props 6.6–6.8): for every prime `p ≤ √(2x)`, the `p`-smooth integers
  `≡ ±1 (mod p²)` in the relevant range number
  `≪ Ψ(2x+1, p)/p²·(log log x)^K` — `p`-smooth numbers equidistribute into
  the coprime classes `mod p²`.  This is the hypothesis the task isolates.
* `SmoothSqWeightHyp` — the **global comparison**
  `∑_{p ≤ √(2x)} Ψ(2x+1, p)/p² ≪ S(x)·(log x)^{-1}·(log log x)^K`:
  the `1/p²`-weighted smooth sum sits on the same `z`-scale saddle as
  `S(x)` itself, with the `ρ(u)/ρ(u−2) ≍ (u log u)^{-2}` saving supplying the
  needed `(log x)^{-1}` factor.
* `LongRunTailHyp` — the **run-length tail**
  `∑_p ∑_{k = 2}^{2p} (R_k + L_k) ≪ S(x)·(log x)^{-1}·(log log x)^K`:
  runs of `p`-smooth integers of length `≥ 2` through `p²`-multiples are
  rare — the second-moment / Størmer-type input.

Under `SmoothEquidistHyp + SmoothSqWeightHyp + LongRunTailHyp`,
`badNonSingleton_interval_bound_of_antiSieve_hyps` proves the residual
statement of `Main.lean`.  The logical content:

```
runCountSum = runDiagSum + runTailSum
            ≤ (C·(loglog)^{K₁})·∑_p Ψ/p²   +   tail          [equidist, k=1]
            ≤ C·(loglog)^{K₁}·S·L^{-1}·(loglog)^{K₂} + S·L^{-1}·(loglog)^{K₃}
            ≤ S·L^{-1}·(loglog)^{K'}
```

and `FreshEye.badNonSingleton_interval_bound_of_runCountSum_loglog` closes.
-/

namespace JSP314

open Finset Filter Classical

/-! ### Run-length monotonicity (subset form) -/

/-- Runs of length `≥ k` are a subset of runs of length `≥ 1`: the condition
"`m+1,…,m+k` all `p`-smooth" entails "`m+1` `p`-smooth". -/
theorem rightRunWitness_subset_one {x p k : ℕ} (hk : 1 ≤ k) :
    rightRunWitness x p k ⊆ rightRunWitness x p 1 :=
  rightRunWitness_anti hk

/-- Count form: `rightRunCount x p k ≤ rightRunCount x p 1` for `k ≥ 1`. -/
theorem rightRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    rightRunCount x p k ≤ rightRunCount x p 1 :=
  rightRunCount_anti hk

/-- The left analogue of `rightRunWitness_subset_one`. -/
theorem leftRunWitness_subset_one {x p k : ℕ} (hk : 1 ≤ k) :
    leftRunWitness x p k ⊆ leftRunWitness x p 1 :=
  leftRunWitness_anti hk

/-- Count form: `leftRunCount x p k ≤ leftRunCount x p 1` for `k ≥ 1`. -/
theorem leftRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    leftRunCount x p k ≤ leftRunCount x p 1 :=
  leftRunCount_anti hk

/-! ### The `≡ −1 (mod p²)` anti-sieve set -/

/-- **The `−1` anti-sieve target**: `p`-smooth `s ∈ [2, N]` with
`p² ∣ s + 1` (i.e. `s ≡ −1 (mod p²)`).  Counting this set at
`N = p²·(2x/p²) + 1` bounds `leftRunCount x p 1` via `r = m/p² ↦ m − 1`
(`leftRunCount_one_le_smoothCongruentNegOne`). -/
def smoothCongruentNegOne (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun s =>
    largestPrimeFactor s ≤ p ∧ p ^ 2 ∣ s + 1

theorem mem_smoothCongruentNegOne {N p s : ℕ} :
    s ∈ smoothCongruentNegOne N p ↔
      2 ≤ s ∧ s ≤ N ∧ largestPrimeFactor s ≤ p ∧ p ^ 2 ∣ s + 1 := by
  simp only [smoothCongruentNegOne, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Monotonicity of `smoothCongruentNegOne` in the ambient bound. -/
theorem smoothCongruentNegOne_mono {N₁ N₂ p : ℕ} (h : N₁ ≤ N₂) :
    smoothCongruentNegOne N₁ p ⊆ smoothCongruentNegOne N₂ p := by
  intro s hs
  obtain ⟨hs2, hsN, hlp, hmod⟩ := mem_smoothCongruentNegOne.mp hs
  exact mem_smoothCongruentNegOne.mpr ⟨hs2, hsN.trans h, hlp, hmod⟩

/-- For a `k = 1` left run witness `m`, `s = m − 1 = p²·(m/p²) − 1` lies in
the `−1` anti-sieve set at `N = p²·(2x/p²) + 1`. -/
theorem leftRunWitness_one_pred_mem {x p m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ leftRunWitness x p 1) :
    m - 1 ∈ smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p := by
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsm⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hm1 hdvd
  have hm4 : 4 ≤ m := (Nat.pow_le_pow_left hp.two_le 2).trans hpm
  have hmle : m ≤ p ^ 2 * (2 * x / p ^ 2) := by
    conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
    exact Nat.mul_le_mul_left _ (Nat.div_le_div_right hm2x)
  rw [mem_smoothCongruentNegOne]
  refine ⟨by omega, by omega,
    hsm (m - 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩), ?_⟩
  rwa [Nat.sub_add_cancel hm1]

/-- **Bridge (left):** `leftRunCount x p 1 ≤ |smoothCongruentNegOne
(p²·(2x/p²)+1) p|` via `m ↦ m − 1`. -/
theorem leftRunCount_one_le_smoothCongruentNegOne {x p : ℕ}
    (hp : Nat.Prime p) :
    leftRunCount x p 1 ≤
      (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card := by
  classical
  apply Finset.card_le_card_of_injOn (· - 1)
  · intro m hm
    rw [Finset.mem_coe]
    exact leftRunWitness_one_pred_mem hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    have ha1 : 1 ≤ a :=
      witness_pos hp (mem_leftRunWitness.mp (Finset.mem_coe.mp ha)).2.1
        (mem_leftRunWitness.mp (Finset.mem_coe.mp ha)).2.2.1
    have hb1 : 1 ≤ b :=
      witness_pos hp (mem_leftRunWitness.mp (Finset.mem_coe.mp hb)).2.1
        (mem_leftRunWitness.mp (Finset.mem_coe.mp hb)).2.2.1
    omega

/-- The ambient-bound `2x + 1` version of the left bridge. -/
theorem leftRunCount_one_le_smoothCongruentNegOne' {x p : ℕ}
    (hp : Nat.Prime p) :
    leftRunCount x p 1 ≤ (smoothCongruentNegOne (2 * x + 1) p).card := by
  refine (leftRunCount_one_le_smoothCongruentNegOne hp).trans
    (Finset.card_le_card (smoothCongruentNegOne_mono ?_))
  have h : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := by
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  omega

/-! ### The `−1` cofactor anatomy -/

/-- `K ∣ s + 1` iff `s ≡ K − 1 (mod K)` (for `K ≥ 1`). -/
theorem modEq_pred_one_of_dvd_succ {s K : ℕ} (hK : 1 ≤ K) (h : K ∣ s + 1) :
    s ≡ K - 1 [MOD K] := by
  obtain ⟨t, ht⟩ := h
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      rw [h0, mul_zero] at ht
      omega
    · exact h0
  have hle : K ≤ s + 1 := by rw [ht]; exact Nat.le_mul_of_pos_right _ ht1
  have hseq : s = (K - 1) + (t - 1) * K := by
    rw [Nat.mul_sub_right_distrib, one_mul, mul_comm t K, ← ht]
    omega
  rw [Nat.ModEq, hseq, Nat.add_mul_mod_self_right]

/-- `K − 1` is coprime to `K` (for `K ≥ 1`). -/
theorem coprime_pred {K : ℕ} (hK : 1 ≤ K) : Nat.Coprime (K - 1) K := by
  rcases Nat.lt_or_ge K 2 with h | h
  · have : K = 1 := by omega
    subst this
    simp [Nat.Coprime]
  · have hK2 : 2 ≤ K - 1 := by omega
    rw [Nat.Coprime, Nat.gcd_rec]
    rw [show K % (K - 1) = 1 by
      conv_lhs => rw [show K = (K - 1) + 1 by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < K - 1)]]
    exact Nat.gcd_one_left _

/-- The largest prime factor of a `−1` anti-sieve element is strictly below
`p`: `s ≡ −1 (mod p)` forces `p ∤ s`. -/
theorem lpf_lt_of_mem_smoothCongruentNegOne {N p s : ℕ} (hp : 2 ≤ p)
    (hs : s ∈ smoothCongruentNegOne N p) :
    largestPrimeFactor s < p := by
  obtain ⟨hs2, -, hlpf, hmod⟩ := mem_smoothCongruentNegOne.mp hs
  have hpdvd : p ∣ s + 1 := (dvd_pow_self p two_ne_zero).trans hmod
  obtain ⟨t, ht⟩ := hpdvd
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      rw [h0, mul_zero] at ht
      omega
    · exact h0
  have hps1 : p ≤ s + 1 := by rw [ht]; exact Nat.le_mul_of_pos_right _ ht1
  have hseq : s = (p - 1) + (t - 1) * p := by
    rw [Nat.mul_sub_right_distrib, one_mul, mul_comm t p, ← ht]
    omega
  have hsmod : s % p = p - 1 := by
    rw [hseq, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (Nat.sub_lt (by omega) one_pos)]
  rcases lt_trichotomy (largestPrimeFactor s) p with h | h | h
  · exact h
  · exfalso
    have hd : p ∣ s := h ▸ largestPrimeFactor_dvd hs2
    have hz : s % p = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  · omega

/-- **The `−1` cofactor-pair set**: `(m, q)` with `q ∈ [1, p−1]` prime, `m`
`q`-smooth, `q·m ≡ −1 (mod p²)` and `q·m ≤ N`. -/
def cofactorFinsetNeg (N p : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (p - 1))).filter fun ⟨m, q⟩ =>
    q.Prime ∧ largestPrimeFactor m ≤ q ∧ q * m ≡ p ^ 2 - 1 [MOD p ^ 2] ∧
      q * m ≤ N

theorem mem_cofactorFinsetNeg {N p m q : ℕ} :
    (m, q) ∈ cofactorFinsetNeg N p ↔
      1 ≤ m ∧ m ≤ N ∧ 1 ≤ q ∧ q ≤ p - 1 ∧ q.Prime ∧
        largestPrimeFactor m ≤ q ∧ q * m ≡ p ^ 2 - 1 [MOD p ^ 2] ∧
          q * m ≤ N := by
  simp only [cofactorFinsetNeg, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

/-- **Anatomy lemma (`−1` class).**  For `s ∈ smoothCongruentNegOne N p`,
`q = largestPrimeFactor s` is prime, `1 ≤ q ≤ p − 1`, `m = s/q` is
`q`-smooth, `q·m ≡ −1 (mod p²)` and `q·m = s ≤ N`. -/
theorem cofactorPairNeg_mem_of_mem {N p s : ℕ} (hp : 2 ≤ p)
    (hs : s ∈ smoothCongruentNegOne N p) :
    (s / largestPrimeFactor s, largestPrimeFactor s) ∈
      cofactorFinsetNeg N p := by
  obtain ⟨hs2, hsN, hlpf, hmod⟩ := mem_smoothCongruentNegOne.mp hs
  have hqprime : (largestPrimeFactor s).Prime := largestPrimeFactor_prime hs2
  have hq2 := hqprime.two_le
  have hqdvd : largestPrimeFactor s ∣ s := largestPrimeFactor_dvd hs2
  have hqlt : largestPrimeFactor s < p :=
    lpf_lt_of_mem_smoothCongruentNegOne hp hs
  have hm1 : 1 ≤ s / largestPrimeFactor s :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hqprime.pos
  have hmul : largestPrimeFactor s * (s / largestPrimeFactor s) = s :=
    Nat.mul_div_cancel' hqdvd
  rw [mem_cofactorFinsetNeg]
  refine ⟨hm1, (Nat.div_le_self _ _).trans hsN, by omega, by omega, hqprime,
    largestPrimeFactor_le_of_dvd (Nat.div_dvd_of_dvd hqdvd) hs2, ?_, ?_⟩
  · rw [hmul]
    exact modEq_pred_one_of_dvd_succ (Nat.one_le_pow 2 p (by omega)) hmod
  · rw [hmul]
    exact hsN

/-- The anatomy map is injective, so the `−1` anti-sieve count is at most the
number of `−1` cofactor pairs. -/
theorem card_smoothCongruentNegOne_le_cofactorFinsetNeg (N p : ℕ)
    (hp : 2 ≤ p) :
    (smoothCongruentNegOne N p).card ≤ (cofactorFinsetNeg N p).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun s => (s / largestPrimeFactor s, largestPrimeFactor s))
  · intro s hs
    rw [Finset.mem_coe] at hs ⊢
    exact cofactorPairNeg_mem_of_mem hp hs
  · intro a ha b hb hab
    have ha2 : 2 ≤ a :=
      (mem_smoothCongruentNegOne.mp (Finset.mem_coe.mp ha)).1
    have hb2 : 2 ≤ b :=
      (mem_smoothCongruentNegOne.mp (Finset.mem_coe.mp hb)).1
    have h1 : largestPrimeFactor a = largestPrimeFactor b :=
      congrArg Prod.snd hab
    have h2 : a / largestPrimeFactor a = b / largestPrimeFactor b :=
      congrArg Prod.fst hab
    have h3 : a = largestPrimeFactor b * (a / largestPrimeFactor a) := by
      rw [← h1]
      exact (Nat.mul_div_cancel' (largestPrimeFactor_dvd ha2)).symm
    calc a = largestPrimeFactor b * (a / largestPrimeFactor a) := h3
      _ = largestPrimeFactor b * (b / largestPrimeFactor b) := by rw [h2]
      _ = b := Nat.mul_div_cancel' (largestPrimeFactor_dvd hb2)

/-- **Fiber uniqueness (`−1` class).**  Two `−1` cofactor pairs with the
same `m` have the same `q`: the class `−m⁻¹ (mod p²)` meets `[1, p − 1]` at
most once. -/
theorem cofactorPairNeg_q_unique {N p m q₁ q₂ : ℕ} (hp : 2 ≤ p)
    (h₁ : (m, q₁) ∈ cofactorFinsetNeg N p)
    (h₂ : (m, q₂) ∈ cofactorFinsetNeg N p) :
    q₁ = q₂ := by
  obtain ⟨-, -, hq1a, hqp1, -, -, hc1, -⟩ := mem_cofactorFinsetNeg.mp h₁
  obtain ⟨-, -, hq2a, hqp2, -, -, hc2, -⟩ := mem_cofactorFinsetNeg.mp h₂
  have hcop : Nat.Coprime (p ^ 2 - 1) (p ^ 2) :=
    coprime_pred (Nat.one_le_pow 2 p (by omega))
  have hcong : q₁ ≡ q₂ [MOD p ^ 2] :=
    modEq_of_mul_modEq_of_coprime (Nat.pow_pos (show 0 < p by omega))
      (mul_comm q₁ m ▸ hc1) (mul_comm q₂ m ▸ hc2) hcop
  have hle : p ≤ p ^ 2 := Nat.le_self_pow (by norm_num) p
  rcases le_total q₁ q₂ with hqq | hqq
  · have hd : p ^ 2 ∣ q₂ - q₁ := (Nat.modEq_iff_dvd' hqq).mp hcong
    have hlt : q₂ - q₁ < p ^ 2 := by omega
    have h0 : q₂ - q₁ = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega
  · have hd : p ^ 2 ∣ q₁ - q₂ := (Nat.modEq_iff_dvd' hqq).mp hcong.symm
    have hlt : q₁ - q₂ < p ^ 2 := by omega
    have h0 : q₁ - q₂ = 0 := Nat.eq_zero_of_dvd_of_lt hd hlt
    omega

/-- The `m`-fiber of the `−1` cofactor set has at most one element. -/
theorem cofactorFinsetNeg_fiber_le_one {N p m : ℕ} (hp : 2 ≤ p) :
    ((cofactorFinsetNeg N p).filter fun e => e.1 = m).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ma, qa⟩ := a
  obtain ⟨mb, qb⟩ := b
  obtain ⟨hmema, hfa⟩ := Finset.mem_filter.mp ha
  obtain ⟨hmemb, hfb⟩ := Finset.mem_filter.mp hb
  have hma : ma = m := hfa
  have hmb : mb = m := hfb
  rw [hma] at hmema
  rw [hmb] at hmemb
  have hq : qa = qb := cofactorPairNeg_q_unique hp hmema hmemb
  simp only [Prod.mk.injEq]
  exact ⟨hma.trans hmb.symm, hq⟩

/-- **Rankin recovery (`−1` class).**  The `−1` cofactor pairs inject via
`(m, q) ↦ m` into the `(p−1)`-smooth integers. -/
theorem cofactorFinsetNeg_card_le_smoothCount (N p : ℕ) (hp : 2 ≤ p) :
    (cofactorFinsetNeg N p).card ≤ smoothCount N (p - 1) := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ⟨m, q⟩ hmq
    rw [Finset.mem_coe] at hmq ⊢
    obtain ⟨hm1, hmN, -, hqp, -, hmq', -, -⟩ := mem_cofactorFinsetNeg.mp hmq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, hmq'.trans hqp⟩
  · intro ⟨m₁, q₁⟩ h₁ ⟨m₂, q₂⟩ h₂ h
    have hm : m₁ = m₂ := h
    have h1 := Finset.mem_coe.mp h₁
    have h2 := Finset.mem_coe.mp h₂
    rw [hm] at h1
    have hq : q₁ = q₂ := cofactorPairNeg_q_unique hp h1 h2
    rw [hm, hq]

/-- `|smoothCongruentNegOne N p| ≤ Ψ(N, p − 1)`. -/
theorem smoothCongruentNegOne_card_le_smoothCount (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentNegOne N p).card ≤ smoothCount N (p - 1) :=
  (card_smoothCongruentNegOne_le_cofactorFinsetNeg N p hp).trans
    (cofactorFinsetNeg_card_le_smoothCount N p hp)

/-- **Rankin recovery for the left run count:**
`leftRunCount x p 1 ≤ Ψ(2x + 1, p − 1)`. -/
theorem leftRunCount_one_le_smoothCount {x p : ℕ} (hp : Nat.Prime p) :
    leftRunCount x p 1 ≤ smoothCount (2 * x + 1) (p - 1) :=
  (leftRunCount_one_le_smoothCongruentNegOne' hp).trans
    (smoothCongruentNegOne_card_le_smoothCount _ _ hp.two_le)

/-! ### The `−1` partner decomposition and the explicit bound -/

/-- The `−1` cofactor–partner set: `m ∈ [1, M]` `y`-smooth with
`q·m ≡ −1 (mod K)` (i.e. `m ≡ −q⁻¹ (mod K)`). -/
def smoothPartnerFinsetNeg (M y K q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun m =>
    largestPrimeFactor m ≤ y ∧ q * m ≡ K - 1 [MOD K]

noncomputable def smoothPartnerCountNeg (M y K q : ℕ) : ℕ :=
  (smoothPartnerFinsetNeg M y K q).card

theorem mem_smoothPartnerFinsetNeg {M y K q m : ℕ} :
    m ∈ smoothPartnerFinsetNeg M y K q ↔
      1 ≤ m ∧ m ≤ M ∧ largestPrimeFactor m ≤ y ∧ q * m ≡ K - 1 [MOD K] := by
  simp only [smoothPartnerFinsetNeg, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- Any two elements of the `−1` partner set are congruent `mod K`. -/
theorem smoothPartnerNeg_modEq {M y K q m₁ m₂ : ℕ} (hK : 1 ≤ K)
    (hm₁ : m₁ ∈ smoothPartnerFinsetNeg M y K q)
    (hm₂ : m₂ ∈ smoothPartnerFinsetNeg M y K q) :
    m₁ ≡ m₂ [MOD K] := by
  obtain ⟨-, -, -, h1⟩ := mem_smoothPartnerFinsetNeg.mp hm₁
  obtain ⟨-, -, -, h2⟩ := mem_smoothPartnerFinsetNeg.mp hm₂
  exact modEq_of_mul_modEq_of_coprime (by omega) h1 h2 (coprime_pred hK)

/-- **`−1` partner count bound (class count).**  If `gcd(q, K) > 1` there are
no solutions at all; otherwise all solutions lie in a single class `mod K`,
so `#{m ≤ M} ≤ M/K + 1`. -/
theorem smoothPartnerCountNeg_le (M y K q : ℕ) (hK : 0 < K) :
    smoothPartnerCountNeg M y K q ≤ M / K + 1 := by
  classical
  by_cases hcop : Nat.Coprime q K
  · rcases (smoothPartnerFinsetNeg M y K q).eq_empty_or_nonempty
      with h | hne
    · simp [smoothPartnerCountNeg, h]
    · obtain ⟨m₀, hm₀⟩ := hne
      have hsub : smoothPartnerFinsetNeg M y K q ⊆
          (Finset.Icc 1 M).filter fun m => m ≡ m₀ [MOD K] := by
        intro m hm
        obtain ⟨hm1, hmM, -, -⟩ := mem_smoothPartnerFinsetNeg.mp hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hm1, hmM⟩,
            smoothPartnerNeg_modEq (by omega) hm hm₀⟩
      exact (Finset.card_le_card hsub).trans (card_residue_class_le M K m₀)
  · have hempty : smoothPartnerFinsetNeg M y K q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      obtain ⟨-, -, -, hcong⟩ := mem_smoothPartnerFinsetNeg.mp hm
      exact hcop
        ((coprime_of_mul_modEq hK hcong (coprime_pred (by omega))).1)
    simp [smoothPartnerCountNeg, hempty]

/-- The `q`-fiber of the `−1` anti-sieve set injects via `s ↦ s/q` into the
`−1` partner set `{m ≤ N/q : m q-smooth, q·m ≡ −1 (mod p²)}`. -/
theorem card_fiber_le_smoothPartnerNeg {N p q : ℕ} (hp : 2 ≤ p)
    (hq : q.Prime) :
    ((smoothCongruentNegOne N p).filter
        fun s => largestPrimeFactor s = q).card ≤
      smoothPartnerCountNeg (N / q) q (p ^ 2) q := by
  classical
  apply Finset.card_le_card_of_injOn (· / q)
  · intro s hs
    rw [Finset.mem_coe] at hs ⊢
    obtain ⟨hs, hqs⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs2, hsN, -, hmod⟩ := mem_smoothCongruentNegOne.mp hs
    have hqdvd : q ∣ s := hqs ▸ largestPrimeFactor_dvd hs2
    rw [mem_smoothPartnerFinsetNeg]
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hq.pos,
      Nat.div_le_div_right hsN, ?_, ?_⟩
    · have h := largestPrimeFactor_le_of_dvd (Nat.div_dvd_of_dvd hqdvd) hs2
      rwa [hqs] at h
    · have hmul : q * (s / q) = s := Nat.mul_div_cancel' hqdvd
      rw [hmul]
      exact modEq_pred_one_of_dvd_succ (Nat.one_le_pow 2 p (by omega)) hmod
  · intro a ha b hb hab
    obtain ⟨ha, hqa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    obtain ⟨hb, hqb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    have ha2 : 2 ≤ a := (mem_smoothCongruentNegOne.mp ha).1
    have hb2 : 2 ≤ b := (mem_smoothCongruentNegOne.mp hb).1
    have hda : q ∣ a := hqa ▸ largestPrimeFactor_dvd ha2
    have hdb : q ∣ b := hqb ▸ largestPrimeFactor_dvd hb2
    have hab' : a / q = b / q := hab
    calc a = q * (a / q) := (Nat.mul_div_cancel' hda).symm
      _ = q * (b / q) := by rw [hab']
      _ = b := Nat.mul_div_cancel' hdb

/-- **Exact fiber decomposition (`−1` class).** -/
theorem smoothCongruentNegOne_card_eq_sum_fiber (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentNegOne N p).card =
      ∑ q ∈ Nat.primesLE (p - 1),
        ((smoothCongruentNegOne N p).filter
          fun s => largestPrimeFactor s = q).card := by
  classical
  have hU : smoothCongruentNegOne N p = (Nat.primesLE (p - 1)).biUnion
      fun q => (smoothCongruentNegOne N p).filter
        fun s => largestPrimeFactor s = q := by
    ext s
    rw [Finset.mem_biUnion]
    constructor
    · intro hs
      obtain ⟨hs2, -, -, -⟩ := mem_smoothCongruentNegOne.mp hs
      refine ⟨largestPrimeFactor s, Nat.mem_primesLE.mpr ⟨?_, ?_⟩,
        Finset.mem_filter.mpr ⟨hs, rfl⟩⟩
      · have h := lpf_lt_of_mem_smoothCongruentNegOne hp hs
        omega
      · exact largestPrimeFactor_prime hs2
    · rintro ⟨q, -, hs⟩
      exact (Finset.mem_filter.mp hs).1
  have hdis : ((Nat.primesLE (p - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun q => (smoothCongruentNegOne N p).filter
        fun s => largestPrimeFactor s = q := by
    intro q₁ _ q₂ _ hne
    exact Finset.disjoint_left.mpr fun s hs₁ hs₂ =>
      hne ((Finset.mem_filter.mp hs₁).2.symm.trans
        (Finset.mem_filter.mp hs₂).2)
  conv_lhs => rw [hU]
  rw [Finset.card_biUnion hdis]

/-- **Per-prime partner bound (`−1` class).** -/
theorem smoothCongruentNegOne_card_le_sum_partner (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentNegOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1),
        smoothPartnerCountNeg (N / q) q (p ^ 2) q := by
  rw [smoothCongruentNegOne_card_eq_sum_fiber N p hp]
  apply Finset.sum_le_sum
  intro q hq
  exact card_fiber_le_smoothPartnerNeg hp (Nat.prime_of_mem_primesLE hq)

/-- **Explicit unconditional bound (`−1` class):**
`|smoothCongruentNegOne N p| ≤ ∑_{q prime < p} (N/(q·p²) + 1)`. -/
theorem smoothCongruentNegOne_card_le_sum (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentNegOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), (N / (q * p ^ 2) + 1) := by
  refine (smoothCongruentNegOne_card_le_sum_partner N p hp).trans ?_
  apply Finset.sum_le_sum
  intro q _
  calc smoothPartnerCountNeg (N / q) q (p ^ 2) q
      ≤ N / q / p ^ 2 + 1 :=
        smoothPartnerCountNeg_le _ _ _ _ (Nat.pow_pos (show 0 < p by omega))
    _ = N / (q * p ^ 2) + 1 := by rw [Nat.div_div_eq_div_mul]

/-- **Real form of the `−1` elementary bound:**
`|smoothCongruentNegOne N p| ≤ (N/p²)·(1 + log(p−1)) + p`. -/
theorem smoothCongruentNegOne_card_le_real (N p : ℕ) (hp : 2 ≤ p) :
    ((smoothCongruentNegOne N p).card : ℝ) ≤
      (N : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := by
  have hsum : (smoothCongruentNegOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), (N / (q * p ^ 2) + 1) :=
    smoothCongruentNegOne_card_le_sum N p hp
  have hterm : ∀ q ∈ Nat.primesLE (p - 1),
      ((N / (q * p ^ 2) + 1 : ℕ) : ℝ) ≤
        (N : ℝ) / (q * (p : ℝ) ^ 2) + 1 := by
    intro q _
    push_cast
    have h : (((N / (q * p ^ 2)) : ℕ) : ℝ) ≤
        (N : ℝ) / (((q * p ^ 2) : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_pow] at h
    linarith [h]
  calc ((smoothCongruentNegOne N p).card : ℝ)
      ≤ ((∑ q ∈ Nat.primesLE (p - 1), (N / (q * p ^ 2) + 1)) : ℕ) :=
        Nat.cast_le.mpr hsum
    _ = ∑ q ∈ Nat.primesLE (p - 1), (((N / (q * p ^ 2) + 1) : ℕ) : ℝ) :=
        Nat.cast_sum _ _
    _ ≤ ∑ q ∈ Nat.primesLE (p - 1), ((N : ℝ) / (q * (p : ℝ) ^ 2) + 1) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) / p ^ 2 * (∑ q ∈ Nat.primesLE (p - 1), (1 : ℝ) / q)
          + (Nat.primesLE (p - 1)).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          have hqR : (0 : ℝ) < (q : ℝ) := by
            exact_mod_cast (Nat.prime_of_mem_primesLE hq).pos
          rw [mul_comm (q : ℝ) ((p : ℝ) ^ 2), ← div_div, mul_one_div]
        · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (N : ℝ) / p ^ 2 * (1 + Real.log (p - 1)) + p := by
        have hcard : ((Nat.primesLE (p - 1)).card : ℝ) ≤ p := by
          have h := card_primesLE_le (p - 1)
          have h' : (Nat.primesLE (p - 1)).card ≤ p := by omega
          exact_mod_cast h'
        apply add_le_add _ hcard
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hlog : Real.log ((p : ℝ) - 1) = Real.log ((p - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
        rw [hlog]
        exact sum_primesLE_inv_le (p - 1)

/-- The elementary real bound on the `k = 1` left-run count:
`leftRunCount x p 1 ≤ ((2x+1)/p²)·(1 + log(p−1)) + p`. -/
theorem leftRunCount_one_le_real {x p : ℕ} (hp : Nat.Prime p) :
    (leftRunCount x p 1 : ℝ) ≤
      ((2 * x + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := by
  have h1 : leftRunCount x p 1 ≤ (smoothCongruentNegOne (2 * x + 1) p).card :=
    leftRunCount_one_le_smoothCongruentNegOne' hp
  have h2 := smoothCongruentNegOne_card_le_real (2 * x + 1) p hp.two_le
  calc (leftRunCount x p 1 : ℝ)
      ≤ ((smoothCongruentNegOne (2 * x + 1) p).card : ℝ) := Nat.cast_le.mpr h1
    _ ≤ ((2 * x + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p :=
        h2

/-! ### Diagonal/tail split of `runCountSum` -/

/-- The `k = 1` **diagonal** of `runCountSum`. -/
noncomputable def runDiagSum (x : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
    (rightRunCount x p 1 + leftRunCount x p 1)

/-- The `k ≥ 2` **tail** of `runCountSum`. -/
noncomputable def runTailSum (x : ℕ) : ℕ :=
  ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
    ∑ k ∈ Finset.Icc 2 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- `Icc 1 (2p) = insert 1 (Icc 2 (2p))` for `p ≥ 1`. -/
theorem Icc_one_two_mul_eq_insert {p : ℕ} (hp : 1 ≤ p) :
    Finset.Icc 1 (2 * p) = insert 1 (Finset.Icc 2 (2 * p)) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- **Diagonal/tail split**:
`runCountSum x = runDiagSum x + runTailSum x`. -/
theorem runCountSum_eq_diag_add_tail (x : ℕ) :
    runCountSum x = runDiagSum x + runTailSum x := by
  unfold runCountSum runDiagSum runTailSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
  rw [Icc_one_two_mul_eq_insert (by omega : 1 ≤ p),
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  omega

/-- Both `k = 1` diagonals together are bounded by twice the true covered
count: the diagonal is *tight*, so the whole excess of `runCountSum` sits in
the `k ≥ 2` tail. -/
theorem sum_runCount_one_le_two_mul_shortBadCount (x : ℕ) :
    ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (rightRunCount x p 1 + leftRunCount x p 1) ≤
      2 * shortBadCount (2 * x) := by
  rw [Finset.sum_add_distrib, two_mul]
  exact add_le_add (sum_rightRunCount_one_le_shortBadCount x)
    (sum_leftRunCount_one_le_shortBadCount x)

/-! ### The equidistribution hypothesis -/

/-- **Per-prime equidistribution bound at scale `x`**: the `p`-smooth
integers `≡ ±1 (mod p²)` up to the sharp range `N = p²·(2x/p²) + 1` number
at most `C·Ψ(2x+1, p)/p²·(log log x)^K`. -/
def smoothEquidistBoundAt (x p : ℕ) (C K : ℝ) : Prop :=
  ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
      (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card : ℝ) ≤
    C * (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 *
      (Real.log (Real.log x)) ^ K

/-- Under the per-prime equidistribution bound, the combined `k = 1` run
count `R₁ + L₁` is bounded by `C·Ψ(2x+1, p)/p²·(log log x)^K`. -/
theorem runCount_one_le_of_equidist {x p : ℕ} (hp : Nat.Prime p)
    {C K : ℝ} (h : smoothEquidistBoundAt x p C K) :
    (rightRunCount x p 1 + leftRunCount x p 1 : ℝ) ≤
      C * (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 *
        (Real.log (Real.log x)) ^ K := by
  have hR : rightRunCount x p 1 ≤
      (smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card := by
    refine (rightRunCount_one_le_apSmoothParamCount hp).trans_eq ?_
    exact apSmoothParamCount_one_eq_smoothCongruentOne _ _ hp.two_le
  have hL := leftRunCount_one_le_smoothCongruentNegOne hp
  have hnat : rightRunCount x p 1 + leftRunCount x p 1 ≤
      (smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
        (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card :=
    add_le_add hR hL
  calc (rightRunCount x p 1 + leftRunCount x p 1 : ℝ)
      ≤ (((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
          (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card : ℕ) :
          ℝ) := Nat.cast_le.mpr hnat
    _ = ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card : ℝ) +
          ((smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card : ℝ) :=
        Nat.cast_add _ _
    _ ≤ C * (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 *
          (Real.log (Real.log x)) ^ K := h

/-- **The anti-sieve equidistribution hypothesis** (Ta26c Props 6.6–6.8
shape): `p`-smooth numbers equidistribute into the classes `±1 (mod p²)`,
with density `≍ 1/p²`, up to a `(log log x)^K` slack, uniformly over primes
`p ≤ √(2x)`. -/
def SmoothEquidistHyp : Prop :=
  ∃ C K : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in atTop,
    ∀ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), Nat.Prime p →
      smoothEquidistBoundAt x p C K

/-- **The `Ψ/p²`-weight hypothesis**: the `1/p²`-weighted smooth count over
`p ≤ √(2x)` is bounded by the singleton scale `S·(log x)^{-1}` up to
`(log log x)^K` slack.  (Same `z`-scale saddle as `S`; the extra
`ρ(u)/ρ(u−2)` ratio supplies the `(log x)^{-1}` saving.) -/
def SmoothSqWeightHyp : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K

/-- **The long-run tail hypothesis**: runs of length `≥ 2` contribute at most
`S·(log x)^{-1}·(log log x)^K`.  This is the second-moment / Størmer-type
input — it is *not* implied by the `k = 1` equidistribution bound. -/
def LongRunTailHyp : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    ((runTailSum x : ℕ) : ℝ) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K

/-- Under the pointwise equidistribution bound at `x`, the diagonal satisfies
`runDiagSum x ≤ C·(log log x)^K·∑_p Ψ(2x+1, p)/p²`. -/
theorem runDiagSum_le_sqWeight {x : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), Nat.Prime p →
      smoothEquidistBoundAt x p C K) :
    (runDiagSum x : ℝ) ≤
      C * (Real.log (Real.log x)) ^ K *
        ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 := by
  calc (runDiagSum x : ℝ)
      = ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (rightRunCount x p 1 + leftRunCount x p 1)) : ℕ → ℝ) := by
        rfl
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          C * (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 *
            (Real.log (Real.log x)) ^ K := by
        rw [show ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            (rightRunCount x p 1 + leftRunCount x p 1) : ℕ) : ℝ) =
          ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            ((rightRunCount x p 1 + leftRunCount x p 1 : ℕ) : ℝ) from
          Nat.cast_sum _ _]
        exact Finset.sum_le_sum fun p hp =>
          runCount_one_le_of_equidist (Nat.prime_of_mem_primesLE hp)
            (heq p hp (Nat.prime_of_mem_primesLE hp))
    _ = C * (Real.log (Real.log x)) ^ K *
          ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring

/-- **Two-term absorption**: if `f` and `g` are eventually bounded by
`c·S·L^{-1}·t^a` and `d·S·L^{-1}·t^b` (`t = log log x`), then `f + g` is
eventually bounded by `S·L^{-1}·t^{max a b + 2}`. -/
theorem exists_loglog_bound_of_two {f g : ℕ → ℕ} (c d a b : ℝ) (hc : 0 ≤ c)
    (hd : 0 ≤ d)
    (hf : ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ c * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ a)
    (hg : ∀ᶠ x : ℕ in atTop,
      (g x : ℝ) ≤ d * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ b) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      ((f x : ℝ) + (g x : ℝ)) ≤ (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ K := by
  have hlt : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨max a b + 2, ?_⟩
  filter_upwards [hf, hg, hlt.eventually_ge_atTop (max 1 (c + d)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      .eventually_ge_atTop 1]
    with x hfx hgx ht hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  set t := Real.log (Real.log (x : ℝ)) with htdef
  set S := (badSingletonCount x : ℝ) with hSdef
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
  have hcd : c + d ≤ t := le_trans (le_max_right _ _) ht
  have hta : t ^ a ≤ t ^ max a b :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have htb : t ^ b ≤ t ^ max a b :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right _ _)
  have hB : (0 : ℝ) ≤ S * (Real.log x) ^ (-(1 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  have h1 : c * S * (Real.log x) ^ (-(1 : ℝ)) * t ^ a ≤
      c * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hta hB) hc
  have h2 : d * S * (Real.log x) ^ (-(1 : ℝ)) * t ^ b ≤
      d * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htb hB) hd
  have hsum : (f x : ℝ) + (g x : ℝ) ≤
      (c + d) * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) := by
    calc (f x : ℝ) + (g x : ℝ)
        ≤ c * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) +
            d * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) :=
          add_le_add (hfx.trans h1) (hgx.trans h2)
      _ = (c + d) * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) := by ring
  have habs : (c + d) * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) ≤
      S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (max a b + 2) := by
    have hnn : (0 : ℝ) ≤ S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b :=
      mul_nonneg hB (Real.rpow_nonneg htpos.le _)
    calc (c + d) * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b)
        ≤ t * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ max a b) :=
          mul_le_mul_of_nonneg_right hcd hnn
      _ = S * (Real.log x) ^ (-(1 : ℝ)) * (t * t ^ max a b) := by ring
      _ = S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (max a b + 1) := by
          rw [Real.rpow_add_one htpos.ne']; ring
      _ ≤ S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (max a b + 2) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hB
  exact hsum.trans habs
```

Wait — there's an error in habs: `t * (... * t^max) ≤ t^{max+1}` then `≤ t^{max+2}` — I used factor t once but need c+d ≤ t² really. Actually above I bound `(c+d)·X ≤ t·X = ...t^{A+1} ≤ t^{A+2}` — that gives (c+d)·X ≤ S·L^{-1}·t^{A+1}·... wait the second step `≤ t^{A+2}` loses an extra t — it's fine (inequality direction correct: t^{A+1} ≤ t^{A+2} since t ≥ 1). So K = max a b + 2 works even with c+d ≤ t. Actually I could use +1 but +2 is safe. Good — but wait in the step `_ ≤ S·L^{-1}·t^{max a b + 2}` I apply `Real.rpow_le_rpow_of_exponent_le ht1` to show `t^{A+1} ≤ t^{A+2}` — with mul_le_mul_of_nonneg_left ... hB — needs the multiplier S·L^{-1} ≥ 0 ✓. OK.

Hmm, wait: in habs the third calc step rewrites `t * t^A` as `t^(A+1)`: `Real.rpow_add_one htpos.ne'` : `t * t^A`? Actually `Real.rpow_add_one (hx : x ≠ 0) : x ^ a * x = x ^ (a + 1)`. I have `t * t^A` — need `t^A * t`. ring normalizes before rw? I wrote `= S·L^{-1}·(t * t^{A})` by ring then `= S·L^{-1}·t^{A+1}` by `rw [Real.rpow_add_one]; ring` — the rw target `t * t^A` doesn't match `t^A * t` pattern of rpow_add_one. Fix: `mul_comm` first or use `Real.rpow_add_one` differently. I'll adjust: `rw [mul_comm t (t ^ max a b), Real.rpow_add_one htpos.ne']`. Let me just restructure:

```lean
      _ = S * (Real.log x) ^ (-(1 : ℝ)) * (t ^ max a b * t) := by ring
      _ = S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (max a b + 1) := by
          rw [Real.rpow_add_one htpos.ne']
```

OK. Now continuing the file: the diagonal bound under the hypothesis and the combined theorem.

```lean
/-- **The `Ψ/p`-weight hypothesis** (cruder route): bounds the `1/p`-weighted
smooth sum — the weight that the `2p·T₁` diagonal collapse produces. -/
def SmoothWeightHyp : Prop := ...
```

And theorem `runCountSum_le_smoothWeight_of_equidist` (pointwise x):

```lean
theorem runCountSum_le_smoothWeight_of_equidist {x : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ primesLE, Prime p → bound) :
    (runCountSum x : ℝ) ≤
      2 * C * t^K * ∑_p Ψ(2x+1,p)/p
```

via runCountSum_le_diagonal (nat), cast, per-term bound 2p·(R₁+L₁) ≤ 2p·C·Ψ/p²·t^K = 2C·Ψ/p·t^K (needs p ≠ 0, field_simp+ring).

Then `badNonSingleton_interval_bound_of_equidist_and_weight : SmoothEquidistHyp → SmoothWeightHyp → residual` via exists_loglog_bound_of_two? It's a single term: runCountSum ≤ 2C·t^{K₁}·(S L^{-1} t^{K₂}) = (2C)·S·L^{-1}·t^{K₁+K₂}. I can feed through a helper:

```lean
theorem exists_loglog_bound_of_mul_const {f : ℕ → ℕ} (c a : ℝ) (hc : 0 ≤ c)
    (hf : ∀ᶠ x, (f x :ℝ) ≤ c * S * L^{-1} * t^a) :
    ∃ K, ∀ᶠ x, (f x:ℝ) ≤ S·L^{-1}·t^K
```
with K = a+2, since c·t^a ≤ t^{a+2} when c ≤ t². Take t ≥ max 1 c: t² ≥ t ≥ c → c·t^a ≤ t²·t^a = t^{a+2} (rpow_add t>0). ✓

Then in `badNonSingleton_interval_bound_of_equidist_and_weight`:
- from hE obtain ⟨C, K₁, hC, hE'⟩; from hW obtain ⟨K₂, hW'⟩.
- hf : ∀ᶠ x, (runCountSum x : ℝ) ≤ (2*C)·S·L^{-1}·t^{K₁+K₂}: pointwise bound via runCountSum_le_smoothWeight_of_equidist then hW':
  runCountSum ≤ 2C·t^{K₁}·∑Ψ/p ≤ 2C·t^{K₁}·S·L^{-1}·t^{K₂} = 2C·S·L^{-1}·t^{K₁+K₂} (rpow_add, need 2C·t^{K₁} ≥ 0 for the mul inequality: C ≥ 0 → 2C ≥ 0, t^{K₁} ≥ 0 ✓).
- then exists_loglog_bound_of_mul_const (2C) (K₁+K₂) (by positivity) hf → ∃ K.
- close via badNonSingleton_interval_bound_of_runCountSum_loglog.

And `badNonSingleton_interval_bound_of_antiSieve_hyps : SmoothEquidistHyp → SmoothSqWeightHyp → LongRunTailHyp → residual`:
- diag: hf with f = runDiagSum, c = C, a = K₁+K₂: runDiagSum ≤ C·t^{K₁}·∑Ψ/p² ≤ C·t^{K₁}·S·L^{-1}·t^{K₂} = C·S·L^{-1}·t^{K₁+K₂}.
- tail: g = runTailSum, d = 1, b = K₃.
- exists_loglog_bound_of_two → ∃ K, ∀ᶠ, (runDiagSum:ℝ)+(runTailSum:ℝ) ≤ S·L^{-1}·t^K.
- runCountSum x = runDiagSum x + runTailSum x → (runCountSum:ℝ) = sum → bound holds for runCountSum → badNonSingleton_interval_bound_of_runCountSum_loglog.

For the banded version — include it as second deliverable:

```lean
/-- Band cutoff: the small band is `p ≤ B x`, the large band `B x < p`. -/
def bandPrimes (x : ℕ) (B : ℕ) : Finset ℕ :=
  (Nat.primesLE (Nat.sqrt (2 * x))).filter (· ≤ B)

noncomputable def bandRunSum (x B : ℕ) : ℕ :=
  ∑ p ∈ bandPrimes x B,
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

noncomputable def largeRunSum (x B : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => B < p),
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

theorem runCountSum_eq_band_add_large (x B : ℕ) :
    runCountSum x = bandRunSum x B + largeRunSum x B := by
  unfold runCountSum bandRunSum largeRunSum bandPrimes
  have hU : Nat.primesLE (Nat.sqrt (2 * x)) =
      (Nat.primesLE (Nat.sqrt (2 * x))).filter (· ≤ B) ∪
        (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => B < p) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases le_or_lt p B with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
  conv_lhs => rw [hU]
  rw [Finset.sum_union ?_]
  · rfl
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  obtain ⟨-, hle⟩ := Finset.mem_filter.mp hq1
  obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hq2
  omega
```

Wait `Finset.sum_union` signature: `Finset.sum_union (h : Disjoint s₁ s₂) : ∑ x ∈ s₁ ∪ s₂, f x = ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x`. Need Disjoint — provide `?_` then prove. The disjoint proof: `Finset.disjoint_left.mpr`? `Finset.disjoint_left : Disjoint s t ↔ ∀ a ∈ s, a ∉ t`. So `rw [Finset.disjoint_left]` makes goal `∀ ⦃a⦄, a ∈ s.filter(·≤B) → a ∉ s.filter(B < ·)`; intro q hq1 hq2 — wait hq2 : q ∈ filter(B<·), i.e. `a ∉ t` means `a ∈ t → False`, so `intro q hq1 hq2` then contradiction. But goal after rw is `∀ ⦃a : ℕ⦄, a ∈ ... → ¬a ∈ ...` — `intro q hq1 hq2` where hq2 : q ∈ ... — intro can intro the ¬ as hypothesis giving False goal? `¬a ∈ t` is `a ∈ t → False`; `intro q hq1 hq2` introduces q, hq1, then hq2 : q ∈ t, goal False. ✓ then obtain memberships, omega.

Then band hypotheses:

```lean
def SmallBandEquidistHyp (B : ℕ → ℕ) : Prop :=
  ∃ C K : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in atTop,
    ∀ p ∈ bandPrimes x (B x), Nat.Prime p → smoothEquidistBoundAt x p C K

def SmallBandWeightHyp (B : ℕ → ℕ) : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ bandPrimes x (B x), (smoothCount (2*x+1) p : ℝ)/(p:ℝ)) ≤
      S·L^{-1}·t^K

def LargeBandRunTailHyp (B : ℕ → ℕ) : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    ((largeRunSum x (B x) : ℕ) : ℝ) ≤ S·L^{-1}·t^K
```

And bandRunSum bound lemma:

```lean
theorem bandRunSum_le_smoothWeight {x B : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ bandPrimes x B, Nat.Prime p → smoothEquidistBoundAt x p C K) :
    (bandRunSum x B : ℝ) ≤
      2 * C * t^K * ∑ p ∈ bandPrimes x B, Ψ/p
```

via inner sum ≤ 2p(R₁+L₁) (sum_Icc_*_le), per-term ≤ 2C·Ψ/p·t^K.

Then `badNonSingleton_interval_bound_of_banded (B : ℕ → ℕ) : SmallBandEquidistHyp B → SmallBandWeightHyp B → LargeBandRunTailHyp B → residual`:
- f = fun x => bandRunSum x (B x): hf bound c = 2C, a = K₁+K₂.
- g = fun x => largeRunSum x (B x): d = 1, b = K₃.
- exists_loglog_bound_of_two gives bound on (bandRunSum:ℝ)+(largeRunSum:ℝ) = (runCountSum:ℝ).
- close.

Also note: `Finset.sum_le_sum` on bandRunSum needs `sum_Icc_rightRunCount_le`/`sum_Icc_leftRunCount_le` per p — the same inner collapse as runCountSum_le_diagonal. In fact simpler: prove `bandRunSum x B ≤ ∑_{p ∈ bandPrimes} 2p·(R₁+L₁)` mirroring runCountSum_le_diagonal, then continue. Or directly generalize: runCountSum_le_diagonal used `Finset.sum_le_sum` with the Icc bound per p; do same on filtered set.

Now assemble everything. Also should I prove `smoothEquidistBoundAt` monotone/`SmoothEquidistHyp` implies SmallBand version? `bandPrimes ⊆ primesLE` — trivially, `SmallBandEquidistHyp B` follows from SmoothEquidistHyp (filter subset). Add one-line theorem `SmallBandEquidistHyp.of_full`. Eh — optional, cheap: 

```lean
theorem SmoothEquidistHyp.smallBand (h : SmoothEquidistHyp) (B : ℕ → ℕ) :
    SmallBandEquidistHyp B := ...
```
bandPrimes x (B x) ⊆ primesLE (√(2x)) via filter_subset → heq p (Finset.mem_filter.mp hp).1. ✓ cheap, include.

Let me now write the complete file to disk and compile.
/-- **Single-term absorption**: `f ≤ c·S·L^{-1}·t^a` eventually implies
`f ≤ S·L^{-1}·t^{a+2}` eventually (a fixed `c` is absorbed since `t² → ∞`). -/
theorem exists_loglog_bound_of_mul_const {f : ℕ → ℕ} (c a : ℝ) (hc : 0 ≤ c)
    (hf : ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ c * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ a) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (f x : ℝ) ≤ (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K := by
  have hlt : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨a + 2, ?_⟩
  filter_upwards [hf, hlt.eventually_ge_atTop (max 1 c),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      .eventually_ge_atTop 1]
    with x hfx ht hL1
  have hL : (0 : ℝ) < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  set t := Real.log (Real.log (x : ℝ)) with htdef
  set S := (badSingletonCount x : ℝ) with hSdef
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
  have hct : c ≤ t := le_trans (le_max_right _ _) ht
  have hB : (0 : ℝ) ≤ S * (Real.log x) ^ (-(1 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hL.le _)
  have hnn : (0 : ℝ) ≤ S * (Real.log x) ^ (-(1 : ℝ)) * t ^ a :=
    mul_nonneg hB (Real.rpow_nonneg htpos.le _)
  calc (f x : ℝ)
      ≤ c * S * (Real.log x) ^ (-(1 : ℝ)) * t ^ a := hfx
    _ = c * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ a) := by ring
    _ ≤ t * (S * (Real.log x) ^ (-(1 : ℝ)) * t ^ a) :=
        mul_le_mul_of_nonneg_right hct hnn
    _ = S * (Real.log x) ^ (-(1 : ℝ)) * (t ^ a * t) := by ring
    _ = S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (a + 1) := by
        rw [Real.rpow_add_one htpos.ne']
    _ ≤ S * (Real.log x) ^ (-(1 : ℝ)) * t ^ (a + 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hB

/-! ### The headline conditional closure (diagonal + tail) -/

/-- **Pointwise diagonal bound under equidistribution.**  If
`smoothEquidistBoundAt x p C K` holds for every `p ≤ √(2x)`, then
`runDiagSum x ≤ C·(log log x)^K·∑_p Ψ(2x+1, p)/p²`. -/
theorem runDiagSum_le_sqWeight' {x : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), Nat.Prime p →
      smoothEquidistBoundAt x p C K) :
    (runDiagSum x : ℝ) ≤
      C * (Real.log (Real.log x)) ^ K *
        ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 := by
  have hcast : ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
      (rightRunCount x p 1 + leftRunCount x p 1) : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ((rightRunCount x p 1 + leftRunCount x p 1 : ℕ) : ℝ) :=
    Nat.cast_sum _ _
  calc (runDiagSum x : ℝ)
      = ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (rightRunCount x p 1 + leftRunCount x p 1)) : ℕ → ℝ) := rfl
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          C * (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 *
            (Real.log (Real.log x)) ^ K := by
        rw [hcast]
        exact Finset.sum_le_sum fun p hp =>
          runCount_one_le_of_equidist (Nat.prime_of_mem_primesLE hp)
            (heq p hp (Nat.prime_of_mem_primesLE hp))
    _ = C * (Real.log (Real.log x)) ^ K *
          ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring

/-- **Conditional run-sum bound**: under `SmoothEquidistHyp`,
`SmoothSqWeightHyp` and `LongRunTailHyp`, eventually
`runCountSum x ≤ S(x)·(log x)^{-1}·(log log x)^K` for an explicit `K`. -/
theorem runCountSum_eventually_le_of_hyps
    (hE : SmoothEquidistHyp) (hW : SmoothSqWeightHyp) (hT : LongRunTailHyp) :
    ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤ (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ K := by
  obtain ⟨C, K₁, hC, hE'⟩ := hE
  obtain ⟨K₂, hW'⟩ := hW
  obtain ⟨K₃, hT'⟩ := hT
  have hlt : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  -- diagonal bound: `runDiagSum ≤ C·S·L^{-1}·t^{K₁+K₂}` eventually.
  have hf : ∀ᶠ x : ℕ in atTop,
      (runDiagSum x : ℝ) ≤ C * (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ (K₁ + K₂) := by
    filter_upwards [hE', hW',
      hlt.eventually_ge_atTop 1] with x hEx hWx ht1
    have ht0 : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := by linarith
    have hfac : (0 : ℝ) ≤ C * (Real.log (Real.log x)) ^ K₁ :=
      mul_nonneg hC (Real.rpow_nonneg ht0.le _)
    calc (runDiagSum x : ℝ)
        ≤ C * (Real.log (Real.log x)) ^ K₁ *
            ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
              (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) ^ 2 :=
          runDiagSum_le_sqWeight' hEx
      _ ≤ C * (Real.log (Real.log x)) ^ K₁ *
            ((badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
              (Real.log (Real.log x)) ^ K₂) :=
          mul_le_mul_of_nonneg_left hWx hfac
      _ = C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            ((Real.log (Real.log x)) ^ K₁ * (Real.log (Real.log x)) ^ K₂) := by
          ring
      _ = C * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            (Real.log (Real.log x)) ^ (K₁ + K₂) := by
          rw [Real.rpow_add ht0]
  -- tail bound: `runTailSum ≤ 1·S·L^{-1}·t^{K₃}`.
  have hg : ∀ᶠ x : ℕ in atTop,
      (runTailSum x : ℝ) ≤ 1 * (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ K₃ := by
    filter_upwards [hT'] with x hx
    simpa using hx
  obtain ⟨K', hK'⟩ := exists_loglog_bound_of_two
    (f := runDiagSum) (g := runTailSum) C 1 (K₁ + K₂) K₃ hC one_pos.le hf hg
  refine ⟨K', ?_⟩
  filter_upwards [hK'] with x hx
  have heq : (runCountSum x : ℝ) = (runDiagSum x : ℝ) + (runTailSum x : ℝ) := by
    rw [← Nat.cast_add]
    exact congrArg Nat.cast (runCountSum_eq_diag_add_tail x)
  rw [heq]
  exact hx

/-- **Headline conditional closure.**  Under the three hypotheses
`SmoothEquidistHyp` (per-prime `≪ Ψ/p²` equidistribution of `p`-smooths into
`±1 (mod p²)`), `SmoothSqWeightHyp` (the `Ψ/p²` saddle comparison against the
singleton count) and `LongRunTailHyp` (the `k ≥ 2` run tail), the residual
`badNonSingleton_interval_bound` of `Main.lean` holds. -/
theorem badNonSingleton_interval_bound_of_antiSieve_hyps
    (hE : SmoothEquidistHyp) (hW : SmoothSqWeightHyp) (hT : LongRunTailHyp) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) :=
  badNonSingleton_interval_bound_of_runCountSum_loglog
    (runCountSum_eventually_le_of_hyps hE hW hT)

/-! ### The cruder `Ψ/p`-weight route (diagonal collapse form) -/

/-- **Pointwise run-sum bound under equidistribution (collapsed form).**
Bounding every `k`-level by the `k = 1` level (`runCountSum_le_diagonal`)
costs a factor `2p` per prime, producing the `1/p`-weighted smooth sum:
`runCountSum x ≤ 2C·(log log x)^K·∑_p Ψ(2x+1, p)/p`. -/
theorem runCountSum_le_smoothWeight_of_equidist {x : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), Nat.Prime p →
      smoothEquidistBoundAt x p C K) :
    (runCountSum x : ℝ) ≤
      2 * C * (Real.log (Real.log x)) ^ K *
        ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) := by
  have hnat : runCountSum x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        2 * p * ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
          (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card) := by
    refine (runCountSum_le_diagonal x).trans ?_
    apply Finset.sum_le_sum
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primesLE hp
    have hR : rightRunCount x p 1 ≤
        (smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card := by
      refine (rightRunCount_one_le_apSmoothParamCount hpp).trans_eq ?_
      exact apSmoothParamCount_one_eq_smoothCongruentOne _ _ hpp.two_le
    have hL := leftRunCount_one_le_smoothCongruentNegOne hpp
    exact Nat.mul_le_mul le_rfl (add_le_add hR hL)
  calc (runCountSum x : ℝ)
      ≤ ((∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          2 * p * ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
            (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card) :
          ℕ) : ℝ) := Nat.cast_le.mpr hnat
    _ = ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (2 * (p : ℝ) *
            (((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
              (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card :
              ℕ) : ℝ)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro p _
        push_cast
        ring
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (2 * (p : ℝ) * (C * (smoothCount (2 * x + 1) p : ℝ) /
            (p : ℝ) ^ 2 * (Real.log (Real.log x)) ^ K)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact heq p hp (Nat.prime_of_mem_primesLE hp)
    _ = 2 * C * (Real.log (Real.log x)) ^ K *
          ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpR : (p : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primesLE hp).ne_zero
        field_simp
        ring

/-- **The `Ψ/p`-weight hypothesis** (the crude route): the `1/p`-weighted
smooth count over `p ≤ √(2x)` is bounded by `S·(log x)^{-1}·(log log x)^K`.

*Honesty note:* this is a *stronger* assumption than `SmoothSqWeightHyp` —
the `1/p` weight (forced by the `2p·T₁` diagonal collapse) sits on a
different saddle than `S`, so this hypothesis packages both the
equidistribution *and* the run-length loss into one weight condition.  It is
recorded because it is exactly what the collapsed reduction needs; the
diagonal/tail split above (`SmoothSqWeightHyp` + `LongRunTailHyp`) is the
finer and more faithful sharpening of the wall. -/
def SmoothWeightHyp : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ)) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K

/-- **Conditional closure via the `Ψ/p` weight** (equidistribution + the
`1/p`-weighted smooth-sum comparison). -/
theorem badNonSingleton_interval_bound_of_equidist_and_weight
    (hE : SmoothEquidistHyp) (hW : SmoothWeightHyp) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨C, K₁, hC, hE'⟩ := hE
  obtain ⟨K₂, hW'⟩ := hW
  have hlt : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hf : ∀ᶠ x : ℕ in atTop,
      (runCountSum x : ℝ) ≤ (2 * C) * (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ (K₁ + K₂) := by
    filter_upwards [hE', hW', hlt.eventually_ge_atTop 1] with x hEx hWx ht1
    have ht0 : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := by linarith
    have hfac : (0 : ℝ) ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ :=
      mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le _)
    calc (runCountSum x : ℝ)
        ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ *
            ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
              (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) :=
          runCountSum_le_smoothWeight_of_equidist hEx
      _ ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ *
            ((badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
              (Real.log (Real.log x)) ^ K₂) :=
          mul_le_mul_of_nonneg_left hWx hfac
      _ = (2 * C) * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            ((Real.log (Real.log x)) ^ K₁ * (Real.log (Real.log x)) ^ K₂) := by
          ring
      _ = (2 * C) * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            (Real.log (Real.log x)) ^ (K₁ + K₂) := by
          rw [Real.rpow_add ht0]
  exact badNonSingleton_interval_bound_of_runCountSum_loglog
    (exists_loglog_bound_of_mul_const (2 * C) (K₁ + K₂) (by linarith) hf)

/-! ### The banded variant (small/mid band + large-`p` tail)

The task's suggested two-part hypothesis: equidistribution handles the
small/mid band `p ≤ B(x)`, while the large-`p` tail is bounded directly on
the run sum (for `p` large the `2p` multiplicity is too big for the `Ψ/p`
weight route — the tail hypothesis is genuinely a different input). -/

/-- The small band: primes `p ≤ √(2x)` with `p ≤ B`. -/
def bandPrimes (x B : ℕ) : Finset ℕ :=
  (Nat.primesLE (Nat.sqrt (2 * x))).filter (· ≤ B)

/-- The large band: primes `p ≤ √(2x)` with `B < p`. -/
def largeBandPrimes (x B : ℕ) : Finset ℕ :=
  (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => B < p)

/-- The run sum restricted to the small band. -/
noncomputable def bandRunSum (x B : ℕ) : ℕ :=
  ∑ p ∈ bandPrimes x B,
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- The run sum restricted to the large band. -/
noncomputable def largeRunSum (x B : ℕ) : ℕ :=
  ∑ p ∈ largeBandPrimes x B,
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- The prime range splits into the two bands. -/
theorem primesLE_eq_band_union_large (x B : ℕ) :
    Nat.primesLE (Nat.sqrt (2 * x)) = bandPrimes x B ∪ largeBandPrimes x B := by
  ext p
  simp only [bandPrimes, largeBandPrimes, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hp
    rcases le_or_lt p B with h | h
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, h⟩
  · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp

/-- The two bands are disjoint. -/
theorem bandPrimes_disjoint_largeBandPrimes (x B : ℕ) :
    Disjoint (bandPrimes x B) (largeBandPrimes x B) := by
  rw [Finset.disjoint_left]
  intro q hq1 hq2
  obtain ⟨-, hle⟩ := Finset.mem_filter.mp hq1
  obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hq2
  omega

/-- **Band split of the run sum**:
`runCountSum x = bandRunSum x B + largeRunSum x B` for any cutoff `B`. -/
theorem runCountSum_eq_band_add_large (x B : ℕ) :
    runCountSum x = bandRunSum x B + largeRunSum x B := by
  unfold runCountSum bandRunSum largeRunSum
  conv_lhs => rw [primesLE_eq_band_union_large x B]
  exact Finset.sum_union (bandPrimes_disjoint_largeBandPrimes x B)

/-- **Equidistribution on the small band only** (the `k = 1` smooth-class
input, for `p ≤ B x`). -/
def SmallBandEquidistHyp (B : ℕ → ℕ) : Prop :=
  ∃ C K : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in atTop,
    ∀ p ∈ bandPrimes x (B x), Nat.Prime p → smoothEquidistBoundAt x p C K

/-- The full equidistribution hypothesis implies the small-band one. -/
theorem SmoothEquidistHyp.toSmallBand (h : SmoothEquidistHyp) (B : ℕ → ℕ) :
    SmallBandEquidistHyp B := by
  obtain ⟨C, K, hC, hE'⟩ := h
  refine ⟨C, K, hC, ?_⟩
  filter_upwards [hE'] with x hx p hp
  exact hx p (Finset.mem_filter.mp hp).1

/-- **The small-band `Ψ/p` weight hypothesis**: the `1/p`-weighted smooth
count over `p ≤ B x` is bounded by `S·(log x)^{-1}·(log log x)^K`. -/
def SmallBandWeightHyp (B : ℕ → ℕ) : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    (∑ p ∈ bandPrimes x (B x),
        (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ)) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K

/-- **The large-band run-tail hypothesis**: the full run sum over primes
`B x < p ≤ √(2x)` is at most `S·(log x)^{-1}·(log log x)^K`.  For `p` large
the `2p` multiplicity is too coarse for the `Ψ/p` route, so the run-length
structure must be bounded directly — this is where the second-moment input
of Ta26c lives. -/
def LargeBandRunTailHyp (B : ℕ → ℕ) : Prop :=
  ∃ K : ℝ, ∀ᶠ x : ℕ in atTop,
    ((largeRunSum x (B x) : ℕ) : ℝ) ≤
      (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
        (Real.log (Real.log x)) ^ K

/-- **Pointwise small-band bound under equidistribution**: the small-band run
sum is at most `2C·(log log x)^K·∑_{p ≤ B x} Ψ(2x+1, p)/p`. -/
theorem bandRunSum_le_smoothWeight_of_equidist {x B : ℕ} {C K : ℝ}
    (heq : ∀ p ∈ bandPrimes x B, Nat.Prime p →
      smoothEquidistBoundAt x p C K) :
    (bandRunSum x B : ℝ) ≤
      2 * C * (Real.log (Real.log x)) ^ K *
        ∑ p ∈ bandPrimes x B, (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) := by
  have hnat : bandRunSum x B ≤
      ∑ p ∈ bandPrimes x B,
        2 * p * ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
          (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card) := by
    unfold bandRunSum
    apply Finset.sum_le_sum
    intro p hp
    have hpp : p.Prime :=
      Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
    have hinner : ∑ k ∈ Finset.Icc 1 (2 * p),
        (rightRunCount x p k + leftRunCount x p k) ≤
        2 * p * (rightRunCount x p 1 + leftRunCount x p 1) := by
      rw [Finset.sum_add_distrib]
      calc ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k +
            ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k
          ≤ 2 * p * rightRunCount x p 1 + 2 * p * leftRunCount x p 1 :=
            add_le_add (sum_Icc_rightRunCount_le x p)
              (sum_Icc_leftRunCount_le x p)
        _ = 2 * p * (rightRunCount x p 1 + leftRunCount x p 1) := by ring
    refine hinner.trans ?_
    have hR : rightRunCount x p 1 ≤
        (smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card := by
      refine (rightRunCount_one_le_apSmoothParamCount hpp).trans_eq ?_
      exact apSmoothParamCount_one_eq_smoothCongruentOne _ _ hpp.two_le
    have hL := leftRunCount_one_le_smoothCongruentNegOne hpp
    exact Nat.mul_le_mul le_rfl (add_le_add hR hL)
  calc (bandRunSum x B : ℝ)
      ≤ ((∑ p ∈ bandPrimes x B,
          2 * p * ((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
            (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card) :
          ℕ) : ℝ) := Nat.cast_le.mpr hnat
    _ = ∑ p ∈ bandPrimes x B,
          (2 * (p : ℝ) *
            (((smoothCongruentOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card +
              (smoothCongruentNegOne (p ^ 2 * (2 * x / p ^ 2) + 1) p).card :
              ℕ) : ℝ)) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro p _
        push_cast
        ring
    _ ≤ ∑ p ∈ bandPrimes x B,
          (2 * (p : ℝ) * (C * (smoothCount (2 * x + 1) p : ℝ) /
            (p : ℝ) ^ 2 * (Real.log (Real.log x)) ^ K)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact heq p hp
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
    _ = 2 * C * (Real.log (Real.log x)) ^ K *
          ∑ p ∈ bandPrimes x B,
            (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1).ne_zero
        field_simp
        ring

/-- **Conditional closure via the banded hypotheses** (small-band
equidistribution + small-band `Ψ/p` weight + large-band run tail). -/
theorem badNonSingleton_interval_bound_of_banded (B : ℕ → ℕ)
    (hE : SmallBandEquidistHyp B) (hW : SmallBandWeightHyp B)
    (hT : LargeBandRunTailHyp B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨C, K₁, hC, hE'⟩ := hE
  obtain ⟨K₂, hW'⟩ := hW
  obtain ⟨K₃, hT'⟩ := hT
  have hlt : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hf : ∀ᶠ x : ℕ in atTop,
      ((bandRunSum x (B x) : ℕ) : ℝ) ≤ (2 * C) * (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ (K₁ + K₂) := by
    filter_upwards [hE', hW', hlt.eventually_ge_atTop 1] with x hEx hWx ht1
    have ht0 : (0 : ℝ) < Real.log (Real.log (x : ℝ)) := by linarith
    have hfac : (0 : ℝ) ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ :=
      mul_nonneg (by linarith) (Real.rpow_nonneg ht0.le _)
    calc ((bandRunSum x (B x) : ℕ) : ℝ)
        ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ *
            ∑ p ∈ bandPrimes x (B x),
              (smoothCount (2 * x + 1) p : ℝ) / (p : ℝ) :=
          bandRunSum_le_smoothWeight_of_equidist hEx
      _ ≤ 2 * C * (Real.log (Real.log x)) ^ K₁ *
            ((badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
              (Real.log (Real.log x)) ^ K₂) :=
          mul_le_mul_of_nonneg_left hWx hfac
      _ = (2 * C) * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            ((Real.log (Real.log x)) ^ K₁ * (Real.log (Real.log x)) ^ K₂) := by
          ring
      _ = (2 * C) * (badSingletonCount x : ℝ) * (Real.log x) ^ (-(1 : ℝ)) *
            (Real.log (Real.log x)) ^ (K₁ + K₂) := by
          rw [Real.rpow_add ht0]
  have hg : ∀ᶠ x : ℕ in atTop,
      ((largeRunSum x (B x) : ℕ) : ℝ) ≤ 1 * (badSingletonCount x : ℝ) *
        (Real.log x) ^ (-(1 : ℝ)) * (Real.log (Real.log x)) ^ K₃ := by
    filter_upwards [hT'] with x hx
    simpa using hx
  obtain ⟨K', hK'⟩ := exists_loglog_bound_of_two
    (f := fun x => bandRunSum x (B x)) (g := fun x => largeRunSum x (B x))
    (2 * C) 1 (K₁ + K₂) K₃ (by linarith) one_pos.le hf hg
  refine badNonSingleton_interval_bound_of_runCountSum_loglog ⟨K', ?_⟩
  filter_upwards [hK'] with x hx
  have heq : (runCountSum x : ℝ) =
      ((bandRunSum x (B x) : ℕ) : ℝ) + ((largeRunSum x (B x) : ℕ) : ℝ) := by
    rw [← Nat.cast_add]
    exact congrArg Nat.cast (runCountSum_eq_band_add_large x (B x))
  rw [heq]
  exact hx

end JSP314

section AxiomCheck

#print axioms JSP314.rightRunWitness_subset_one
#print axioms JSP314.rightRunCount_le_one
#print axioms JSP314.leftRunCount_le_one
#print axioms JSP314.leftRunCount_one_le_smoothCongruentNegOne
#print axioms JSP314.leftRunCount_one_le_smoothCount
#print axioms JSP314.leftRunCount_one_le_real
#print axioms JSP314.runCountSum_eq_diag_add_tail
#print axioms JSP314.sum_runCount_one_le_two_mul_shortBadCount
#print axioms JSP314.runCountSum_eventually_le_of_hyps
#print axioms JSP314.badNonSingleton_interval_bound_of_antiSieve_hyps
#print axioms JSP314.badNonSingleton_interval_bound_of_equidist_and_weight
#print axioms JSP314.badNonSingleton_interval_bound_of_banded

end AxiomCheck
