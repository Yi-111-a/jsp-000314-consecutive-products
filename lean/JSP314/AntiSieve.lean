import JSP314.RunSieve
import JSP314.ErdosTk
import Mathlib.Tactic

/-!
# JSP-000314 — the anti-sieve: anatomy of `p`-smooth numbers in the
class `1 (mod p²)`

This file formalizes the **elementary** part of Tao's anti-sieve
(Propositions 6.6–6.8 of arXiv:2603.27990) needed for the last open band
`p₀ ∈ (z^{0.6}, z^{2.9})` of `badNonSingleton_interval_bound`.

The missing estimate is

  `T₁ = #{r ≤ 2x/p₀² : p₀²r + 1 is p₀-smooth}  ≪  Ψ(2x, p₀)·p₀^{-2+o(1)}`,

i.e. the `p₀`-smooth integers `s = p₀²r + 1` are `≍ 1/p₀²`-dense inside the
`p₀`-smooths — smooth numbers equidistribute into the coprime classes
`mod p₀²`.

## What is proved here (no sorries)

* `smoothCongruentOne N p` — the anti-sieve set: `p`-smooth `s ∈ [2, N]`
  with `s ≡ 1 (mod p²)`.
* `apSmoothParamCount_one_eq_smoothCongruentOne` — **count-level equality**
  `T₁ = |smoothCongruentOne (p²·hi + 1) p|` via the bijection `r ↦ p²r + 1`
  (Task 1).
* **Anatomy lemma** (`cofactorPair_mem_of_mem`): every `s` in the
  anti-sieve set factors *uniquely* as `s = q·m` with `q = largestPrimeFactor s`
  prime, `q < p` (since `s ≡ 1 (mod p)` forces `p ∤ s`), `m = s/q`
  `q`-smooth, `q·m ≤ N` and `q·m ≡ 1 (mod p²)`.
* `card_smoothCongruentOne_le_cofactorFinset` — injection of the
  anti-sieve set into the cofactor-pair set `cofactorFinset`.
* `cofactorPair_q_unique` — **at most one admissible `q` per `m`**:
  `q₁m ≡ q₂m ≡ 1 (mod p²)` with `q₁, q₂ ≤ p − 1` forces `q₁ = q₂`
  (`m` is coprime to `p²`, and the class `m⁻¹ mod p²` meets `[1, p−1]`
  at most once since `p − 1 < p²`).  Consequences:
  `cofactorFinset_fiber_le_one`, `cofactorFinset_card_le_smoothCount`,
  `apSmoothParamCount_one_le_smoothCount`, `rightRunCount_one_le_smoothCount`
  — this is the "T₁ ≤ Ψ(N, p−1)" Rankin-recovery bound (Task 2).
* `smoothCongruentOne_card_eq_sum_fiber` — exact decomposition
  `|smoothCongruentOne| = ∑_{q prime < p} |{s : lpf s = q}|`, and
  `smoothCongruentOne_card_le_sum_partner` — the per-prime bound
  `T₁ ≤ ∑_{q<p} #{m ≤ N/q : m q-smooth, q·m ≡ 1 (mod p²)}` (Task 1).
* `card_residue_class_le`, `smoothPartnerCount_le` — the inner count is
  at most `M/K + 1` (solutions of `q·m ≡ 1 (mod K)` lie in a single
  class mod `K`, when solvable at all).
* `smoothCongruentOne_card_le_sum`,
  `smoothCongruentOne_card_le_real`,
  `apSmoothParamCount_one_le_real`, `rightRunCount_one_le_real` —
  the explicit unconditional bound
  `T₁ ≤ (N/p²)·(1 + log(p−1)) + p`.

## Where the `p₀^{-2}` saving must come from (the math wall)

The elementary reduction gives `T₁ ≤ Σ_{q<p} S_q` with
`S_q = #{m ≤ N/q : lpf m ≤ q, q·m ≡ 1 (mod p²)}`.  Two facts are proved
above:

1. each `m` admits **at most one** `q` (the class `m⁻¹ mod p²` meets
   `[1,p−1]` at most once, and it must additionally be prime and
   satisfy `q·m ≤ N`); heuristically only a `~1/p` fraction of `m`'s
   have `m⁻¹ mod p² ∈ [1, p)`, and only ~`1/log p` of those are prime —
   this is exactly the `p₀^{-2}` saving;
2. dropping smoothness, `S_q ≤ N/(qp²) + 1`, giving
   `T₁ ≤ (N/p²)·Σ_{q<p}1/q + p ≈ (N/p²)·log log p + p` — *worse* than the
   trivial `N/p²` bound.

So the saving is provably invisible to class-counting: one needs
`#{m ≤ M : m q-smooth, m ≡ q⁻¹ (mod p²)} ≍ Ψ(M,q)/p²`, i.e.
**equidistribution of `q`-smooth numbers among the coprime classes
`mod p²` with `p²` *larger* than the smoothness bound `q`**.  That is
the analytic input of Tao's Props 6.6–6.8 (character-sum/Halász–Montgomery
estimates for smooth-supported sequences, i.e. `Σ_{m ≡ a (p²)} Λ_q(m)`
vs `Ψ(M,q)`, together with the second-moment `X_{p,l}` bounds).
Every reduction needed to *apply* that input — the cofactor anatomy,
the fiber uniqueness, the per-prime partner decomposition and the
residue-class count — is proved above; the missing piece is purely the
equidistribution statement, which has no elementary proof (it already
fails for the analogous inverse-in-short-interval count without
Kloosterman-type input).
-/

namespace JSP314

open Finset

/-! ### Definitions -/

/-- **Ψ-type finset**: `s ∈ [1, N]` with `largestPrimeFactor s ≤ y`. -/
def smoothFinset (N y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun s => largestPrimeFactor s ≤ y

/-- `smoothCount N y = Ψ(N, y)`: the number of `y`-smooth integers in `[1, N]`. -/
noncomputable def smoothCount (N y : ℕ) : ℕ := (smoothFinset N y).card

/-- The **anti-sieve target**: `p`-smooth `s ∈ [2, N]` with `s ≡ 1 (mod p²)`.
Counting this set at `N = p²·hi + 1` is exactly `apSmoothParamCount 1 hi (p²) 1 p`
(`apSmoothParamCount_one_eq_smoothCongruentOne`). -/
def smoothCongruentOne (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun s =>
    largestPrimeFactor s ≤ p ∧ s % (p ^ 2) = 1

/-- The **cofactor–partner set**: `m ∈ [1, M]` that is `y`-smooth and satisfies
`q·m ≡ 1 (mod K)` (i.e. `m` lies in the class `q⁻¹ mod K`). -/
def smoothPartnerFinset (M y K q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter fun m =>
    largestPrimeFactor m ≤ y ∧ q * m ≡ 1 [MOD K]

/-- Its cardinality. -/
noncomputable def smoothPartnerCount (M y K q : ℕ) : ℕ :=
  (smoothPartnerFinset M y K q).card

/-- The **cofactor-pair set**: pairs `(m, q)` with `q ∈ [1, p − 1]` prime,
`m` `q`-smooth, `q·m ≡ 1 (mod p²)` and `q·m ≤ N`.  The anatomy map
`s ↦ (s / largestPrimeFactor s, largestPrimeFactor s)` injects
`smoothCongruentOne N p` into this set. -/
def cofactorFinset (N p : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 (p - 1))).filter fun ⟨m, q⟩ =>
    q.Prime ∧ largestPrimeFactor m ≤ q ∧ q * m ≡ 1 [MOD p ^ 2] ∧ q * m ≤ N

theorem mem_smoothCongruentOne {N p s : ℕ} :
    s ∈ smoothCongruentOne N p ↔
      2 ≤ s ∧ s ≤ N ∧ largestPrimeFactor s ≤ p ∧ s % p ^ 2 = 1 := by
  simp only [smoothCongruentOne, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem mem_smoothPartnerFinset {M y K q m : ℕ} :
    m ∈ smoothPartnerFinset M y K q ↔
      1 ≤ m ∧ m ≤ M ∧ largestPrimeFactor m ≤ y ∧ q * m ≡ 1 [MOD K] := by
  simp only [smoothPartnerFinset, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem mem_cofactorFinset {N p m q : ℕ} :
    (m, q) ∈ cofactorFinset N p ↔
      1 ≤ m ∧ m ≤ N ∧ 1 ≤ q ∧ q ≤ p - 1 ∧ q.Prime ∧
        largestPrimeFactor m ≤ q ∧ q * m ≡ 1 [MOD p ^ 2] ∧ q * m ≤ N := by
  simp only [cofactorFinset, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]
  tauto

/-! ### Basic lemmas -/

/-- Monotonicity of `largestPrimeFactor` under divisibility. -/
theorem largestPrimeFactor_le_of_dvd {m s : ℕ} (h : m ∣ s) (hs : 2 ≤ s) :
    largestPrimeFactor m ≤ largestPrimeFactor s := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [largestPrimeFactor_eq_one_iff.mpr (by omega : m ≤ 1)]
    exact (one_lt_largestPrimeFactor hs).le
  · rw [largestPrimeFactor_eq_maxPrimeFac hm,
        largestPrimeFactor_eq_maxPrimeFac hs,
        Nat.maxPrimeFac_le_iff (by omega : 1 < m)]
    intro r hrp hrd
    exact Nat.le_maxPrimeFac (by omega : s ≠ 0) hrp (hrd.trans h)

/-- For `p ≥ 2`, `s ≡ 1 (mod p²)` is the same as `s % p² = 1`. -/
theorem modEq_one_iff {s p : ℕ} (hp : 2 ≤ p) :
    s ≡ 1 [MOD p ^ 2] ↔ s % p ^ 2 = 1 := by
  have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (one_lt_two.trans_le hp)
  rw [Nat.ModEq, Nat.mod_eq_of_lt h2]

/-- The largest prime factor of an anti-sieve element is *strictly* below `p`:
`s ≡ 1 (mod p)` forces `p ∤ s`. -/
theorem lpf_lt_of_mem_smoothCongruentOne {N p s : ℕ} (hp : 2 ≤ p)
    (hs : s ∈ smoothCongruentOne N p) :
    largestPrimeFactor s < p := by
  obtain ⟨hs2, -, hlpf, hmod⟩ := mem_smoothCongruentOne.mp hs
  have hps : s % p = 1 := by
    have h := Nat.mod_mod_of_dvd s (dvd_pow_self p two_ne_zero)
    rw [hmod, Nat.mod_eq_of_lt (one_lt_two.trans_le hp)] at h
    exact h.symm
  rcases lt_trichotomy (largestPrimeFactor s) p with h | h | h
  · exact h
  · exfalso
    have hd : p ∣ s := h ▸ largestPrimeFactor_dvd hs2
    have : s % p = 0 := Nat.mod_eq_zero_of_dvd hd
    omega
  · omega

/-- Monotonicity of `smoothCongruentOne` in the ambient bound. -/
theorem smoothCongruentOne_mono {N₁ N₂ p : ℕ} (h : N₁ ≤ N₂) :
    smoothCongruentOne N₁ p ⊆ smoothCongruentOne N₂ p := by
  intro s hs
  obtain ⟨hs2, hsN, hlp, hmod⟩ := mem_smoothCongruentOne.mp hs
  exact mem_smoothCongruentOne.mpr ⟨hs2, hsN.trans h, hlp, hmod⟩

/-- Monotonicity of `smoothCount` in the ambient bound. -/
theorem smoothCount_mono {N₁ N₂ y : ℕ} (h : N₁ ≤ N₂) :
    smoothCount N₁ y ≤ smoothCount N₂ y := by
  apply Finset.card_le_card
  intro s hs
  simp only [smoothFinset, Finset.mem_filter] at hs ⊢
  obtain ⟨hsI, hlp⟩ := hs
  obtain ⟨hs1, hsN⟩ := Finset.mem_Icc.mp hsI
  exact ⟨Finset.mem_Icc.mpr ⟨hs1, hsN.trans h⟩, hlp⟩

/-! ### Bridge lemmas (formerly imported from `JSP314.APPsi`)

`JSP314.APPsi` is currently broken upstream, so the handful of results this
file needs from it — the `rightRunCount → apSmoothParamCount` injection and
the harmonic/prime-reciprocal bounds — are proved here directly (identical
statements and proofs, no new content). -/

/-- For a `k = 1` right run witness `m`, `r = m/p²` lies in `[1, 2x/p²]` and
`p²·r + 1 = m + 1` is `p`-smooth. -/
theorem rightRunWitness_one_div_mem {x p m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ rightRunWitness x p 1) :
    m / p ^ 2 ∈ (Finset.Icc 1 (2 * x / p ^ 2)).filter
      (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p) := by
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hp2, Nat.div_le_div_right hm2x⟩,
    ?_⟩
  have hrew : p ^ 2 * (m / p ^ 2) + 1 = m + 1 := by
    rw [Nat.mul_div_cancel' hdvd]
  rw [hrew]
  exact hsmooth (m + 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)

/-- **Bridge (right):** `rightRunCount x p 1` is at most the AP smooth count
`apSmoothParamCount 1 (2x/p²) (p²) 1 p`. -/
theorem rightRunCount_one_le_apSmoothParamCount {x p : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p 1 ≤ apSmoothParamCount 1 (2 * x / p ^ 2) (p ^ 2) 1 p := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe]
    exact rightRunWitness_one_div_mem hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_rightRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_rightRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

/-- `1/(N+1) ≤ log(N+1) − log N` for `N ≥ 1`. -/
theorem one_div_succ_le_log_sub_log {N : ℕ} (hN : 1 ≤ N) :
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
theorem sum_range_one_div_succ_le (N : ℕ) :
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
theorem sum_primesLE_inv_le (y : ℕ) :
    ∑ p ∈ Nat.primesLE y, (1 : ℝ) / p ≤ 1 + Real.log y := by
  rw [Nat.primesLE_eq_filter_range]
  calc ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime, (1 : ℝ) / p
      ≤ ∑ n ∈ Finset.range (y + 1), (1 : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => by positivity
    _ = ∑ i ∈ Finset.range y, (1 : ℝ) / ((i : ℝ) + 1) := by
        rw [Finset.sum_range_succ', Nat.cast_zero, div_zero, add_zero]
        apply Finset.sum_congr rfl
        intro i _
        rw [Nat.cast_add, Nat.cast_one]
    _ ≤ 1 + Real.log y := sum_range_one_div_succ_le y

/-! ### Task 1: the count-level identity `T₁ = |smoothCongruentOne|` -/

/-- **Count-level identity.**  `r ↦ p²·r + 1` is a bijection between the
parameter set counted by `apSmoothParamCount 1 hi (p²) 1 p` and the
`p`-smooth `s ≤ p²·hi + 1` congruent to `1 mod p²`. -/
theorem apSmoothParamCount_one_eq_smoothCongruentOne (hi p : ℕ) (hp : 2 ≤ p) :
    apSmoothParamCount 1 hi (p ^ 2) 1 p =
      (smoothCongruentOne (p ^ 2 * hi + 1) p).card := by
  classical
  have hp2 : 0 < p ^ 2 := Nat.pow_pos (show 0 < p by omega)
  have hp2' : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (one_lt_two.trans_le hp)
  apply Finset.card_bij (fun r _ => p ^ 2 * r + 1)
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrIcc, hlpf⟩ := hr
    obtain ⟨hr1, hrhi⟩ := Finset.mem_Icc.mp hrIcc
    rw [mem_smoothCongruentOne]
    have hrpos : 1 ≤ p ^ 2 * r := Nat.mul_pos hp2 hr1
    refine ⟨by omega, Nat.add_le_add_right (Nat.mul_le_mul_left _ hrhi) 1,
      hlpf, ?_⟩
    rw [show p ^ 2 * r + 1 = 1 + r * p ^ 2 by rw [mul_comm, add_comm],
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp2']
  · intro a₁ _ a₂ _ h
    have h' : p ^ 2 * a₁ = p ^ 2 * a₂ := by omega
    exact Nat.eq_of_mul_eq_mul_left hp2 h'
  · intro s hs
    obtain ⟨hs2, hsN, hlpf, hmod⟩ := mem_smoothCongruentOne.mp hs
    have hdivmod : p ^ 2 * (s / p ^ 2) + 1 = s := by
      have h := Nat.div_add_mod s (p ^ 2)
      omega
    refine ⟨s / p ^ 2, ?_, hdivmod⟩
    rw [Finset.mem_filter]
    have hpos : 1 ≤ s / p ^ 2 := by
      rcases Nat.eq_zero_or_pos (s / p ^ 2) with h0 | h0
      · exfalso
        rw [h0] at hdivmod
        simp at hdivmod
        omega
      · exact h0
    have hle : s / p ^ 2 ≤ hi :=
      Nat.le_of_mul_le_mul_left
        (show p ^ 2 * (s / p ^ 2) ≤ p ^ 2 * hi by omega) hp2
    exact ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩, by rwa [hdivmod]⟩

/-! ### Task 1/2: the cofactor anatomy -/

/-- **Anatomy lemma.**  For `s` in the anti-sieve set, `q = largestPrimeFactor s`
is prime, `1 ≤ q ≤ p − 1`, `m = s/q` is `q`-smooth, `q·m ≡ 1 (mod p²)`
and `q·m = s ≤ N`: the pair `(m, q)` lies in `cofactorFinset N p`. -/
theorem cofactorPair_mem_of_mem {N p s : ℕ} (hp : 2 ≤ p)
    (hs : s ∈ smoothCongruentOne N p) :
    (s / largestPrimeFactor s, largestPrimeFactor s) ∈ cofactorFinset N p := by
  obtain ⟨hs2, hsN, hlpf, hmod⟩ := mem_smoothCongruentOne.mp hs
  have hqprime : (largestPrimeFactor s).Prime := largestPrimeFactor_prime hs2
  have hq2 := hqprime.two_le
  have hqdvd : largestPrimeFactor s ∣ s := largestPrimeFactor_dvd hs2
  have hqlt : largestPrimeFactor s < p := lpf_lt_of_mem_smoothCongruentOne hp hs
  have hm1 : 1 ≤ s / largestPrimeFactor s :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hqprime.pos
  have hmul : largestPrimeFactor s * (s / largestPrimeFactor s) = s :=
    Nat.mul_div_cancel' hqdvd
  rw [mem_cofactorFinset]
  refine ⟨hm1, (Nat.div_le_self _ _).trans hsN, by omega, by omega, hqprime,
    largestPrimeFactor_le_of_dvd (Nat.div_dvd_of_dvd hqdvd) hs2, ?_, ?_⟩
  · rw [hmul]
    exact (modEq_one_iff hp).mpr hmod
  · rw [hmul]
    exact hsN

/-- The anatomy map is injective, so the anti-sieve count is at most the
number of cofactor pairs. -/
theorem card_smoothCongruentOne_le_cofactorFinset (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card ≤ (cofactorFinset N p).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun s => (s / largestPrimeFactor s, largestPrimeFactor s))
  · intro s hs
    rw [Finset.mem_coe] at hs ⊢
    exact cofactorPair_mem_of_mem hp hs
  · intro a ha b hb hab
    have ha2 : 2 ≤ a := (mem_smoothCongruentOne.mp (Finset.mem_coe.mp ha)).1
    have hb2 : 2 ≤ b := (mem_smoothCongruentOne.mp (Finset.mem_coe.mp hb)).1
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

/-! ### Coprimality and cancellation mod `K` -/

/-- If `a·b ≡ 1 (mod K)` with `K > 0`, then each factor is coprime to `K`. -/
theorem coprime_of_mul_modEq_one {K a b : ℕ} (hK : 0 < K)
    (h : a * b ≡ 1 [MOD K]) :
    Nat.Coprime a K ∧ Nat.Coprime b K := by
  by_cases hK1 : K = 1
  · subst hK1
    exact ⟨Nat.gcd_one_right a, Nat.gcd_one_right b⟩
  have hK1 : 1 < K := by omega
  have hmod : (a * b) % K = 1 := by
    rw [Nat.ModEq, Nat.mod_eq_of_lt hK1] at h
    exact h
  have hdiv : a * b = K * ((a * b) / K) + 1 := by
    have := Nat.div_add_mod (a * b) K
    omega
  have hsub : a * b - K * ((a * b) / K) = 1 := by omega
  have hg1 : Nat.gcd a K ∣ 1 := by
    have h1 : Nat.gcd a K ∣ a * b :=
      (Nat.gcd_dvd_left a K).trans (dvd_mul_right a b)
    have h2 : Nat.gcd a K ∣ K * ((a * b) / K) :=
      (Nat.gcd_dvd_right a K).trans (dvd_mul_right K _)
    have h3 := Nat.dvd_sub h1 h2
    rwa [hsub] at h3
  have hg2 : Nat.gcd b K ∣ 1 := by
    have h1 : Nat.gcd b K ∣ a * b :=
      (Nat.gcd_dvd_left b K).trans (dvd_mul_left b a)
    have h2 : Nat.gcd b K ∣ K * ((a * b) / K) :=
      (Nat.gcd_dvd_right b K).trans (dvd_mul_right K _)
    have h3 := Nat.dvd_sub h1 h2
    rwa [hsub] at h3
  constructor
  · have hpos : 0 < Nat.gcd a K := Nat.gcd_pos_of_pos_right a hK
    have hle : Nat.gcd a K ≤ 1 := Nat.le_of_dvd one_pos hg1
    show Nat.gcd a K = 1
    omega
  · have hpos : 0 < Nat.gcd b K := Nat.gcd_pos_of_pos_right b hK
    have hle : Nat.gcd b K ≤ 1 := Nat.le_of_dvd one_pos hg2
    show Nat.gcd b K = 1
    omega

/-- Cancellation: if `q·m₁` and `q·m₂` are both `≡ 1 (mod K)` then
`m₁ ≡ m₂ (mod K)`. -/
theorem modEq_of_mul_modEq_one {K q m₁ m₂ : ℕ} (hK : 0 < K)
    (h1 : q * m₁ ≡ 1 [MOD K]) (h2 : q * m₂ ≡ 1 [MOD K]) :
    m₁ ≡ m₂ [MOD K] := by
  have hcop : Nat.Coprime K q := ((coprime_of_mul_modEq_one hK h1).1).symm
  rcases le_total m₁ m₂ with h | h
  · have hmul : q * m₁ ≤ q * m₂ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₂ - q * m₁ :=
      (Nat.modEq_iff_dvd' hmul).mp (h1.trans h2.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact (Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)
  · have hmul : q * m₂ ≤ q * m₁ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₁ - q * m₂ :=
      (Nat.modEq_iff_dvd' hmul).mp (h2.trans h1.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact ((Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)).symm

/-! ### At most one admissible `q` per cofactor `m` -/

/-- **Fiber uniqueness.**  Two cofactor pairs with the same `m` have the
same `q`: the class `m⁻¹ (mod p²)` meets `[1, p − 1]` at most once. -/
theorem cofactorPair_q_unique {N p m q₁ q₂ : ℕ} (hp : 2 ≤ p)
    (h₁ : (m, q₁) ∈ cofactorFinset N p) (h₂ : (m, q₂) ∈ cofactorFinset N p) :
    q₁ = q₂ := by
  obtain ⟨-, -, hq1a, hqp1, -, -, hc1, -⟩ := mem_cofactorFinset.mp h₁
  obtain ⟨-, -, hq2a, hqp2, -, -, hc2, -⟩ := mem_cofactorFinset.mp h₂
  have hcong : q₁ ≡ q₂ [MOD p ^ 2] :=
    modEq_of_mul_modEq_one (Nat.pow_pos (show 0 < p by omega))
      (mul_comm q₁ m ▸ hc1) (mul_comm q₂ m ▸ hc2)
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

/-- The `m`-fiber of the cofactor set has at most one element. -/
theorem cofactorFinset_fiber_le_one {N p m : ℕ} (hp : 2 ≤ p) :
    ((cofactorFinset N p).filter fun e => e.1 = m).card ≤ 1 := by
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
  have hq : qa = qb := cofactorPair_q_unique hp hmema hmemb
  simp only [Prod.mk.injEq]
  exact ⟨hma.trans hmb.symm, hq⟩

/-- **Rankin recovery (per-`m` uniqueness form).**  The cofactor pairs
inject via `(m, q) ↦ m` into the `(p−1)`-smooth integers, so
`|cofactorFinset| ≤ Ψ(N, p−1)`. -/
theorem cofactorFinset_card_le_smoothCount (N p : ℕ) (hp : 2 ≤ p) :
    (cofactorFinset N p).card ≤ smoothCount N (p - 1) := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ⟨m, q⟩ hmq
    rw [Finset.mem_coe] at hmq ⊢
    obtain ⟨hm1, hmN, -, hqp, -, hmq', -, -⟩ := mem_cofactorFinset.mp hmq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, hmq'.trans hqp⟩
  · intro ⟨m₁, q₁⟩ h₁ ⟨m₂, q₂⟩ h₂ h
    have hm : m₁ = m₂ := h
    have h1 := Finset.mem_coe.mp h₁
    have h2 := Finset.mem_coe.mp h₂
    rw [hm] at h1
    have hq : q₁ = q₂ := cofactorPair_q_unique hp h1 h2
    rw [hm, hq]

/-- **Rankin recovery for `T₁`.**  `T₁ ≤ Ψ(p²·hi + 1, p − 1)`: each
`p`-smooth `s ≡ 1 (mod p²)` is determined by its `(p−1)`-smooth cofactor
`m = s/q`, and each `m` admits at most one `q`. -/
theorem apSmoothParamCount_one_le_smoothCount (hi p : ℕ) (hp : 2 ≤ p) :
    apSmoothParamCount 1 hi (p ^ 2) 1 p ≤
      smoothCount (p ^ 2 * hi + 1) (p - 1) := by
  rw [apSmoothParamCount_one_eq_smoothCongruentOne hi p hp]
  exact (card_smoothCongruentOne_le_cofactorFinset _ _ hp).trans
    (cofactorFinset_card_le_smoothCount _ _ hp)

/-! ### Per-prime partner decomposition -/

/-- The `q`-fiber (`largestPrimeFactor s = q`) of the anti-sieve set injects,
via `s ↦ s/q`, into the partner set `{m ≤ N/q : m q-smooth, q·m ≡ 1 (mod p²)}`. -/
theorem card_fiber_le_smoothPartner {N p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) :
    ((smoothCongruentOne N p).filter fun s => largestPrimeFactor s = q).card ≤
      smoothPartnerCount (N / q) q (p ^ 2) q := by
  classical
  apply Finset.card_le_card_of_injOn (· / q)
  · intro s hs
    rw [Finset.mem_coe] at hs ⊢
    obtain ⟨hs, hqs⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs2, hsN, -, hmod⟩ := mem_smoothCongruentOne.mp hs
    have hqdvd : q ∣ s := hqs ▸ largestPrimeFactor_dvd hs2
    rw [mem_smoothPartnerFinset]
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hq.pos,
      Nat.div_le_div_right hsN, ?_, ?_⟩
    · have h := largestPrimeFactor_le_of_dvd (Nat.div_dvd_of_dvd hqdvd) hs2
      rwa [hqs] at h
    · have hmul : q * (s / q) = s := Nat.mul_div_cancel' hqdvd
      rw [hmul]
      exact (modEq_one_iff hp).mpr hmod
  · intro a ha b hb hab
    obtain ⟨ha, hqa⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    obtain ⟨hb, hqb⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    have ha2 : 2 ≤ a := (mem_smoothCongruentOne.mp ha).1
    have hb2 : 2 ≤ b := (mem_smoothCongruentOne.mp hb).1
    have hda : q ∣ a := hqa ▸ largestPrimeFactor_dvd ha2
    have hdb : q ∣ b := hqb ▸ largestPrimeFactor_dvd hb2
    have hab' : a / q = b / q := hab
    calc a = q * (a / q) := (Nat.mul_div_cancel' hda).symm
      _ = q * (b / q) := by rw [hab']
      _ = b := Nat.mul_div_cancel' hdb

/-- **Exact fiber decomposition.**  The anti-sieve set is the disjoint
union, over primes `q < p`, of its `largestPrimeFactor = q` fibers:
`|smoothCongruentOne N p| = ∑_{q ∈ primesLE (p−1)} |{s : lpf s = q}|`. -/
theorem smoothCongruentOne_card_eq_sum_fiber (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card =
      ∑ q ∈ Nat.primesLE (p - 1),
        ((smoothCongruentOne N p).filter
          fun s => largestPrimeFactor s = q).card := by
  classical
  have hU : smoothCongruentOne N p = (Nat.primesLE (p - 1)).biUnion
      fun q => (smoothCongruentOne N p).filter
        fun s => largestPrimeFactor s = q := by
    ext s
    rw [Finset.mem_biUnion]
    constructor
    · intro hs
      obtain ⟨hs2, -, -, -⟩ := mem_smoothCongruentOne.mp hs
      refine ⟨largestPrimeFactor s, Nat.mem_primesLE.mpr ⟨?_, ?_⟩,
        Finset.mem_filter.mpr ⟨hs, rfl⟩⟩
      · have h := lpf_lt_of_mem_smoothCongruentOne hp hs
        omega
      · exact largestPrimeFactor_prime hs2
    · rintro ⟨q, -, hs⟩
      exact (Finset.mem_filter.mp hs).1
  have hdis : ((Nat.primesLE (p - 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun q => (smoothCongruentOne N p).filter
        fun s => largestPrimeFactor s = q := by
    intro q₁ _ q₂ _ hne
    exact Finset.disjoint_left.mpr fun s hs₁ hs₂ =>
      hne ((Finset.mem_filter.mp hs₁).2.symm.trans
        (Finset.mem_filter.mp hs₂).2)
  conv_lhs => rw [hU]
  rw [Finset.card_biUnion hdis]

/-- **Per-prime partner bound.**  `T₁ ≤ ∑_{q prime < p} Ψ_q(N/q; p², q⁻¹)`,
where the inner count is the `q`-smooth `m ≤ N/q` with `q·m ≡ 1 (mod p²)`. -/
theorem smoothCongruentOne_card_le_sum_partner (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), smoothPartnerCount (N / q) q (p ^ 2) q := by
  rw [smoothCongruentOne_card_eq_sum_fiber N p hp]
  apply Finset.sum_le_sum
  intro q hq
  exact card_fiber_le_smoothPartner hp (Nat.prime_of_mem_primesLE hq)

/-! ### The residue-class count -/

/-- Numbers in `[1, M]` lying in a fixed residue class `mod K` number at most
`M / K + 1` (inject `m ↦ m / K`). -/
theorem card_residue_class_le (M K a : ℕ) :
    ((Finset.Icc 1 M).filter fun m => m ≡ a [MOD K]).card ≤ M / K + 1 := by
  classical
  refine (Finset.card_le_card_of_injOn
    (t := Finset.Icc 0 (M / K)) (· / K) ?_ ?_).trans ?_
  · intro m hm
    obtain ⟨-, hmM⟩ := Finset.mem_Icc.mp
      (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).1
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hmM⟩
  · intro a ha b hb hab
    obtain ⟨-, hae⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    obtain ⟨-, hbe⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    have hmod : a % K = b % K := hae.trans hbe.symm
    have hda := Nat.div_add_mod a K
    have hdb := Nat.div_add_mod b K
    have hab' : a / K = b / K := hab
    calc a = K * (a / K) + a % K := hda.symm
      _ = K * (b / K) + b % K := by rw [hab', hmod]
      _ = b := hdb
  · have hcard : (Finset.Icc 0 (M / K)).card = M / K + 1 := by
      rw [Nat.card_Icc, Nat.sub_zero]
    exact le_of_eq hcard

/-- Any two elements of the partner set are congruent `mod K`. -/
theorem smoothPartner_modEq {M y K q m₁ m₂ : ℕ}
    (hm₁ : m₁ ∈ smoothPartnerFinset M y K q)
    (hm₂ : m₂ ∈ smoothPartnerFinset M y K q)
    (hq : Nat.Coprime q K) :
    m₁ ≡ m₂ [MOD K] := by
  obtain ⟨-, -, -, h1⟩ := mem_smoothPartnerFinset.mp hm₁
  obtain ⟨-, -, -, h2⟩ := mem_smoothPartnerFinset.mp hm₂
  have hcop : Nat.Coprime K q := hq.symm
  rcases le_total m₁ m₂ with h | h
  · have hmul : q * m₁ ≤ q * m₂ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₂ - q * m₁ :=
      (Nat.modEq_iff_dvd' hmul).mp (h1.trans h2.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact (Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)
  · have hmul : q * m₂ ≤ q * m₁ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₁ - q * m₂ :=
      (Nat.modEq_iff_dvd' hmul).mp (h2.trans h1.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact ((Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)).symm

/-- **Partner count bound (class count).**  `#{m ≤ M : q·m ≡ 1 (mod K),
m y-smooth} ≤ M/K + 1`: if `gcd(q,K) > 1` there are no solutions at all;
otherwise all solutions lie in a single class `mod K`. -/
theorem smoothPartnerCount_le (M y K q : ℕ) (hK : 0 < K) :
    smoothPartnerCount M y K q ≤ M / K + 1 := by
  classical
  by_cases hcop : Nat.Coprime q K
  · rcases (smoothPartnerFinset M y K q).eq_empty_or_nonempty with h | hne
    · simp [smoothPartnerCount, h]
    · obtain ⟨m₀, hm₀⟩ := hne
      have hsub : smoothPartnerFinset M y K q ⊆
          (Finset.Icc 1 M).filter fun m => m ≡ m₀ [MOD K] := by
        intro m hm
        obtain ⟨hm1, hmM, -, -⟩ := mem_smoothPartnerFinset.mp hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨hm1, hmM⟩, smoothPartner_modEq hm hm₀ hcop⟩
      exact (Finset.card_le_card hsub).trans (card_residue_class_le M K m₀)
  · have hempty : smoothPartnerFinset M y K q = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      obtain ⟨-, -, -, hcong⟩ := mem_smoothPartnerFinset.mp hm
      exact hcop (coprime_of_mul_modEq_one hK hcong).1
    simp [smoothPartnerCount, hempty]

/-- **Explicit unconditional bound.**  `T₁ ≤ ∑_{q prime < p} (N/(q·p²) + 1)`. -/
theorem smoothCongruentOne_card_le_sum (N p : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), (N / (q * p ^ 2) + 1) := by
  refine (smoothCongruentOne_card_le_sum_partner N p hp).trans ?_
  apply Finset.sum_le_sum
  intro q _
  calc smoothPartnerCount (N / q) q (p ^ 2) q
      ≤ N / q / p ^ 2 + 1 :=
        smoothPartnerCount_le _ _ _ _ (Nat.pow_pos (show 0 < p by omega))
    _ = N / (q * p ^ 2) + 1 := by rw [Nat.div_div_eq_div_mul]

/-- `|primesLE n| ≤ n + 1`. -/
theorem card_primesLE_le (n : ℕ) : (Nat.primesLE n).card ≤ n + 1 := by
  rw [Nat.primesLE_eq_filter_range]
  calc ((Finset.range (n + 1)).filter Nat.Prime).card
      ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range _

/-- **Real form of the elementary bound:**
`|smoothCongruentOne N p| ≤ (N/p²)·(1 + log(p−1)) + p`.

*Honesty note:* this is *worse* than the trivial bound `T₁ ≤ hi ≈ N/p²`
by the factor `Σ_{q<p} 1/q ~ log log p`; see the file's head comment —
the `p₀^{-2}` saving is not visible to residue-class counting. -/
theorem smoothCongruentOne_card_le_real (N p : ℕ) (hp : 2 ≤ p) :
    ((smoothCongruentOne N p).card : ℝ) ≤
      (N : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := by
  have hsum : (smoothCongruentOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), (N / (q * p ^ 2) + 1) :=
    smoothCongruentOne_card_le_sum N p hp
  have hterm : ∀ q ∈ Nat.primesLE (p - 1),
      ((N / (q * p ^ 2) + 1 : ℕ) : ℝ) ≤ (N : ℝ) / (q * (p : ℝ) ^ 2) + 1 := by
    intro q _
    push_cast
    have h : (((N / (q * p ^ 2)) : ℕ) : ℝ) ≤
        (N : ℝ) / (((q * p ^ 2) : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_pow] at h
    linarith [h]
  calc ((smoothCongruentOne N p).card : ℝ)
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
          have hpR : (0 : ℝ) < (p : ℝ) := by
            exact_mod_cast (by omega : 0 < p)
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

/-- **Headline elementary bound on `T₁`:**
`#{r ∈ [1,hi] : p²r + 1 p-smooth} ≤ ((p²hi+1)/p²)·(1 + log(p−1)) + p`. -/
theorem apSmoothParamCount_one_le_real (hi p : ℕ) (hp : 2 ≤ p) :
    (apSmoothParamCount 1 hi (p ^ 2) 1 p : ℝ) ≤
      ((p ^ 2 * hi + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := by
  rw [apSmoothParamCount_one_eq_smoothCongruentOne hi p hp]
  exact smoothCongruentOne_card_le_real _ _ hp

/-! ### Consequences for the run count -/

/-- The `k = 1` right-run count is bounded by the anti-sieve set:
`rightRunCount x p 1 ≤ |smoothCongruentOne (2x+1) p|`. -/
theorem rightRunCount_one_le_smoothCongruentOne {x p : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p 1 ≤ (smoothCongruentOne (2 * x + 1) p).card := by
  refine (rightRunCount_one_le_apSmoothParamCount hp).trans ?_
  rw [apSmoothParamCount_one_eq_smoothCongruentOne _ _ hp.two_le]
  apply Finset.card_le_card
  apply smoothCongruentOne_mono
  have h : p ^ 2 * (2 * x / p ^ 2) ≤ 2 * x := by
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  omega

/-- **Rankin recovery for the run count:**
`rightRunCount x p 1 ≤ Ψ(2x + 1, p − 1)`. -/
theorem rightRunCount_one_le_smoothCount {x p : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p 1 ≤ smoothCount (2 * x + 1) (p - 1) :=
  (rightRunCount_one_le_smoothCongruentOne hp).trans
    ((card_smoothCongruentOne_le_cofactorFinset _ _ hp.two_le).trans
      (cofactorFinset_card_le_smoothCount _ _ hp.two_le))

/-- The elementary real bound on the `k = 1` right-run count:
`rightRunCount x p 1 ≤ ((2x+1)/p²)·(1 + log(p−1)) + p`. -/
theorem rightRunCount_one_le_real {x p : ℕ} (hp : Nat.Prime p) :
    (rightRunCount x p 1 : ℝ) ≤
      ((2 * x + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := by
  have h1 : rightRunCount x p 1 ≤ (smoothCongruentOne (2 * x + 1) p).card :=
    rightRunCount_one_le_smoothCongruentOne hp
  have h2 := smoothCongruentOne_card_le_real (2 * x + 1) p hp.two_le
  calc (rightRunCount x p 1 : ℝ)
      ≤ ((smoothCongruentOne (2 * x + 1) p).card : ℝ) := Nat.cast_le.mpr h1
    _ ≤ ((2 * x + 1 : ℕ) : ℝ) / (p : ℝ) ^ 2 * (1 + Real.log (p - 1)) + p := h2

/-! ### Crude-moment machinery (new content)

The remaining sections formalize the **elementary** inputs of Tao's
anti-sieve (arXiv:2603.27990, Props 6.7(i)/6.8(i) shape) at the level of the
`T₁` problem:

* `coprime_of_mul_modEq`, `modEq_of_mul_modEq_of_coprime` — the cancellation
  lemmas for a general invertible residue class `c (mod K)` (the file's
  `coprime_of_mul_modEq_one`/`modEq_of_mul_modEq_one` are the `c = 1` case).
* `sum_Ioc_inv_le_log_sub_log`, `sum_primesLE_Ioc_inv_le` — the
  **prime-band moment** `∑_{a<q≤b} 1/q ≤ log b − log a`: the number of
  primes in `(z^{1−δ}, z^{1+δ}]` entering the anatomy, at logarithmic
  precision.
* `smoothCongruentOneLpfLe`, `smoothCongruentOneLpfBand` — the anatomy split
  of `T₁` by the largest prime factor: the `lpf ≤ a` part is bounded by
  `Ψ(N, a)` (Rankin territory), the `a < lpf ≤ b` band part by
  `(N/p²)·log(b/a) + b`.  Combined:
  `T₁ ≤ Ψ(N,a) + (N/p²)·log((p−1)/a) + p`.
* `primePairCongFinset`, `primePairCong₂Finset` — the **freeze-prime
  moments**: for an invertible class `a (mod p)` the number of prime pairs
  `(q₁,q₂) ∈ [1,P₁]×[1,P₂]` with `q₁q₂ ≡ a (mod p)` is at most
  `π(P₁)·(P₂/p + 1)` — a `1/p`-density bound (Prop 6.7(i) shape); and with
  *two* congruences modulo distinct primes the count is
  `π(P₁)·(P₂/(p·p') + 1)` — the `1/(pp')` correlation of Prop 6.8(i).
* `smoothCongruentOne_card_le_of_partner_bound` — the conditional
  `p₀^{-2}` theorem: the missing equidistribution input is isolated as an
  explicit hypothesis. -/

/-- If `a·b ≡ c (mod K)` with `gcd(c, K) = 1`, then each factor is coprime
to `K` (generalization of `coprime_of_mul_modEq_one`). -/
theorem coprime_of_mul_modEq {K a b c : ℕ} (hK : 0 < K)
    (h : a * b ≡ c [MOD K]) (hc : Nat.Coprime c K) :
    Nat.Coprime a K ∧ Nat.Coprime b K := by
  have hmod : (a * b) % K = c % K := h
  have hdvd : a * b - K * ((a * b) / K) = c % K := by
    have hdiv := Nat.div_add_mod (a * b) K
    omega
  have hg1 : Nat.gcd a K ∣ c % K := by
    have h1 : Nat.gcd a K ∣ a * b :=
      (Nat.gcd_dvd_left a K).trans (dvd_mul_right a b)
    have h2 : Nat.gcd a K ∣ K * ((a * b) / K) :=
      (Nat.gcd_dvd_right a K).trans (dvd_mul_right K _)
    have h3 := Nat.dvd_sub h1 h2
    rwa [hdvd] at h3
  have hg1c : Nat.gcd a K ∣ c := by
    have h5 : Nat.gcd a K ∣ K * (c / K) :=
      (Nat.gcd_dvd_right a K).trans (dvd_mul_right K _)
    have h6 : Nat.gcd a K ∣ c % K + K * (c / K) := hg1.add h5
    rwa [Nat.mod_add_div] at h6
  have hg2 : Nat.gcd b K ∣ c % K := by
    have h1 : Nat.gcd b K ∣ a * b :=
      (Nat.gcd_dvd_left b K).trans (dvd_mul_left b a)
    have h2 : Nat.gcd b K ∣ K * ((a * b) / K) :=
      (Nat.gcd_dvd_right b K).trans (dvd_mul_right K _)
    have h3 := Nat.dvd_sub h1 h2
    rwa [hdvd] at h3
  have hg2c : Nat.gcd b K ∣ c := by
    have h5 : Nat.gcd b K ∣ K * (c / K) :=
      (Nat.gcd_dvd_right b K).trans (dvd_mul_right K _)
    have h6 : Nat.gcd b K ∣ c % K + K * (c / K) := hg2.add h5
    rwa [Nat.mod_add_div] at h6
  constructor
  · have hd : Nat.gcd a K ∣ Nat.gcd c K :=
      Nat.dvd_gcd hg1c (Nat.gcd_dvd_right a K)
    rw [hc] at hd
    show Nat.gcd a K = 1
    exact Nat.dvd_one.mp hd
  · have hd : Nat.gcd b K ∣ Nat.gcd c K :=
      Nat.dvd_gcd hg2c (Nat.gcd_dvd_right b K)
    rw [hc] at hd
    show Nat.gcd b K = 1
    exact Nat.dvd_one.mp hd

/-- **Cancellation in a general invertible class**: if `q·m₁` and `q·m₂`
are both `≡ c (mod K)` with `gcd(c, K) = 1` then `m₁ ≡ m₂ (mod K)`
(generalization of `modEq_of_mul_modEq_one`). -/
theorem modEq_of_mul_modEq_of_coprime {K q c m₁ m₂ : ℕ} (hK : 0 < K)
    (h1 : q * m₁ ≡ c [MOD K]) (h2 : q * m₂ ≡ c [MOD K])
    (hc : Nat.Coprime c K) :
    m₁ ≡ m₂ [MOD K] := by
  have hcop : Nat.Coprime K q :=
    ((coprime_of_mul_modEq hK h1 hc).1).symm
  rcases le_total m₁ m₂ with h | h
  · have hmul : q * m₁ ≤ q * m₂ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₂ - q * m₁ :=
      (Nat.modEq_iff_dvd' hmul).mp (h1.trans h2.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact (Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)
  · have hmul : q * m₂ ≤ q * m₁ := Nat.mul_le_mul_left q h
    have hd : K ∣ q * m₁ - q * m₂ :=
      (Nat.modEq_iff_dvd' hmul).mp (h2.trans h1.symm)
    rw [← Nat.mul_sub_left_distrib] at hd
    exact ((Nat.modEq_iff_dvd' h).mpr (hcop.dvd_mul_left.mp hd)).symm

/-! ### The prime-band moment: `∑_{a<q≤b} 1/q ≤ log b − log a` -/

/-- **Harmonic bound on an interval**: `∑_{a<n≤b} 1/n ≤ log b − log a`
(for `1 ≤ a`).  Proved by telescoping `1/(n) ≤ log n − log (n−1)`. -/
theorem sum_Ioc_inv_le_log_sub_log {a b : ℕ} (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Icc (a + 1) b, (1 : ℝ) / n ≤ Real.log b - Real.log a := by
  rcases le_or_gt b a with hba | hab
  · rw [Finset.Icc_eq_empty_of_lt (by omega : b < a + 1), Finset.sum_empty]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      rw [Nat.cast_zero, Real.log_zero]
      have hlog : 0 ≤ Real.log (a : ℝ) :=
        Real.log_nonneg (by exact_mod_cast ha)
      linarith
    · have hle : Real.log (b : ℝ) ≤ Real.log (a : ℝ) :=
        Real.log_le_log (by exact_mod_cast hb) (by exact_mod_cast hba)
      linarith
  · have hcast : ∀ i : ℕ, ((a + 1 + i : ℕ) : ℝ) = (a : ℝ) + 1 + i := by
      intro i; push_cast; ring
    calc ∑ n ∈ Finset.Icc (a + 1) b, (1 : ℝ) / n
        = ∑ i ∈ Finset.range (b - a), (1 : ℝ) / ((a + 1 + i : ℕ) : ℝ) := by
          rw [show Finset.Icc (a + 1) b = Finset.Ico (a + 1) (b + 1) from rfl,
            Finset.sum_Ico_eq_sum_range,
            show b + 1 - (a + 1) = b - a by omega]
      _ ≤ ∑ i ∈ Finset.range (b - a),
            (Real.log ((a : ℝ) + 1 + i) - Real.log ((a : ℝ) + i)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [hcast i]
          have hstep := one_div_succ_le_log_sub_log
            (show 1 ≤ a + i by omega : 1 ≤ a + i)
          have hcast' : ((a + i : ℕ) : ℝ) = (a : ℝ) + i := by push_cast; ring
          rw [hcast'] at hstep
          rw [show (a : ℝ) + 1 + (i : ℝ) = (a : ℝ) + i + 1 by ring]
          exact hstep
      _ = Real.log ((a : ℝ) + (b - a : ℕ)) - Real.log (a : ℝ) := by
          have hstep : ∀ i : ℕ, i ∈ Finset.range (b - a) →
              Real.log ((a : ℝ) + 1 + i) - Real.log ((a : ℝ) + i)
                = Real.log ((a : ℝ) + ((i + 1 : ℕ) : ℝ))
                  - Real.log ((a : ℝ) + i) := by
            intro i _
            rw [show (a : ℝ) + 1 + (i : ℝ) = (a : ℝ) + ((i + 1 : ℕ) : ℝ) by
              push_cast; ring]
          rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub]
          simp
      _ = Real.log b - Real.log a := by
          rw [Nat.cast_sub (Nat.le_of_lt hab)]
          congr 1
          ring

/-- **Prime-band reciprocal moment** (Ta26c's `(z^{1−δ}, z^{1+δ}]` prime
supply, at logarithmic precision):
`∑_{a < q ≤ b, q prime} 1/q ≤ log b − log a`. -/
theorem sum_primesLE_Ioc_inv_le {a b : ℕ} (ha : 1 ≤ a) :
    ∑ q ∈ (Nat.primesLE b).filter fun q => a < q, (1 : ℝ) / q ≤
      Real.log b - Real.log a := by
  calc ∑ q ∈ (Nat.primesLE b).filter fun q => a < q, (1 : ℝ) / q
      ≤ ∑ n ∈ Finset.Icc (a + 1) b, (1 : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨hqb, hqa⟩ := Finset.mem_filter.mp hq
          have hq2 := (Nat.prime_of_mem_primesLE hqb).two_le
          have hqb' := Nat.le_of_mem_primesLE hqb
          exact Finset.mem_Icc.mpr ⟨by omega, hqb'⟩
        · intro i _ _
          positivity
    _ ≤ Real.log b - Real.log a := sum_Ioc_inv_le_log_sub_log ha

/-! ### Anatomy split of `T₁` by the largest prime factor -/

/-- Anti-sieve elements whose largest prime factor is `≤ a`: the part of
`T₁` supported on integers with **no** prime factor in `(a, p)`. -/
def smoothCongruentOneLpfLe (N p a : ℕ) : Finset ℕ :=
  (smoothCongruentOne N p).filter fun s => largestPrimeFactor s ≤ a

/-- Anti-sieve elements whose largest prime factor lies in `(a, b]`. -/
def smoothCongruentOneLpfBand (N p a b : ℕ) : Finset ℕ :=
  (smoothCongruentOne N p).filter fun s =>
    a < largestPrimeFactor s ∧ largestPrimeFactor s ≤ b

/-- The `lpf ≤ a` part of `T₁` is bounded by the `a`-smooth count
`Ψ(N, a)` — Rankin territory. -/
theorem smoothCongruentOneLpfLe_card_le (N p a : ℕ) :
    (smoothCongruentOneLpfLe N p a).card ≤ smoothCount N a := by
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hs, hlpa⟩ := Finset.mem_filter.mp hs
  obtain ⟨hs2, hsN, -, -⟩ := mem_smoothCongruentOne.mp hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hsN⟩, hlpa⟩

/-- Exact fiber decomposition of the band part: the band set is the
disjoint union, over primes `q ∈ (a, b]`, of the `largestPrimeFactor = q`
fibers of the anti-sieve set. -/
theorem smoothCongruentOneLpfBand_card_eq_sum (N p a b : ℕ) :
    (smoothCongruentOneLpfBand N p a b).card =
      ∑ q ∈ (Nat.primesLE b).filter fun q => a < q,
        ((smoothCongruentOne N p).filter
          fun s => largestPrimeFactor s = q).card := by
  classical
  have hU : smoothCongruentOneLpfBand N p a b =
      ((Nat.primesLE b).filter fun q => a < q).biUnion
        fun q => (smoothCongruentOne N p).filter
          fun s => largestPrimeFactor s = q := by
    ext s
    rw [Finset.mem_biUnion]
    constructor
    · intro hs
      obtain ⟨hsmem, ⟨hga, hgb⟩⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs2, -, -, -⟩ := mem_smoothCongruentOne.mp hsmem
      refine ⟨largestPrimeFactor s, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Nat.mem_primesLE.mpr ⟨hgb, largestPrimeFactor_prime hs2⟩, hga⟩
      · exact Finset.mem_filter.mpr ⟨hsmem, rfl⟩
    · rintro ⟨q, hq, hs⟩
      obtain ⟨hqb, hqa⟩ := Finset.mem_filter.mp hq
      obtain ⟨hsmem, hlp⟩ := Finset.mem_filter.mp hs
      subst hlp
      exact Finset.mem_filter.mpr
        ⟨hsmem, hqa, Nat.le_of_mem_primesLE hqb⟩
  have hdis : Set.PairwiseDisjoint
      (((Nat.primesLE b).filter fun q => a < q : Finset ℕ) : Set ℕ)
      (fun q => (smoothCongruentOne N p).filter
        fun s => largestPrimeFactor s = q) := by
    intro q₁ _ q₂ _ hne
    exact Finset.disjoint_left.mpr fun s hs₁ hs₂ =>
      hne ((Finset.mem_filter.mp hs₁).2.symm.trans
        (Finset.mem_filter.mp hs₂).2)
  conv_lhs => rw [hU]
  rw [Finset.card_biUnion hdis]

/-- **Band-part count bound**: the `(a, b]`-band contribution to `T₁` is at
most `∑_{a<q≤b, q prime} (N/(q·p²) + 1)`. -/
theorem smoothCongruentOneLpfBand_card_le_sum (N p a b : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOneLpfBand N p a b).card ≤
      ∑ q ∈ (Nat.primesLE b).filter fun q => a < q, (N / (q * p ^ 2) + 1) := by
  rw [smoothCongruentOneLpfBand_card_eq_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqprime : q.Prime :=
    Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1
  calc ((smoothCongruentOne N p).filter fun s => largestPrimeFactor s = q).card
      ≤ smoothPartnerCount (N / q) q (p ^ 2) q :=
        card_fiber_le_smoothPartner hp hqprime
    _ ≤ N / q / p ^ 2 + 1 :=
        smoothPartnerCount_le _ _ _ _ (Nat.pow_pos (show 0 < p by omega))
    _ = N / (q * p ^ 2) + 1 := by rw [Nat.div_div_eq_div_mul]

/-- **Real form of the band-part bound**:
`|smoothCongruentOneLpfBand N p a b| ≤ (N/p²)·(log b − log a) + b`. -/
theorem smoothCongruentOneLpfBand_card_le_real (N p a b : ℕ) (hp : 2 ≤ p)
    (ha : 1 ≤ a) :
    ((smoothCongruentOneLpfBand N p a b).card : ℝ) ≤
      (N : ℝ) / (p : ℝ) ^ 2 * (Real.log b - Real.log a) + b := by
  classical
  set S := (Nat.primesLE b).filter fun q => a < q
  have hsum : (smoothCongruentOneLpfBand N p a b).card ≤
      ∑ q ∈ S, (N / (q * p ^ 2) + 1) :=
    smoothCongruentOneLpfBand_card_le_sum N p a b hp
  have hterm : ∀ q ∈ S,
      ((N / (q * p ^ 2) + 1 : ℕ) : ℝ) ≤ (N : ℝ) / (q * (p : ℝ) ^ 2) + 1 := by
    intro q _
    push_cast
    have h : (((N / (q * p ^ 2)) : ℕ) : ℝ) ≤
        (N : ℝ) / (((q * p ^ 2) : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_pow] at h
    linarith [h]
  have hcardS : (S.card : ℝ) ≤ b := by
    have hsub : S ⊆ Finset.Icc (a + 1) b := by
      intro q hq
      obtain ⟨hqb, hqa⟩ := Finset.mem_filter.mp hq
      have hq2 := (Nat.prime_of_mem_primesLE hqb).two_le
      have hqb' := Nat.le_of_mem_primesLE hqb
      exact Finset.mem_Icc.mpr ⟨by omega, hqb'⟩
    have hcard : S.card ≤ (Finset.Icc (a + 1) b).card := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have : S.card ≤ b := by omega
    exact_mod_cast this
  calc ((smoothCongruentOneLpfBand N p a b).card : ℝ)
      ≤ ((∑ q ∈ S, (N / (q * p ^ 2) + 1)) : ℕ) := Nat.cast_le.mpr hsum
    _ = ∑ q ∈ S, (((N / (q * p ^ 2) + 1) : ℕ) : ℝ) := Nat.cast_sum _ _
    _ ≤ ∑ q ∈ S, ((N : ℝ) / (q * (p : ℝ) ^ 2) + 1) :=
        Finset.sum_le_sum hterm
    _ = (N : ℝ) / p ^ 2 * (∑ q ∈ S, (1 : ℝ) / q) + S.card := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          have hqR : (0 : ℝ) < (q : ℝ) := by
            have hqprime : q.Prime :=
              Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hq).1
            exact_mod_cast hqprime.pos
          rw [mul_comm (q : ℝ) ((p : ℝ) ^ 2), ← div_div, mul_one_div]
        · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (N : ℝ) / p ^ 2 * (Real.log b - Real.log a) + b := by
        apply add_le_add _ hcardS
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_primesLE_Ioc_inv_le ha

/-- **Anatomy split**: every anti-sieve element is either `a`-smooth through
its largest prime factor or has its largest prime factor in `(a, p − 1]`. -/
theorem smoothCongruentOne_card_eq_lpf_split (N p a : ℕ) (hp : 2 ≤ p) :
    (smoothCongruentOne N p).card =
      (smoothCongruentOneLpfLe N p a).card +
        (smoothCongruentOneLpfBand N p a (p - 1)).card := by
  classical
  have hU : smoothCongruentOne N p =
      smoothCongruentOneLpfLe N p a ∪ smoothCongruentOneLpfBand N p a (p - 1) := by
    ext s
    simp only [smoothCongruentOneLpfLe, smoothCongruentOneLpfBand,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hs
      rcases le_or_gt (largestPrimeFactor s) a with h | h
      · exact Or.inl ⟨hs, h⟩
      · refine Or.inr ⟨hs, h, ?_⟩
        have hlt := lpf_lt_of_mem_smoothCongruentOne hp hs
        omega
    · rintro (⟨hs, -⟩ | ⟨hs, -, -⟩) <;> exact hs
  have hdis : Disjoint (smoothCongruentOneLpfLe N p a)
      (smoothCongruentOneLpfBand N p a (p - 1)) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨-, h1⟩ := Finset.mem_filter.mp hs
    obtain ⟨-, ⟨h2, -⟩⟩ := Finset.mem_filter.mp hs'
    omega
  rw [hU, Finset.card_union_of_disjoint hdis]

/-- **Banded-anatomy bound on `T₁`** — the mid-band ingredient, splitting at
a free parameter `a ≥ 1`:
`|smoothCongruentOne N p| ≤ Ψ(N, a) + (N/p²)·log((p−1)/a) + p`.

The first term counts anti-sieve elements with **no** prime factor in
`(a, p)` — Rankin territory.  The second is the per-prime residue-class
bound summed over the band primes; injecting the equidistribution
hypothesis `smoothPartnerCount ≤ C·Ψ/p²` (see
`smoothCongruentOne_card_le_of_partner_bound`) in place of the class count
`N/(q p²)` is exactly the `p₀^{-2}`-saving step. -/
theorem smoothCongruentOne_card_le_lpf_split_real (N p a : ℕ) (hp : 2 ≤ p)
    (ha : 1 ≤ a) :
    ((smoothCongruentOne N p).card : ℝ) ≤
      smoothCount N a +
        (N : ℝ) / (p : ℝ) ^ 2 * (Real.log (p - 1) - Real.log a) + p := by
  have hsplit := smoothCongruentOne_card_eq_lpf_split N p a hp
  have h1 : ((smoothCongruentOneLpfLe N p a).card : ℝ) ≤ smoothCount N a :=
    Nat.cast_le.mpr (smoothCongruentOneLpfLe_card_le N p a)
  have h2 := smoothCongruentOneLpfBand_card_le_real N p a (p - 1) hp ha
  have hpm1 : ((p - 1 : ℕ) : ℝ) ≤ p := by
    have : (p - 1 : ℕ) ≤ p := Nat.sub_le _ _
    exact_mod_cast this
  calc ((smoothCongruentOne N p).card : ℝ)
      = ((smoothCongruentOneLpfLe N p a).card : ℝ) +
          ((smoothCongruentOneLpfBand N p a (p - 1)).card : ℝ) := by
        rw [← Nat.cast_add, hsplit]
    _ ≤ smoothCount N a +
          ((N : ℝ) / (p : ℝ) ^ 2 * (Real.log ((p - 1 : ℕ) : ℝ) - Real.log a)
            + (p - 1 : ℕ)) := add_le_add h1 h2
    _ ≤ smoothCount N a +
          ((N : ℝ) / (p : ℝ) ^ 2 * (Real.log ((p - 1 : ℕ) : ℝ) - Real.log a)
            + p) := by
        linarith [hpm1]
    _ = smoothCount N a +
          (N : ℝ) / (p : ℝ) ^ 2 * (Real.log (p - 1) - Real.log a) + p := by
        rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
        ring

/-! ### Freeze-prime moments: prime pairs in a congruence class -/

/-- **Congruent prime pairs** (the freeze-prime first moment): pairs of
primes `(q₁, q₂)` with `q₁ ≤ P₁`, `q₂ ≤ P₂` and `q₁·q₂ ≡ a (mod p)`. -/
def primePairCongFinset (P₁ P₂ p a : ℕ) : Finset (ℕ × ℕ) :=
  ((Nat.primesLE P₁) ×ˢ (Nat.primesLE P₂)).filter fun ⟨q₁, q₂⟩ =>
    q₁ * q₂ ≡ a [MOD p]

theorem mem_primePairCongFinset {P₁ P₂ p a q₁ q₂ : ℕ} :
    (q₁, q₂) ∈ primePairCongFinset P₁ P₂ p a ↔
      q₁ ∈ Nat.primesLE P₁ ∧ q₂ ∈ Nat.primesLE P₂ ∧ q₁ * q₂ ≡ a [MOD p] := by
  simp only [primePairCongFinset, Finset.mem_filter, Finset.mem_product]
  tauto

/-- **Fiber bound**: for each frozen `q₁`, the admissible `q₂`'s all lie in
a single residue class `mod p` — hence at most `P₂/p + 1` of them.  This is
the elementary core of Prop 6.7(i): freezing all but one prime coordinate
exposes the `1/p` density. -/
theorem primePairCong_fiber_card_le {P₁ P₂ p a q₁ : ℕ}
    (hp : 0 < p) (ha : Nat.Coprime a p) :
    ((primePairCongFinset P₁ P₂ p a).filter fun e => e.1 = q₁).card ≤
      P₂ / p + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((primePairCongFinset P₁ P₂ p a).filter fun e => e.1 = q₁) with
    hempty | hne
  · simp [hempty]
  obtain ⟨⟨q₁', m₀⟩, he₀⟩ := hne
  obtain ⟨hmem₀, hfst⟩ := Finset.mem_filter.mp he₀
  obtain ⟨hprod₀, hcong₀⟩ := Finset.mem_filter.mp hmem₀
  obtain ⟨hq₁₀, hm₀⟩ := Finset.mem_product.mp hprod₀
  simp only at hfst
  subst hfst
  refine (Finset.card_le_card_of_injOn Prod.snd ?_ ?_).trans
    (card_residue_class_le P₂ p m₀)
  · intro e he
    rw [Finset.mem_coe] at he ⊢
    obtain ⟨hmeme, hfe⟩ := Finset.mem_filter.mp he
    obtain ⟨hprode, hconge⟩ := Finset.mem_filter.mp hmeme
    obtain ⟨hq₁e, hq₂e⟩ := Finset.mem_product.mp hprode
    have hq₂prime := Nat.prime_of_mem_primesLE hq₂e
    have hconge' : e.1 * e.2 ≡ a [MOD p] := hconge
    have hconge'' : q₁' * e.2 ≡ a [MOD p] := hfe ▸ hconge'
    have hcong : e.2 ≡ m₀ [MOD p] :=
      modEq_of_mul_modEq_of_coprime hp hconge'' hcong₀ ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hcong⟩
    · exact hq₂prime.one_le
    · exact Nat.le_of_mem_primesLE hq₂e
  · intro e₁ he₁ e₂ he₂ h
    obtain ⟨-, hf₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he₁)
    obtain ⟨-, hf₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he₂)
    obtain ⟨a₁, b₁⟩ := e₁
    obtain ⟨a₂, b₂⟩ := e₂
    simp only at hf₁ hf₂ h
    simp only [Prod.mk.injEq]
    exact ⟨hf₁.trans hf₂.symm, h⟩

/-- **Crude first moment** (Ta26c Prop 6.7(i) shape): for `a` coprime to
`p`, the number of prime pairs `(q₁, q₂) ∈ [1, P₁]×[1, P₂]` with
`q₁q₂ ≡ a (mod p)` is at most `π(P₁)·(P₂/p + 1)`.  Relative to the full
box this is a `≪ 1/p` density once `p ≲ P₂`. -/
theorem primePairCongFinset_card_le {P₁ P₂ p a : ℕ}
    (hp : 0 < p) (ha : Nat.Coprime a p) :
    (primePairCongFinset P₁ P₂ p a).card ≤
      (Nat.primesLE P₁).card * (P₂ / p + 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Nat.primesLE P₁)
    (s := primePairCongFinset P₁ P₂ p a)]
  · calc ∑ b ∈ Nat.primesLE P₁,
          #{a ∈ primePairCongFinset P₁ P₂ p a | a.1 = b}
        ≤ ∑ _b ∈ Nat.primesLE P₁, (P₂ / p + 1) :=
          Finset.sum_le_sum fun q₁ _ => primePairCong_fiber_card_le hp ha
      _ = (Nat.primesLE P₁).card * (P₂ / p + 1) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
  · intro e he
    obtain ⟨hprod, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact (Finset.mem_product.mp hprod).1

/-- **Real form of the crude first moment**:
`|primePairCongFinset| ≤ (P₁+1)·(P₂/p + 1)` in `ℝ`. -/
theorem primePairCongFinset_card_le_real {P₁ P₂ p a : ℕ}
    (hp : 0 < p) (ha : Nat.Coprime a p) :
    ((primePairCongFinset P₁ P₂ p a).card : ℝ) ≤
      ((P₁ : ℝ) + 1) * ((P₂ : ℝ) / p + 1) := by
  have h := primePairCongFinset_card_le hp ha (P₁ := P₁) (P₂ := P₂)
  have hcard : (Nat.primesLE P₁).card ≤ P₁ + 1 := card_primesLE_le P₁
  have hcast : ((primePairCongFinset P₁ P₂ p a).card : ℝ) ≤
      (((Nat.primesLE P₁).card * (P₂ / p + 1) : ℕ) : ℝ) := Nat.cast_le.mpr h
  rw [Nat.cast_mul] at hcast
  have h1 : (((Nat.primesLE P₁).card : ℕ) : ℝ) ≤ (P₁ : ℝ) + 1 := by
    have : ((Nat.primesLE P₁).card : ℝ) ≤ ((P₁ + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcard
    rwa [Nat.cast_add, Nat.cast_one] at this
  have h2 : (((P₂ / p + 1 : ℕ) : ℝ)) ≤ (P₂ : ℝ) / p + 1 := by
    push_cast
    have : (((P₂ / p : ℕ) : ℝ)) ≤ (P₂ : ℝ) / p := Nat.cast_div_le
    linarith [this]
  calc ((primePairCongFinset P₁ P₂ p a).card : ℝ)
      ≤ ((Nat.primesLE P₁).card : ℝ) * ((P₂ / p + 1 : ℕ) : ℝ) := hcast
    _ ≤ ((P₁ : ℝ) + 1) * ((P₂ : ℝ) / p + 1) := by
        apply mul_le_mul h1 h2 (by positivity) (by positivity)

/-- **Congruent prime pairs, double congruence** (the freeze-prime second
moment): `(q₁, q₂)` prime with `q₁ ≤ P₁`, `q₂ ≤ P₂`,
`q₁q₂ ≡ a (mod p)` and `q₁q₂ ≡ a' (mod p')`. -/
def primePairCong₂Finset (P₁ P₂ p p' a a' : ℕ) : Finset (ℕ × ℕ) :=
  ((Nat.primesLE P₁) ×ˢ (Nat.primesLE P₂)).filter fun ⟨q₁, q₂⟩ =>
    q₁ * q₂ ≡ a [MOD p] ∧ q₁ * q₂ ≡ a' [MOD p']

/-- **Fiber bound, double congruence**: for each frozen `q₁`, the
admissible `q₂`'s lie in a single class `mod p·p'` (by CRT), hence at most
`P₂/(p·p') + 1` of them — the elementary core of Prop 6.8(i). -/
theorem primePairCong₂_fiber_card_le {P₁ P₂ p p' a a' q₁ : ℕ}
    (hp : 0 < p) (hp' : 0 < p') (hpp : Nat.Coprime p p')
    (ha : Nat.Coprime a p) (ha' : Nat.Coprime a' p') :
    ((primePairCong₂Finset P₁ P₂ p p' a a').filter fun e => e.1 = q₁).card ≤
      P₂ / (p * p') + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((primePairCong₂Finset P₁ P₂ p p' a a').filter fun e => e.1 = q₁) with
    hempty | hne
  · simp [hempty]
  obtain ⟨⟨q₁', m₀⟩, he₀⟩ := hne
  obtain ⟨hmem₀, hfst⟩ := Finset.mem_filter.mp he₀
  obtain ⟨hprod₀, hcong₀⟩ := Finset.mem_filter.mp hmem₀
  obtain ⟨hq₁₀, hm₀⟩ := Finset.mem_product.mp hprod₀
  simp only at hfst
  subst hfst
  refine (Finset.card_le_card_of_injOn Prod.snd ?_ ?_).trans
    (card_residue_class_le P₂ (p * p') m₀)
  · intro e he
    rw [Finset.mem_coe] at he ⊢
    obtain ⟨hmeme, hfe⟩ := Finset.mem_filter.mp he
    obtain ⟨hprode, hconge⟩ := Finset.mem_filter.mp hmeme
    obtain ⟨hq₁e, hq₂e⟩ := Finset.mem_product.mp hprode
    have hq₂prime := Nat.prime_of_mem_primesLE hq₂e
    have hcong₁ : q₁' * e.2 ≡ a [MOD p] := hfe ▸ hconge.1
    have hcong₂ : q₁' * e.2 ≡ a' [MOD p'] := hfe ▸ hconge.2
    have hmod₁ : e.2 ≡ m₀ [MOD p] :=
      modEq_of_mul_modEq_of_coprime hp hcong₁ hcong₀.1 ha
    have hmod₂ : e.2 ≡ m₀ [MOD p'] :=
      modEq_of_mul_modEq_of_coprime hp' hcong₂ hcong₀.2 ha'
    have hmod : e.2 ≡ m₀ [MOD p * p'] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hpp).mp ⟨hmod₁, hmod₂⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hmod⟩
    · exact hq₂prime.one_le
    · exact Nat.le_of_mem_primesLE hq₂e
  · intro e₁ he₁ e₂ he₂ h
    obtain ⟨-, hf₁⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he₁)
    obtain ⟨-, hf₂⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he₂)
    obtain ⟨a₁, b₁⟩ := e₁
    obtain ⟨a₂, b₂⟩ := e₂
    simp only at hf₁ hf₂ h
    simp only [Prod.mk.injEq]
    exact ⟨hf₁.trans hf₂.symm, h⟩

/-- **Crude second moment** (Ta26c Prop 6.8(i) shape): for `a` coprime to
`p` and `a'` coprime to `p'`, with `p, p'` coprime, the number of prime
pairs with `q₁q₂ ≡ a (mod p)` and `q₁q₂ ≡ a' (mod p')` is at most
`π(P₁)·(P₂/(p·p') + 1)` — a `≪ 1/(p·p')` correlation bound. -/
theorem primePairCong₂Finset_card_le {P₁ P₂ p p' a a' : ℕ}
    (hp : 0 < p) (hp' : 0 < p') (hpp : Nat.Coprime p p')
    (ha : Nat.Coprime a p) (ha' : Nat.Coprime a' p') :
    (primePairCong₂Finset P₁ P₂ p p' a a').card ≤
      (Nat.primesLE P₁).card * (P₂ / (p * p') + 1) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Nat.primesLE P₁)
    (s := primePairCong₂Finset P₁ P₂ p p' a a')]
  · calc ∑ b ∈ Nat.primesLE P₁,
          #{a ∈ primePairCong₂Finset P₁ P₂ p p' a a' | a.1 = b}
        ≤ ∑ _b ∈ Nat.primesLE P₁, (P₂ / (p * p') + 1) :=
          Finset.sum_le_sum fun q₁ _ =>
            primePairCong₂_fiber_card_le hp hp' hpp ha ha'
      _ = (Nat.primesLE P₁).card * (P₂ / (p * p') + 1) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
  · intro e he
    obtain ⟨hprod, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact (Finset.mem_product.mp hprod).1

/-- **Real form of the crude second moment.** -/
theorem primePairCong₂Finset_card_le_real {P₁ P₂ p p' a a' : ℕ}
    (hp : 0 < p) (hp' : 0 < p') (hpp : Nat.Coprime p p')
    (ha : Nat.Coprime a p) (ha' : Nat.Coprime a' p') :
    ((primePairCong₂Finset P₁ P₂ p p' a a').card : ℝ) ≤
      ((P₁ : ℝ) + 1) * ((P₂ : ℝ) / (p * p') + 1) := by
  have h := primePairCong₂Finset_card_le hp hp' hpp ha ha'
    (P₁ := P₁) (P₂ := P₂)
  have hcard : (Nat.primesLE P₁).card ≤ P₁ + 1 := card_primesLE_le P₁
  have hcast : ((primePairCong₂Finset P₁ P₂ p p' a a').card : ℝ) ≤
      (((Nat.primesLE P₁).card * (P₂ / (p * p') + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr h
  rw [Nat.cast_mul] at hcast
  have h1 : (((Nat.primesLE P₁).card : ℕ) : ℝ) ≤ (P₁ : ℝ) + 1 := by
    have : ((Nat.primesLE P₁).card : ℝ) ≤ ((P₁ + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcard
    rwa [Nat.cast_add, Nat.cast_one] at this
  have h2 : (((P₂ / (p * p') + 1 : ℕ) : ℝ)) ≤ (P₂ : ℝ) / (p * p') + 1 := by
    push_cast
    have hd : (((P₂ / (p * p') : ℕ) : ℝ)) ≤
        (P₂ : ℝ) / (((p * p') : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_mul] at hd
    linarith [hd]
  calc ((primePairCong₂Finset P₁ P₂ p p' a a').card : ℝ)
      ≤ ((Nat.primesLE P₁).card : ℝ) * ((P₂ / (p * p') + 1 : ℕ) : ℝ) := hcast
    _ ≤ ((P₁ : ℝ) + 1) * ((P₂ : ℝ) / (p * p') + 1) := by
        apply mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ### The conditional `p₀^{-2}` bound -/

/-- **Conditional `p₀^{-2}` bound** (the missing input isolated as an
explicit hypothesis).

*Hypothesis* (`heq`): for every cofactor prime `q < p`, the `q`-smooth
integers `m ≤ N/q` lying in the inverse class `q⁻¹ (mod p²)` number at
most `C` times their expected share `Ψ(N/q, q)/p²`.  This is precisely
the smooth-numbers-in-AP equidistribution input of Ta26c Props 6.6–6.8
(level `p²` larger than the smoothness bound `q`), which has no known
elementary proof.

*Conclusion*: `T₁ = |smoothCongruentOne N p| ≤ (C/p²)·Σ_{q prime<p} Ψ(N/q, q)`.
Everything else in the reduction — the cofactor anatomy, fiber uniqueness
and the per-prime decomposition — is proved unconditionally above. -/
theorem smoothCongruentOne_card_le_of_partner_bound (N p : ℕ) (hp : 2 ≤ p)
    (C : ℝ)
    (heq : ∀ q ∈ Nat.primesLE (p - 1),
      (smoothPartnerCount (N / q) q (p ^ 2) q : ℝ) ≤
        C * (smoothCount (N / q) q : ℝ) / (p : ℝ) ^ 2) :
    ((smoothCongruentOne N p).card : ℝ) ≤
      C / (p : ℝ) ^ 2 *
        ∑ q ∈ Nat.primesLE (p - 1), (smoothCount (N / q) q : ℝ) := by
  have hsum : (smoothCongruentOne N p).card ≤
      ∑ q ∈ Nat.primesLE (p - 1), smoothPartnerCount (N / q) q (p ^ 2) q :=
    smoothCongruentOne_card_le_sum_partner N p hp
  calc ((smoothCongruentOne N p).card : ℝ)
      ≤ ((∑ q ∈ Nat.primesLE (p - 1),
          smoothPartnerCount (N / q) q (p ^ 2) q) : ℕ) := Nat.cast_le.mpr hsum
    _ = ∑ q ∈ Nat.primesLE (p - 1),
          ((smoothPartnerCount (N / q) q (p ^ 2) q : ℕ) : ℝ) :=
        Nat.cast_sum _ _
    _ ≤ ∑ q ∈ Nat.primesLE (p - 1),
          C * (smoothCount (N / q) q : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum fun q hq => heq q hq
    _ = C / (p : ℝ) ^ 2 *
          ∑ q ∈ Nat.primesLE (p - 1), (smoothCount (N / q) q : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [div_mul_eq_mul_div]

/-- Monotonicity of `smoothCount` in the smoothness bound. -/
theorem smoothCount_mono_y {N y₁ y₂ : ℕ} (h : y₁ ≤ y₂) :
    smoothCount N y₁ ≤ smoothCount N y₂ := by
  apply Finset.card_le_card
  intro s hs
  simp only [smoothFinset, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, hs.2.trans h⟩

/-- A crude consequence of the conditional bound: since
`Ψ(N/q, q) ≤ Ψ(N, p−1)` and there are `≤ p` cofactor primes, the
hypothesis yields `T₁ ≤ C·Ψ(N, p−1)/p` — already a `1/p` saving over the
Rankin recovery bound `T₁ ≤ Ψ(N, p−1)`. -/
theorem smoothCongruentOne_card_le_of_partner_bound_crude (N p : ℕ)
    (hp : 2 ≤ p) (C : ℝ) (hC : 0 ≤ C)
    (heq : ∀ q ∈ Nat.primesLE (p - 1),
      (smoothPartnerCount (N / q) q (p ^ 2) q : ℝ) ≤
        C * (smoothCount (N / q) q : ℝ) / (p : ℝ) ^ 2) :
    ((smoothCongruentOne N p).card : ℝ) ≤
      C * smoothCount N (p - 1) / p := by
  have hmain := smoothCongruentOne_card_le_of_partner_bound N p hp C heq
  have hterm : ∀ q ∈ Nat.primesLE (p - 1),
      (smoothCount (N / q) q : ℝ) ≤ smoothCount N (p - 1) := by
    intro q hq
    have hqle : q ≤ p - 1 := (Nat.mem_primesLE.mp hq).1
    have h1 : smoothCount (N / q) q ≤ smoothCount N q :=
      smoothCount_mono (Nat.div_le_self _ _)
    have h2 : smoothCount N q ≤ smoothCount N (p - 1) :=
      smoothCount_mono_y hqle
    exact_mod_cast h1.trans h2
  have hsumle : ∑ q ∈ Nat.primesLE (p - 1), (smoothCount (N / q) q : ℝ) ≤
      (Nat.primesLE (p - 1)).card * smoothCount N (p - 1) := by
    calc ∑ q ∈ Nat.primesLE (p - 1), (smoothCount (N / q) q : ℝ)
        ≤ ∑ q ∈ Nat.primesLE (p - 1), (smoothCount N (p - 1) : ℝ) :=
          Finset.sum_le_sum hterm
      _ = (Nat.primesLE (p - 1)).card * smoothCount N (p - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Nat.primesLE (p - 1)).card : ℝ) ≤ p := by
    have h' : (Nat.primesLE (p - 1)).card ≤ p := by
      have h := card_primesLE_le (p - 1)
      omega
    exact_mod_cast h'
  have hNN : (0 : ℝ) ≤ smoothCount N (p - 1) := Nat.cast_nonneg _
  calc ((smoothCongruentOne N p).card : ℝ)
      ≤ C / (p : ℝ) ^ 2 *
          ∑ q ∈ Nat.primesLE (p - 1), (smoothCount (N / q) q : ℝ) := hmain
    _ ≤ C / (p : ℝ) ^ 2 *
          ((Nat.primesLE (p - 1)).card * smoothCount N (p - 1)) := by
        apply mul_le_mul_of_nonneg_left hsumle
        apply div_nonneg hC (by positivity)
    _ ≤ C / (p : ℝ) ^ 2 * (p * smoothCount N (p - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by apply div_nonneg hC (by positivity))
        exact mul_le_mul_of_nonneg_right hcard hNN
    _ = C * smoothCount N (p - 1) / p := by
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [eq_div_iff hpR, div_mul_eq_mul_div, div_mul_eq_mul_div,
          div_eq_iff (pow_ne_zero 2 hpR), pow_two]
        ring

end JSP314
