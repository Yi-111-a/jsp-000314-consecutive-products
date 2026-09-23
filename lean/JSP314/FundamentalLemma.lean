import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# JSP-000314 — the fundamental lemma of sieve theory (Brun's pure sieve)

A usable form of Tao's Lemma 5.4 (arXiv:2603.27990): the existence of
*upper-bound sieve weights* `λ_d ∈ {-1, 0, 1}` with `λ_1 = 1`, supported on
`squarefree d ∣ P`, such that `ν n = ∑_{d ∣ n} λ_d` is nonnegative and equals
`1` whenever `n` is coprime to `P`.

We implement **Brun's pure sieve**: for a squarefree `P` (e.g. a primorial
`z#`) and a truncation parameter `t`, take `λ_d = μ d` for `d ∣ P` with
`ω(d) ≤ 2t` and `λ_d = 0` otherwise.  Then for `ω = ω(gcd n P)`,

  `ν n = ∑_{j = 0}^{2t} (-1)^j C(ω, j) = C(ω - 1, 2t)`   (for `ω ≥ 1`)

by the truncated alternating binomial identity, hence `ν n ≥ 0` and
`ν n = 1` iff `gcd n P = 1`.

## Main definitions

* `brunLambda P t d` : the sieve weight, `μ d` for `d ∣ P` with
  `d.primeFactors.card ≤ 2t`, `0` otherwise.
* `brunNu P t n` : the sieve value `ν n = ∑_{d ∣ n} λ_d`.

## Main results

* `brunNu_eq_sum_powerset`, `brunNu_eq_alternating`, `brunNu_eq_choose`:
  evaluation of `ν n`.
* `brunNu_nonneg`, `brunNu_eq_one_of_coprime`, `brunNu_ge_indicator`:
  `ν` is a nonnegative upper-bound sieve for `n` coprime to `P`.
* `brun_isUpperMoebius`: compatibility with Mathlib's `BoundingSieve`
  (`IsUpperMoebius`) sieve framework.
* `brun_sum_moebius_div`, `brun_sum_lambda_div`,
  `brun_sum_lambda_div_eq_prod_sub_tail`, `brun_abs_sum_lambda_div_sub_prod_le`:
  the main-term computation `∑_{d ∣ P} λ_d / d = ∏_{q ∣ P} (1 - q⁻¹) - tail`
  with `|tail| ≤ ∑_{s ⊆ primeFactors P, #s > 2t} ∏_{q ∈ s} q⁻¹`.
* `brun_tail_le`, `brun_tail_le_exp`: Rankin-type bounds
  `y^{2t} · tail ≤ ∏_{q ∈ S} (1 + y/q) ≤ exp(y · ∑_{q ∈ S} q⁻¹)` for `y ≥ 1`,
  which give `tail ≤ (e σ / 2t)^{2t}`-type control with `σ = ∑_{q ∈ S} q⁻¹`.

No `sorry`; kernel-checkable.
-/

namespace JSP314

open Finset Nat
open scoped ArithmeticFunction.Moebius

/-- **Brun's pure-sieve weights.**  `λ_d = μ d` for `d ∣ P` with at most `2t`
distinct prime factors, and `λ_d = 0` otherwise. -/
def brunLambda (P t d : ℕ) : ℤ :=
  if d ∣ P ∧ d.primeFactors.card ≤ 2 * t then μ d else 0

/-- The sifted majorant `ν n = ∑_{d ∣ n} λ_d`. -/
def brunNu (P t n : ℕ) : ℤ := ∑ d ∈ n.divisors, brunLambda P t d

/-- `λ_1 = 1`. -/
@[simp] theorem brunLambda_one (P t : ℕ) : brunLambda P t 1 = 1 := by
  simp [brunLambda, ArithmeticFunction.moebius_apply_one]

/-- The weights take values in `{-1, 0, 1}`. -/
theorem brunLambda_eq_or (P t d : ℕ) :
    brunLambda P t d = 0 ∨ brunLambda P t d = 1 ∨ brunLambda P t d = -1 := by
  unfold brunLambda
  split_ifs
  · exact ArithmeticFunction.moebius_eq_or d
  · exact Or.inl rfl

theorem abs_brunLambda_le_one (P t d : ℕ) : |brunLambda P t d| ≤ 1 := by
  unfold brunLambda
  split_ifs
  · exact ArithmeticFunction.abs_moebius_le_one
  · simp

theorem brunLambda_of_not_dvd {P t d : ℕ} (h : ¬ d ∣ P) : brunLambda P t d = 0 :=
  if_neg fun hd => h hd.1

theorem brunLambda_of_dvd {P t d : ℕ} (hd : d ∣ P)
    (hω : d.primeFactors.card ≤ 2 * t) : brunLambda P t d = μ d :=
  if_pos ⟨hd, hω⟩

/-- The weights are supported on `d ∣ P`. -/
theorem brunLambda_dvd_of_ne_zero {P t d : ℕ} (h : brunLambda P t d ≠ 0) :
    d ∣ P := by
  by_contra hd
  exact h (brunLambda_of_not_dvd hd)

/-- Hence `λ` is supported on `d ≤ P` (for `P ≠ 0`). -/
theorem brunLambda_le_of_ne_zero {P t d : ℕ} (hP : 0 < P)
    (h : brunLambda P t d ≠ 0) : d ≤ P :=
  Nat.le_of_dvd hP (brunLambda_dvd_of_ne_zero h)

/-- Nonzero weights are supported on squarefree integers. -/
theorem brunLambda_squarefree_of_ne_zero {P t d : ℕ} (h : brunLambda P t d ≠ 0) :
    Squarefree d := by
  unfold brunLambda at h
  by_cases hc : d ∣ P ∧ d.primeFactors.card ≤ 2 * t
  · rw [if_pos hc] at h
    exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
  · rw [if_neg hc] at h
    exact absurd rfl h

/-- For `d ≤ P`… the support of `λ` on `P = z#` lies in `d ≤ 4^z`. -/
theorem brunLambda_primorial_le_of_ne_zero {t z d : ℕ}
    (h : brunLambda (primorial z) t d ≠ 0) : d ≤ 4 ^ z :=
  (Nat.le_of_dvd (primorial_pos z) (brunLambda_dvd_of_ne_zero h)).trans
    (primorial_le_four_pow z)

/-- Möbius of a product of distinct primes `s ⊆ P.primeFactors` is `(-1)^#s`. -/
theorem moebius_prod_primeFactors {P : ℕ} {s : Finset ℕ} (hs : s ⊆ P.primeFactors) :
    μ (∏ q ∈ s, q) = (-1 : ℤ) ^ s.card := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_subset_primeFactors
    P s hs]
  exact Finset.prod_eq_pow_card fun q hq =>
    ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors (hs hq))

/-- **Evaluation of `ν` over the powerset of `primeFactors (gcd n P)`.**  For
`n ≠ 0`, `ν n` equals the truncated alternating sum over subsets of the prime
factors of `gcd n P` of size `≤ 2t`. -/
theorem brunNu_eq_sum_powerset {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0) :
    brunNu P t n = ∑ s ∈ (n.gcd P).primeFactors.powerset with s.card ≤ 2 * t,
      (-1 : ℤ) ^ s.card := by
  have hP0 : P ≠ 0 := hP.ne_zero
  set g := n.gcd P with hg_def
  have hg0 : g ≠ 0 := gcd_ne_zero_right hP0
  have hgsq : Squarefree g := Squarefree.squarefree_of_dvd (gcd_dvd_right n P) hP
  have hset : (n.divisors.filter fun d => d ∣ P ∧ d.primeFactors.card ≤ 2 * t)
      = g.divisors.filter fun d => d.primeFactors.card ≤ 2 * t := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, hdP, hω⟩
      exact ⟨⟨Nat.dvd_gcd hdn hdP, hg0⟩, hω⟩
    · rintro ⟨⟨hdg, -⟩, hω⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_left n P), hn⟩,
        hdg.trans (Nat.gcd_dvd_right n P), hω⟩
  have hunfold : brunNu P t n
      = ∑ d ∈ n.divisors, (if d ∣ P ∧ d.primeFactors.card ≤ 2 * t
          then (μ d : ℤ) else 0) := rfl
  rw [hunfold, ← Finset.sum_filter, hset]
  refine Finset.sum_nbij' (i := fun d => d.primeFactors)
    (j := fun s => ∏ q ∈ s, q) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Nat.primeFactors_mono (Nat.mem_divisors.mp hd.1).1 hg0), hd.2⟩
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    obtain ⟨hs_sub, hcard⟩ := hs
    have hdvd : ∏ q ∈ s, q ∣ g := by
      rw [← Nat.prod_primeFactors_of_squarefree hgsq]
      exact Finset.prod_dvd_prod_of_subset s g.primeFactors _ hs_sub
    have hpfs : (∏ q ∈ s, q).primeFactors = s :=
      Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (hs_sub hq)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, hg0⟩, by rw [hpfs]; exact hcard⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd.1).1 hgsq)
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    exact Nat.primeFactors_prod fun q hq =>
      Nat.prime_of_mem_primeFactors (hs.1 hq)
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hdsq : Squarefree d :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd.1).1 hgsq
    have hμ : (μ d : ℤ) = (-1) ^ d.primeFactors.card := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
      exact moebius_prod_primeFactors (P := d) Finset.subset_rfl
    exact hμ

/-- **Closed form of `ν`**: with `ω = #(primeFactors (gcd n P))`,
`ν n = ∑_{j < 2t+1} (-1)^j · C(ω, j)`. -/
theorem brunNu_eq_alternating {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0) :
    brunNu P t n = ∑ j ∈ Finset.range (2 * t + 1),
      (-1 : ℤ) ^ j * ((n.gcd P).primeFactors.card.choose j : ℤ) := by
  rw [brunNu_eq_sum_powerset hP hn]
  set ω := (n.gcd P).primeFactors.card with hω
  have key := Finset.sum_powerset_apply_card
    (f := fun j => if j ≤ 2 * t then (-1 : ℤ) ^ j else 0)
    (x := (n.gcd P).primeFactors)
  calc ∑ s ∈ (n.gcd P).primeFactors.powerset with s.card ≤ 2 * t,
          (-1 : ℤ) ^ s.card
      = ∑ s ∈ (n.gcd P).primeFactors.powerset,
          (if s.card ≤ 2 * t then (-1 : ℤ) ^ s.card else 0) :=
        (Finset.sum_filter _ _ _).symm
    _ = ∑ j ∈ Finset.range (ω + 1),
          (ω.choose j : ℤ) • (if j ≤ 2 * t then (-1 : ℤ) ^ j else 0) := key
    _ = ∑ j ∈ Finset.range (2 * t + 1),
          (-1 : ℤ) ^ j * (ω.choose j : ℤ) := by
        have hterm : ∀ j, (ω.choose j : ℤ) •
              (if j ≤ 2 * t then (-1 : ℤ) ^ j else 0)
            = if j ≤ 2 * t then (-1 : ℤ) ^ j * (ω.choose j : ℤ) else 0 := by
          intro j
          by_cases hj : j ≤ 2 * t
          · simp only [hj, if_true, nsmul_eq_mul]
            rw [mul_comm]
          · simp only [hj, if_false, smul_zero]
        rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_filter]
        have hflt : (Finset.range (ω + 1)).filter (fun j => j ≤ 2 * t)
            = Finset.range (min ω (2 * t) + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hflt]
        apply Finset.sum_subset
        · intro j hj
          rw [Finset.mem_range] at hj ⊢
          omega
        · intro j hj1 hj2
          rw [Finset.mem_range] at hj1 hj2
          have hlt : ω < j := by omega
          simp [Nat.choose_eq_zero_of_lt hlt]

/-- **The Bonferroni/Beta-sieve closed form**: for `ω = ω(gcd n P)`,
`ν n = C(ω - 1, 2t)` if `ω ≥ 1` and `ν n = 1` if `ω = 0`.  In particular
`ν n ≥ 0` and `ν n = 1` when `n` is coprime to `P`. -/
theorem brunNu_eq_choose {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0) :
    brunNu P t n = if (n.gcd P).primeFactors.card = 0 then 1
      else (((n.gcd P).primeFactors.card - 1).choose (2 * t) : ℤ) := by
  rw [brunNu_eq_alternating hP hn]
  by_cases hω : (n.gcd P).primeFactors.card = 0
  · rw [if_pos hω]
    rw [Finset.sum_eq_single 0]
    · simp [hω]
    · intro j _ hj
      rw [hω, Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
      simp
    · intro h
      exact absurd h (by simp)
  · rw [if_neg hω]
    have hω1 : (n.gcd P).primeFactors.card - 1 + 1
        = (n.gcd P).primeFactors.card := by omega
    have hkey := Int.alternating_sum_range_choose_eq_choose
      (n := (n.gcd P).primeFactors.card - 1) (m := 2 * t)
    rw [hω1] at hkey
    rw [hkey, Even.neg_one_pow ⟨t, two_mul t⟩, one_mul]

/-- `ν n ≥ 0` — the weights form an *upper bound* sieve. -/
theorem brunNu_nonneg {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0) :
    0 ≤ brunNu P t n := by
  rw [brunNu_eq_choose hP hn]
  split_ifs
  · exact zero_le_one
  · exact Nat.cast_nonneg _

/-- `ν n = 1` when `n` is coprime to `P`: the sieve majorizes the
coprimality indicator exactly. -/
theorem brunNu_eq_one_of_coprime {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0)
    (hc : n.Coprime P) : brunNu P t n = 1 := by
  rw [brunNu_eq_choose hP hn]
  have hgc : n.gcd P = 1 := hc
  have hcard : (n.gcd P).primeFactors.card = 0 := by rw [hgc]; simp
  rw [if_pos hcard]

/-- `ν` dominates the indicator of `n` coprime to `P`: the defining property
of an upper-bound sieve. -/
theorem brunNu_ge_indicator {P t n : ℕ} (hP : Squarefree P) (hn : n ≠ 0) :
    (if n.Coprime P then (1 : ℤ) else 0) ≤ brunNu P t n := by
  by_cases hc : n.Coprime P
  · rw [if_pos hc, brunNu_eq_one_of_coprime hP hn hc]
  · rw [if_neg hc]
    exact brunNu_nonneg hP hn

/-- `ν q = 1` for primes `q ∤ P`: the sieve is *exact* on large primes. -/
theorem brunNu_eq_one_of_prime_not_dvd {P t q : ℕ} (hP : Squarefree P)
    (hq : q.Prime) (hd : ¬ q ∣ P) : brunNu P t q = 1 :=
  brunNu_eq_one_of_coprime hP hq.ne_zero (hq.coprime_iff_not_dvd.mpr hd)

/-- With `P = z#`, `ν q = 1` for all primes `q > z` (in particular for primes
in `[Z, 2Z]` with `Z > z`, as required by the fundamental lemma). -/
theorem brunNu_primorial_eq_one_of_prime_gt {t z q : ℕ} (hq : q.Prime)
    (hzq : z < q) : brunNu (primorial z) t q = 1 :=
  brunNu_eq_one_of_prime_not_dvd (squarefree_primorial z) hq fun h =>
    absurd (hq.dvd_primorial_iff.mp h) (by omega)

/-- The Brun weights give an `IsUpperMoebius` sequence, hence plug directly
into Mathlib's `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`. -/
theorem brun_isUpperMoebius {P : ℕ} (hP : Squarefree P) (t : ℕ) :
    BoundingSieve.IsUpperMoebius fun d => (brunLambda P t d : ℝ) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [← Int.cast_sum]
    change (if n = 1 then (1 : ℝ) else 0) ≤ (brunNu P t n : ℝ)
    by_cases h1 : n = 1
    · rw [if_pos h1, h1]
      have hnu1 : brunNu P t 1 = 1 := by
        rw [brunNu, Nat.divisors_one, Finset.sum_singleton, brunLambda_one]
      rw [hnu1]
      norm_num
    · rw [if_neg h1]
      exact Int.cast_nonneg.mpr (brunNu_nonneg hP hn)

/-! ### The main term `∑_{d ∣ P} λ_d / d` -/

/-- The full Möbius sum over subsets of `S`: a pure powerset identity
`∑_{s ⊆ S} (-1)^#s ∏_{q ∈ s} q⁻¹ = ∏_{q ∈ S} (1 - q⁻¹)`. -/
theorem sum_powerset_neg_one_pow_mul_prod_inv (S : Finset ℕ) :
    ∑ s ∈ S.powerset, (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹
      = ∏ q ∈ S, (1 - (q : ℚ)⁻¹) := by
  have e : ∏ q ∈ S, (1 - (q : ℚ)⁻¹) = ∏ q ∈ S, (-(q : ℚ)⁻¹ + 1) :=
    Finset.prod_congr rfl fun q _ => by ring
  rw [e, Finset.prod_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_neg]
  simp

/-- The complete Möbius sum `∑_{d ∣ P} μ d / d = ∏_{q ∣ P} (1 - q⁻¹)` over
ℚ for squarefree `P`. -/
theorem brun_sum_moebius_div {P : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (μ d : ℚ) / d
      = ∏ q ∈ P.primeFactors, (1 - (q : ℚ)⁻¹) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hbij : ∑ d ∈ P.divisors, (μ d : ℚ) / d
      = ∑ s ∈ P.primeFactors.powerset,
          (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹ := by
    refine Finset.sum_nbij' (i := fun d => d.primeFactors)
      (j := fun s => ∏ q ∈ s, q) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      exact Finset.mem_powerset.mpr
        (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP0)
    · intro s hs
      rw [Finset.mem_powerset] at hs
      have hdvd : ∏ q ∈ s, q ∣ P := by
        rw [← Nat.prod_primeFactors_of_squarefree hP]
        exact Finset.prod_dvd_prod_of_subset s P.primeFactors _ hs
      exact Nat.mem_divisors.mpr ⟨hdvd, hP0⟩
    · intro d hd
      exact Nat.prod_primeFactors_of_squarefree
        (Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hP)
    · intro s hs
      exact Nat.primeFactors_prod fun q hq =>
        Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hq)
    · intro d hd
      have hdsq : Squarefree d :=
        Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hP
      have hμ : (μ d : ℤ) = (-1) ^ d.primeFactors.card := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
        exact moebius_prod_primeFactors (P := d) Finset.subset_rfl
      have hd' : (d : ℚ) = ∏ q ∈ d.primeFactors, (q : ℚ) := by
        rw [← Nat.prod_primeFactors_of_squarefree hdsq, Nat.cast_prod]
      have hμ' : (μ d : ℚ) = (-1 : ℚ) ^ d.primeFactors.card := by
        exact_mod_cast hμ
      rw [div_eq_mul_inv, hd', Finset.prod_inv_distrib, hμ']
  rw [hbij, sum_powerset_neg_one_pow_mul_prod_inv]

/-- The Brun main term: `∑_{d ∣ P} λ_d / d` equals the truncated powerset
sum. -/
theorem brun_sum_lambda_div {P t : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (brunLambda P t d : ℚ) / d
      = ∑ s ∈ P.primeFactors.powerset with s.card ≤ 2 * t,
          (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹ := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have step : ∀ d ∈ P.divisors, (brunLambda P t d : ℚ) / d
      = if d.primeFactors.card ≤ 2 * t then (μ d : ℚ) / d else 0 := by
    intro d hd
    have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
    by_cases hω : d.primeFactors.card ≤ 2 * t
    · rw [brunLambda_of_dvd hdvd hω, if_pos hω]
    · rw [show brunLambda P t d = 0 from if_neg fun h => hω h.2, if_neg hω]
      simp
  rw [Finset.sum_congr rfl step, ← Finset.sum_filter]
  refine Finset.sum_nbij' (i := fun d => d.primeFactors)
    (j := fun s => ∏ q ∈ s, q) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Nat.primeFactors_mono (Nat.mem_divisors.mp hd.1).1 hP0), hd.2⟩
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    have hdvd : ∏ q ∈ s, q ∣ P := by
      rw [← Nat.prod_primeFactors_of_squarefree hP]
      exact Finset.prod_dvd_prod_of_subset s P.primeFactors _ hs.1
    have hpfs : (∏ q ∈ s, q).primeFactors = s :=
      Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (hs.1 hq)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, hP0⟩, by rw [hpfs]; exact hs.2⟩
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hP)
  · intro s hs
    exact Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors
      ((Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1) hq)
  · intro d hd
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hP
    have hμ : (μ d : ℤ) = (-1) ^ d.primeFactors.card := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
      exact moebius_prod_primeFactors (P := d) Finset.subset_rfl
    have hd' : (d : ℚ) = ∏ q ∈ d.primeFactors, (q : ℚ) := by
      rw [← Nat.prod_primeFactors_of_squarefree hdsq, Nat.cast_prod]
    have hμ' : (μ d : ℚ) = (-1 : ℚ) ^ d.primeFactors.card := by
      exact_mod_cast hμ
    rw [div_eq_mul_inv, hd', Finset.prod_inv_distrib, hμ']

/-- **Main term decomposition**: `∑_{d ∣ P} λ_d / d` equals the full product
`∏_{q ∣ P} (1 - q⁻¹)` minus the tail `∑_{s ⊆ primeFactors P, #s > 2t}
(-1)^#s ∏_{q ∈ s} q⁻¹`. -/
theorem brun_sum_lambda_div_eq_prod_sub_tail {P t : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, (brunLambda P t d : ℚ) / d
      = ∏ q ∈ P.primeFactors, (1 - (q : ℚ)⁻¹)
        - ∑ s ∈ P.primeFactors.powerset with 2 * t < s.card,
            (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹ := by
  rw [brun_sum_lambda_div hP]
  have hdisj : Disjoint (P.primeFactors.powerset.filter fun s => s.card ≤ 2 * t)
      (P.primeFactors.powerset.filter fun s => ¬ s.card ≤ 2 * t) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hunion : P.primeFactors.powerset.filter (fun s => s.card ≤ 2 * t)
      ∪ P.primeFactors.powerset.filter (fun s => ¬ s.card ≤ 2 * t)
      = P.primeFactors.powerset := Finset.filter_union_filter_not_eq _
  have hsplit : ∑ s ∈ P.primeFactors.powerset,
        (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹
      = ∑ s ∈ P.primeFactors.powerset with s.card ≤ 2 * t,
          (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹
        + ∑ s ∈ P.primeFactors.powerset with ¬ s.card ≤ 2 * t,
          (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹ := by
    rw [← hunion, Finset.sum_union hdisj]
  rw [sum_powerset_neg_one_pow_mul_prod_inv] at hsplit
  have hflt : P.primeFactors.powerset.filter (fun s => ¬ s.card ≤ 2 * t)
      = P.primeFactors.powerset.filter fun s => 2 * t < s.card :=
    Finset.filter_congr fun s _ => not_le
  rw [hflt] at hsplit
  rw [← hsplit]
  ring

/-- The main term differs from `∏_{q ∣ P} (1 - q⁻¹)` by at most the absolute
tail `∑_{s ⊆ primeFactors P, #s > 2t} ∏_{q ∈ s} q⁻¹`. -/
theorem brun_abs_sum_lambda_div_sub_prod_le {P t : ℕ} (hP : Squarefree P) :
    |∑ d ∈ P.divisors, (brunLambda P t d : ℚ) / d
        - ∏ q ∈ P.primeFactors, (1 - (q : ℚ)⁻¹)|
      ≤ ∑ s ∈ P.primeFactors.powerset with 2 * t < s.card,
          ∏ q ∈ s, (q : ℚ)⁻¹ := by
  rw [brun_sum_lambda_div_eq_prod_sub_tail hP]
  have hrw : ∏ q ∈ P.primeFactors, (1 - (q : ℚ)⁻¹)
        - ∑ s ∈ P.primeFactors.powerset with 2 * t < s.card,
            (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹
        - ∏ q ∈ P.primeFactors, (1 - (q : ℚ)⁻¹)
      = -∑ s ∈ P.primeFactors.powerset with 2 * t < s.card,
          (-1 : ℚ) ^ s.card * ∏ q ∈ s, (q : ℚ)⁻¹ := by ring
  rw [hrw, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro s _
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Finset.prod_nonneg fun q _ =>
      inv_nonneg.mpr (Nat.cast_nonneg _))]

/-- **Rankin bound for the tail** (real version): for `y ≥ 1`,
`y^{2t} · tail ≤ ∏_{q ∈ S} (1 + y/q)`. -/
theorem brun_tail_le {S : Finset ℕ} {t : ℕ} {y : ℝ} (hy : 1 ≤ y) :
    y ^ (2 * t) * ∑ s ∈ S.powerset with 2 * t < s.card, ∏ q ∈ s, (q : ℝ)⁻¹
      ≤ ∏ q ∈ S, (1 + (q : ℝ)⁻¹ * y) := by
  have hprod : ∏ q ∈ S, (1 + (q : ℝ)⁻¹ * y)
      = ∑ s ∈ S.powerset, (∏ q ∈ s, (q : ℝ)⁻¹) * y ^ s.card := by
    have e : ∏ q ∈ S, (1 + (q : ℝ)⁻¹ * y)
        = ∏ q ∈ S, ((q : ℝ)⁻¹ * y + 1) :=
      Finset.prod_congr rfl fun q _ => by ring
    rw [e, Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.prod_mul_pow_card]
    simp
  rw [hprod]
  calc y ^ (2 * t) * ∑ s ∈ S.powerset with 2 * t < s.card, ∏ q ∈ s, (q : ℝ)⁻¹
      = ∑ s ∈ S.powerset with 2 * t < s.card,
          (∏ q ∈ s, (q : ℝ)⁻¹) * y ^ (2 * t) := by
        rw [mul_comm, Finset.sum_mul]
    _ ≤ ∑ s ∈ S.powerset with 2 * t < s.card,
          (∏ q ∈ s, (q : ℝ)⁻¹) * y ^ s.card := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_filter] at hs
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hy (Nat.le_of_lt hs.2))
          (Finset.prod_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ ∑ s ∈ S.powerset, (∏ q ∈ s, (q : ℝ)⁻¹) * y ^ s.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun s _ _ => mul_nonneg
            (Finset.prod_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg _))
            (pow_nonneg (by linarith) _)

/-- **Exponential tail bound**: for `y ≥ 1`,
`y^{2t} · tail ≤ exp(y · ∑_{q ∈ S} q⁻¹)`, i.e.
`tail ≤ y^{-2t} exp(y σ)` with `σ = ∑ q⁻¹`; the choice `y = 2t/σ` gives
`tail ≤ (e σ / 2t)^{2t}`. -/
theorem brun_tail_le_exp {S : Finset ℕ} {t : ℕ} {y : ℝ} (hy : 1 ≤ y) :
    y ^ (2 * t) * ∑ s ∈ S.powerset with 2 * t < s.card, ∏ q ∈ s, (q : ℝ)⁻¹
      ≤ Real.exp (y * ∑ q ∈ S, (q : ℝ)⁻¹) := by
  refine brun_tail_le hy |>.trans ?_
  calc ∏ q ∈ S, (1 + (q : ℝ)⁻¹ * y)
      ≤ Real.exp (∑ q ∈ S, (q : ℝ)⁻¹ * y) :=
        Real.prod_one_add_le_exp_sum _ fun q _ =>
          mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (by linarith)
    _ = Real.exp (y * ∑ q ∈ S, (q : ℝ)⁻¹) := by
        rw [← Finset.sum_mul, mul_comm]

end JSP314
