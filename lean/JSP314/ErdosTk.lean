import JSP314.Defs
import JSP314.QuadMertens
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# JSP-000314 — Erdős's valuation bound for smooth numbers on an
arithmetic progression

For coprime `c, j`, let

  `apSmoothParamCount lo hi c j p`
    = #{r ∈ [lo, hi] : largestPrimeFactor (c·r + j) ≤ p},

the count of `p`-smooth values of the linear progression `n = c·r + j` over
`r ∈ [lo, hi]`.  This file formalizes the classical Erdős valuation argument:
writing `log n = ∑_q v_q(n)·log q` and swapping the order of summation gives

  `T · log(c·lo + j)`
    ≤ `∑_{q ≤ p prime} log q · ∑_{r ∈ [lo,hi]} v_q(c·r + j)`
    ≤ `(hi − lo) · ∑_{q ≤ p} log q / (q − 1)  +  log₂(c·hi + j) · ∑_{q ≤ p} log q`,

because for `q ∤ c` the congruence `q^a ∣ c·r + j` has at most one solution
class mod `q^a`, hence at most `⌊(hi − lo)/q^a⌋ + 1` solutions in `[lo, hi]`,
while for `q ∣ c` (which forces `q ∤ j` by coprimality) it has none.

Combined with the elementary Mertens bound `∑_{q ≤ p} log q/(q−1) ≤ 2 log p + 11`
(`SylvesterSchur.sum_log_div_pred_primesLE_le`, proved in
`JSP314.QuadMertens`) and Chebyshev's `∑_{q ≤ p} log q = θ(p) ≤ p·log 4`
(`Chebyshev.theta_le_log4_mul_x`), this gives the fully explicit unconditional
inequality

  `T · log(c·lo + j) ≤ (hi − lo)·(2 log p + 11) + p·log 4·⌊log₂(c·hi + j)⌋`,

and the natural-number corollary (for `p ≥ 1`)

  `T · ⌊log₂(c·lo + j)⌋ ≤ (hi − lo)·(2·⌊log₂ p⌋ + 18) + 2·p·⌊log₂(c·hi + j)⌋`.

Specializing to the dyadic band `lo = B/2`, `hi = B` yields the headline
`Tsmooth` bounds.
-/

namespace JSP314

open Finset

/-- `apSmoothParamCount lo hi c j p`: the number of `r ∈ [lo, hi]` for which
`c·r + j` is `p`-smooth (largest prime factor `≤ p`). -/
def apSmoothParamCount (lo hi c j p : ℕ) : ℕ :=
  ((Finset.Icc lo hi).filter fun r => largestPrimeFactor (c * r + j) ≤ p).card

/-- The dyadic-band version: `r ∈ [B/2, B]`. -/
def Tsmooth (B c j p : ℕ) : ℕ := apSmoothParamCount (B / 2) B c j p

/-! ### Step 1: pointwise logarithm expansion -/

/-- For `n` with `largestPrimeFactor n ≤ p`,
`log n = ∑_{q ≤ p, q prime} v_q(n)·log q`.  Holds for `n ≤ 1` too (both
sides vanish: `log 0 = log 1 = 0` and the factorization is empty). -/
theorem log_eq_sum_factorization_primesLE {n p : ℕ} (hn : largestPrimeFactor n ≤ p) :
    Real.log n = ∑ q ∈ Nat.primesLE p, (n.factorization q : ℝ) * Real.log q := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [Nat.factorization_zero]
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have : n = 1 := by omega
    subst this
    simp [Nat.factorization_one]
  · have hsupp : n.primeFactors ⊆ Nat.primesLE p := by
      intro q hq
      obtain ⟨hqprime, hqdiv, _⟩ := Nat.mem_primeFactors.mp hq
      exact Nat.mem_primesLE.mpr
        ⟨(prime_dvd_le_largestPrimeFactor hge hqprime hqdiv).trans hn, hqprime⟩
    have hprod : (∏ q ∈ n.primeFactors, (q : ℝ) ^ (n.factorization q)) = (n : ℝ) := by
      have h := Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hpos)
      rw [Nat.prod_factorization_eq_prod_primeFactors] at h
      exact_mod_cast h
    rw [← hprod,
      Real.log_prod (fun q hq =>
        pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hq).ne_zero))]
    trans ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log q
    · exact Finset.sum_congr rfl fun q _ => Real.log_pow _ _
    · refine Finset.sum_subset hsupp fun q _ hq => ?_
      have h0 : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
      simp [h0]

/-! ### Step 2: counting solutions of `m ∣ c·r + j` on an interval -/

/-- If `m` is coprime to `c`, the solutions `r ∈ [lo, hi]` of `m ∣ c·r + j`
lie in a single residue class mod `m`, so there are at most
`⌊(hi − lo)/m⌋ + 1` of them. -/
theorem card_dvd_linear_le {m c j lo hi : ℕ} (_hm : 0 < m) (hmc : Nat.Coprime m c) :
    ((Finset.Icc lo hi).filter fun r => m ∣ c * r + j).card ≤ (hi - lo) / m + 1 := by
  set s := (Finset.Icc lo hi).filter fun r => m ∣ c * r + j with hs
  rcases s.eq_empty_or_nonempty with h | hne
  · simp [h]
  · set r0 := s.min' hne with hr0
    have hr0mem : r0 ∈ (Finset.Icc lo hi).filter fun r => m ∣ c * r + j :=
      hs ▸ s.min'_mem hne
    obtain ⟨hr0Icc, hr0dvd⟩ := Finset.mem_filter.mp hr0mem
    obtain ⟨hr0lo, _⟩ := Finset.mem_Icc.mp hr0Icc
    have hsub : s ⊆ (Finset.Icc 0 ((hi - lo) / m)).image (fun k => r0 + m * k) := by
      intro r hr
      have hr' : r ∈ (Finset.Icc lo hi).filter fun r => m ∣ c * r + j := hs ▸ hr
      obtain ⟨hrIcc, hrdvd⟩ := Finset.mem_filter.mp hr'
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hrIcc
      have hr0le : r0 ≤ r := Finset.min'_le s r hr
      have hdiff : m ∣ c * r + j - (c * r0 + j) := Nat.dvd_sub hrdvd hr0dvd
      have hmul : c * r0 ≤ c * r := Nat.mul_le_mul_left c hr0le
      have heq : c * r + j - (c * r0 + j) = c * (r - r0) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [heq, mul_comm] at hdiff
      have hdvd : m ∣ r - r0 := hmc.dvd_mul_right.mp hdiff
      have hkbound : (r - r0) / m ≤ (hi - lo) / m := by
        have h1 : r - r0 ≤ hi - lo := by omega
        exact Nat.div_le_div_right h1
      refine Finset.mem_image.mpr ⟨(r - r0) / m,
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, hkbound⟩, ?_⟩
      have h2 : m * ((r - r0) / m) = r - r0 := Nat.mul_div_cancel' hdvd
      show r0 + m * ((r - r0) / m) = r
      rw [h2]
      exact Nat.add_sub_of_le hr0le
    refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
    rw [Nat.card_Icc]
    exact Nat.sub_le _ _

/-- For a prime power `q^a` (`a ≥ 1`), the number of `r ∈ [lo, hi]` with
`q^a ∣ c·r + j` is at most `⌊(hi − lo)/q^a⌋ + 1`; if `q ∣ c` there are no
solutions at all (coprimality `gcd(c,j) = 1` gives `q ∤ j`). -/
theorem card_powdvd_linear_le {q c j lo hi : ℕ} (hq : q.Prime) (hcj : Nat.Coprime c j)
    {a : ℕ} (ha : 1 ≤ a) :
    ((Finset.Icc lo hi).filter fun r => q ^ a ∣ c * r + j).card ≤ (hi - lo) / q ^ a + 1 := by
  by_cases hqc : q ∣ c
  · have hqdj : ¬ q ∣ j := by
      intro h
      have h2 : q ∣ Nat.gcd c j := Nat.dvd_gcd hqc h
      rw [hcj] at h2
      exact hq.not_dvd_one h2
    have hempty : (Finset.Icc lo hi).filter (fun r => q ^ a ∣ c * r + j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro r _ hdvd
      apply hqdj
      have hq1 : q ∣ q ^ a := dvd_pow_self q (Nat.ne_of_gt ha)
      have hq2 : q ∣ c * r + j := hq1.trans hdvd
      have hq3 : q ∣ c * r := dvd_mul_of_dvd_left hqc r
      have hq4 : q ∣ (c * r + j) - c * r := Nat.dvd_sub hq2 hq3
      have hsub : c * r + j - c * r = j := by omega
      rwa [hsub] at hq4
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have hmc : (q ^ a).Coprime c := by
      rw [Nat.coprime_pow_left_iff ha]
      exact hq.coprime_iff_not_dvd.mpr hqc
    exact card_dvd_linear_le (pow_pos hq.pos a) hmc

/-! ### Step 3: the valuation swap -/

/-- For `n ≠ 0`, `v_q(n)` equals the number of exponents `a ≥ 1` with
`q^a ∣ n`, counted up to any `L ≥ v_q(n)`. -/
theorem factorization_le_card_Ico {q n L : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (hL : ∀ a, q ^ a ∣ n → a ≤ L) :
    n.factorization q ≤ ((Finset.Ico 1 (L + 1)).filter fun a => q ^ a ∣ n).card := by
  rcases Nat.eq_zero_or_pos (n.factorization q) with hv0 | hvpos
  · rw [hv0]
    exact Nat.zero_le _
  · have hvdvd : q ^ n.factorization q ∣ n := Nat.ordProj_dvd n q
    have hvL : n.factorization q ≤ L := hL _ hvdvd
    have hfilter : (Finset.Ico 1 (L + 1)).filter (fun a => q ^ a ∣ n) =
        Finset.Ico 1 (n.factorization q + 1) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, hd⟩
        exact ⟨h1, Nat.lt_succ_iff.mpr ((hq.pow_dvd_iff_le_factorization hn).mp hd)⟩
      · rintro ⟨h1, h2⟩
        have hav : a ≤ n.factorization q := Nat.lt_succ_iff.mp h2
        exact ⟨⟨h1, Nat.lt_succ_iff.mpr (hav.trans hvL)⟩,
          (pow_dvd_pow q hav).trans hvdvd⟩
    rw [hfilter, Nat.card_Ico]
    omega

/-- `∑_r v_q(c·r+j) ≤ ∑_{1 ≤ a ≤ log₂(c·hi+j)} (⌊(hi−lo)/q^a⌋ + 1)`. -/
theorem sum_factorization_le {q c j lo hi : ℕ} (hq : q.Prime) (hcj : Nat.Coprime c j) :
    (∑ r ∈ Finset.Icc lo hi, (c * r + j).factorization q) ≤
      ∑ a ∈ Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1), ((hi - lo) / q ^ a + 1) := by
  have hper : ∀ r ∈ Finset.Icc lo hi,
      (c * r + j).factorization q ≤
        ((Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1)).filter
          fun a => q ^ a ∣ c * r + j).card := by
    intro r hr
    obtain ⟨_, hhi⟩ := Finset.mem_Icc.mp hr
    rcases Nat.eq_zero_or_pos (c * r + j) with hn0 | hnpos
    · simp [hn0, Nat.factorization_zero]
    · apply factorization_le_card_Ico hq hnpos.ne'
      intro a ha
      have h1 : q ^ a ≤ c * r + j := Nat.le_of_dvd hnpos ha
      have h2 : (2 : ℕ) ^ a ≤ c * hi + j :=
        ((Nat.pow_le_pow_left hq.two_le a).trans h1).trans (by
          have hmul := Nat.mul_le_mul_left c hhi
          omega)
      exact Nat.le_log_of_pow_le Nat.one_lt_two h2
  calc ∑ r ∈ Finset.Icc lo hi, (c * r + j).factorization q
      ≤ ∑ r ∈ Finset.Icc lo hi,
          ((Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1)).filter
            fun a => q ^ a ∣ c * r + j).card :=
        Finset.sum_le_sum hper
    _ = ∑ r ∈ Finset.Icc lo hi, ∑ a ∈ Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1),
          ite (q ^ a ∣ c * r + j) 1 0 :=
        Finset.sum_congr rfl fun r _ =>
          Finset.card_filter (fun a => q ^ a ∣ c * r + j) _
    _ = ∑ a ∈ Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1),
          ∑ r ∈ Finset.Icc lo hi, ite (q ^ a ∣ c * r + j) 1 0 :=
        Finset.sum_comm
    _ = ∑ a ∈ Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1),
          ((Finset.Icc lo hi).filter fun r => q ^ a ∣ c * r + j).card :=
        Finset.sum_congr rfl fun a _ =>
          (Finset.card_filter (fun r => q ^ a ∣ c * r + j) _).symm
    _ ≤ ∑ a ∈ Finset.Ico 1 (Nat.log 2 (c * hi + j) + 1), ((hi - lo) / q ^ a + 1) := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact card_powdvd_linear_le hq hcj (Finset.mem_Ico.mp ha).1

/-- The same bound in `ℝ`, packaged as
`∑_r v_q ≤ (hi − lo)/(q − 1) + ⌊log₂(c·hi + j)⌋` (finite geometric sum). -/
theorem sum_factorization_real_le {q c j lo hi : ℕ} (hq : q.Prime)
    (hcj : Nat.Coprime c j) :
    (∑ r ∈ Finset.Icc lo hi, (((c * r + j).factorization q : ℕ) : ℝ)) ≤
      ((hi - lo : ℕ) : ℝ) / ((q : ℝ) - 1) + (Nat.log 2 (c * hi + j) : ℝ) := by
  set L := Nat.log 2 (c * hi + j) with hL
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have h := sum_factorization_le hq hcj (q := q) (c := c) (j := j) (lo := lo) (hi := hi)
  have hR : (∑ r ∈ Finset.Icc lo hi, (((c * r + j).factorization q : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Ico 1 (L + 1), (((hi - lo) / q ^ a + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  refine hR.trans ?_
  have hterm : ∀ a ∈ Finset.Ico 1 (L + 1),
      (((hi - lo) / q ^ a + 1 : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) * (1 / q) ^ a + 1 := by
    intro a _
    calc (((hi - lo) / q ^ a + 1 : ℕ) : ℝ) = (((hi - lo) / q ^ a : ℕ) : ℝ) + 1 := by
          norm_cast
      _ ≤ ((hi - lo : ℕ) : ℝ) / ((q : ℝ) ^ a) + 1 := by
          have h1 : (((hi - lo) / q ^ a : ℕ) : ℝ) ≤ ((hi - lo : ℕ) : ℝ) / ((q : ℝ) ^ a) := by
            rw [← Nat.cast_pow]
            exact Nat.cast_div_le
          linarith
      _ = ((hi - lo : ℕ) : ℝ) * (1 / q) ^ a + 1 := by
          rw [div_eq_mul_inv, ← inv_pow, ← one_div]
  have hgeo : ∑ a ∈ Finset.Ico 1 (L + 1), ((1 : ℝ) / q) ^ a ≤ 1 / ((q : ℝ) - 1) := by
    have h1 : (1 : ℝ) / q < 1 := by
      rw [div_lt_one (by linarith : (0 : ℝ) < q)]
      linarith
    have h0 : (0 : ℝ) ≤ 1 / q := by positivity
    have h2 := geom_sum_Ico_le_of_lt_one (m := 1) (n := L + 1) (x := (1 : ℝ) / q) h0 h1
    refine h2.trans (le_of_eq ?_)
    rw [pow_one]
    field_simp
  calc ∑ a ∈ Finset.Ico 1 (L + 1), (((hi - lo) / q ^ a + 1 : ℕ) : ℝ)
      ≤ ∑ a ∈ Finset.Ico 1 (L + 1), (((hi - lo : ℕ) : ℝ) * (1 / q) ^ a + 1) :=
        Finset.sum_le_sum hterm
    _ = ((hi - lo : ℕ) : ℝ) * (∑ a ∈ Finset.Ico 1 (L + 1), ((1 : ℝ) / q) ^ a)
          + (L : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        rw [Finset.sum_const, Nat.card_Ico]
        simp
    _ ≤ ((hi - lo : ℕ) : ℝ) * (1 / ((q : ℝ) - 1)) + (L : ℝ) := by
        have hd : (0 : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_left hgeo hd
        linarith
    _ = ((hi - lo : ℕ) : ℝ) / ((q : ℝ) - 1) + (L : ℝ) := by
        rw [mul_one_div]

/-! ### Step 4: assembling the Erdős bound -/

/-- **The Erdős valuation bound (exact form).**  For `gcd(c, j) = 1`,

  `T · log(c·lo + j) ≤ (hi − lo)·∑_{q ≤ p} log q/(q−1)
                       + ⌊log₂(c·hi + j)⌋·∑_{q ≤ p} log q`,

where `T` counts `r ∈ [lo, hi]` with `c·r + j` `p`-smooth. -/
theorem apSmoothParamCount_mul_log_le {lo hi c j p : ℕ} (hcj : Nat.Coprime c j) :
    (apSmoothParamCount lo hi c j p : ℝ) * Real.log ↑(c * lo + j) ≤
      ((hi - lo : ℕ) : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1))
        + (Nat.log 2 (c * hi + j) : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q) := by
  set S := (Finset.Icc lo hi).filter fun r => largestPrimeFactor (c * r + j) ≤ p
    with hS
  set L := Nat.log 2 (c * hi + j) with hL
  have hScard : apSmoothParamCount lo hi c j p = S.card := by
    unfold apSmoothParamCount
    rw [hS]
  -- Pointwise expansion and swap of the double sum.
  have hsum : ∑ r ∈ S, Real.log ↑(c * r + j) =
      ∑ q ∈ Nat.primesLE p, Real.log q *
        ∑ r ∈ S, (((c * r + j).factorization q : ℕ) : ℝ) := by
    trans ∑ r ∈ S, ∑ q ∈ Nat.primesLE p,
        ((c * r + j).factorization q : ℝ) * Real.log q
    · refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨_, hlp⟩ := Finset.mem_filter.mp (hS ▸ hr)
      exact log_eq_sum_factorization_primesLE hlp
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  -- Lower bound: each counted `r` has `c·r + j ≥ c·lo + j`.
  have hlow : (S.card : ℝ) * Real.log ↑(c * lo + j) ≤
      ∑ r ∈ S, Real.log ↑(c * r + j) := by
    have hconst : ∑ r ∈ S, Real.log ↑(c * lo + j) =
        (S.card : ℝ) * Real.log ↑(c * lo + j) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨hrIcc, _⟩ := Finset.mem_filter.mp (hS ▸ hr)
    have hle : (↑(c * lo + j) : ℝ) ≤ ↑(c * r + j) := by
      have h1 := (Finset.mem_Icc.mp hrIcc).1
      have h2 : c * lo ≤ c * r := Nat.mul_le_mul_left c h1
      exact_mod_cast (Nat.add_le_add_right h2 j)
    rcases Nat.eq_zero_or_pos (c * lo + j) with h0 | hpos
    · have hx : (↑(c * lo + j) : ℝ) = 0 := by exact_mod_cast h0
      rw [hx, Real.log_zero]
      exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (by exact_mod_cast hpos) hle
  -- Bound each prime's contribution.
  have hSsub : S ⊆ Finset.Icc lo hi := by rw [hS]; exact Finset.filter_subset _ _
  have hupper : ∑ q ∈ Nat.primesLE p,
        Real.log q * ∑ r ∈ S, (((c * r + j).factorization q : ℕ) : ℝ)
      ≤ ∑ q ∈ Nat.primesLE p,
        Real.log q * (((hi - lo : ℕ) : ℝ) / ((q : ℝ) - 1) + (L : ℝ)) := by
    refine Finset.sum_le_sum fun q hq => ?_
    have hqq := Nat.prime_of_mem_primesLE hq
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hqq.one_le)
    have hsub : ∑ r ∈ S, (((c * r + j).factorization q : ℕ) : ℝ) ≤
        ∑ r ∈ Finset.Icc lo hi, (((c * r + j).factorization q : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub fun x _ _ => Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left (hsub.trans (sum_factorization_real_le hqq hcj)) hlog
  have hexpand : ∑ q ∈ Nat.primesLE p,
        Real.log q * (((hi - lo : ℕ) : ℝ) / ((q : ℝ) - 1) + (L : ℝ))
      = ((hi - lo : ℕ) : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1))
          + (L : ℝ) * ∑ q ∈ Nat.primesLE p, Real.log q := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    · rw [← Finset.sum_mul]
      exact mul_comm _ _
  calc (apSmoothParamCount lo hi c j p : ℝ) * Real.log ↑(c * lo + j)
      = (S.card : ℝ) * Real.log ↑(c * lo + j) := by rw [hScard]
    _ ≤ ∑ r ∈ S, Real.log ↑(c * r + j) := hlow
    _ = ∑ q ∈ Nat.primesLE p, Real.log q *
          ∑ r ∈ S, (((c * r + j).factorization q : ℕ) : ℝ) := hsum
    _ ≤ ∑ q ∈ Nat.primesLE p,
          Real.log q * (((hi - lo : ℕ) : ℝ) / ((q : ℝ) - 1) + (L : ℝ)) := hupper
    _ = ((hi - lo : ℕ) : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1))
          + (L : ℝ) * ∑ q ∈ Nat.primesLE p, Real.log q := hexpand

/-- **Fully explicit unconditional form.**  For `gcd(c,j) = 1` and `p ≥ 1`,
`T·log(c·lo + j) ≤ (hi−lo)·(2 log p + 11) + p·log 4·⌊log₂(c·hi+j)⌋`. -/
theorem apSmoothParamCount_mul_log_le_explicit {lo hi c j p : ℕ}
    (hcj : Nat.Coprime c j) (hp : 1 ≤ p) :
    (apSmoothParamCount lo hi c j p : ℝ) * Real.log ↑(c * lo + j) ≤
      ((hi - lo : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (c * hi + j) : ℝ) * (p * Real.log 4) := by
  refine (apSmoothParamCount_mul_log_le hcj).trans ?_
  have hmertens := SylvesterSchur.sum_log_div_pred_primesLE_le hp
  have hsum_eq : (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1))
      = ∑ q ∈ Nat.primesLE p, Real.log q / (((q - 1 : ℕ)) : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq1 : 1 ≤ q := (Nat.prime_of_mem_primesLE hq).one_le
    rw [Nat.cast_sub hq1, Nat.cast_one]
  rw [hsum_eq]
  have htheta : ∑ q ∈ Nat.primesLE p, Real.log q ≤ (p : ℝ) * Real.log 4 := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]
    have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg p)
    rwa [mul_comm (Real.log 4) (p : ℝ)] at h
  exact add_le_add
    (mul_le_mul_of_nonneg_left hmertens (Nat.cast_nonneg _))
    (mul_le_mul_of_nonneg_left htheta (Nat.cast_nonneg _))

/-! ### Natural-number corollaries -/

/-- The `Nat.log 2` form of the bound: for `gcd(c,j) = 1`, `p ≥ 1`,

  `T·⌊log₂(c·lo+j)⌋ ≤ (hi−lo)·(2·⌊log₂ p⌋ + 18) + 2·p·⌊log₂(c·hi+j)⌋`. -/
theorem apSmoothParamCount_mul_natlog_le {lo hi c j p : ℕ}
    (hcj : Nat.Coprime c j) (hp : 1 ≤ p) :
    apSmoothParamCount lo hi c j p * Nat.log 2 (c * lo + j) ≤
      (hi - lo) * (2 * Nat.log 2 p + 18) + 2 * p * Nat.log 2 (c * hi + j) := by
  have hexp := apSmoothParamCount_mul_log_le_explicit (lo := lo) (hi := hi)
    (c := c) (j := j) (p := p) hcj hp
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2d9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- ⌊log₂ x⌋·log 2 ≤ log x
  have hN0 : (Nat.log 2 (c * lo + j) : ℝ) * Real.log 2 ≤
      Real.log ↑(c * lo + j) := by
    rcases Nat.eq_zero_or_pos (c * lo + j) with h0 | hpos
    · simp [h0]
    · have h : ((2 : ℝ) ^ Nat.log 2 (c * lo + j)) ≤ ↑(c * lo + j) := by
        exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
      calc (Nat.log 2 (c * lo + j) : ℝ) * Real.log 2
          = Real.log ((2 : ℝ) ^ Nat.log 2 (c * lo + j)) := by
            rw [Real.log_pow]
        _ ≤ Real.log ↑(c * lo + j) := Real.log_le_log (by positivity) h
  -- log p ≤ (⌊log₂ p⌋ + 1)·log 2
  have hlogp : Real.log p ≤ (Nat.log 2 p + 1 : ℝ) * Real.log 2 := by
    have h : (p : ℝ) < (2 : ℝ) ^ (Nat.log 2 p + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self one_lt_two p
    calc Real.log p ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 p + 1)) :=
          Real.log_le_log (by exact_mod_cast hp) h.le
      _ = (Nat.log 2 p + 1 : ℝ) * Real.log 2 := by
          rw [Real.log_pow]; push_cast; ring
  have h2logp : 2 * Real.log p + 11 ≤ (2 * (Nat.log 2 p : ℝ) + 18) * Real.log 2 := by
    linarith [hlogp]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  -- multiply the lower bound through
  have key : ((apSmoothParamCount lo hi c j p * Nat.log 2 (c * lo + j) : ℕ) : ℝ)
        * Real.log 2
      ≤ ((hi - lo : ℕ) : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (c * hi + j) : ℝ) * (p * Real.log 4) := by
    have h := mul_le_mul_of_nonneg_left hN0
      (Nat.cast_nonneg (apSmoothParamCount lo hi c j p))
    calc ((apSmoothParamCount lo hi c j p * Nat.log 2 (c * lo + j) : ℕ) : ℝ)
          * Real.log 2
        = (apSmoothParamCount lo hi c j p : ℝ)
            * ((Nat.log 2 (c * lo + j) : ℝ) * Real.log 2) := by push_cast; ring
      _ ≤ (apSmoothParamCount lo hi c j p : ℝ) * Real.log ↑(c * lo + j) := h
      _ ≤ _ := hexp
  -- compare with the natural-number RHS after dividing by log 2
  have hfinal : ((apSmoothParamCount lo hi c j p * Nat.log 2 (c * lo + j) : ℕ) : ℝ)
      ≤ (((hi - lo) * (2 * Nat.log 2 p + 18) + 2 * p * Nat.log 2 (c * hi + j) : ℕ)
          : ℝ) := by
    have h1 := (le_div_iff₀ hlog2pos).mpr key
    have h3 : ((((hi - lo) * (2 * Nat.log 2 p + 18)
            + 2 * p * Nat.log 2 (c * hi + j) : ℕ)) : ℝ)
        = ((hi - lo : ℕ) : ℝ) * (2 * (Nat.log 2 p : ℝ) + 18)
            + 2 * p * (Nat.log 2 (c * hi + j) : ℝ) := by
      push_cast
      ring
    have h2 : (((hi - lo : ℕ) : ℝ) * (2 * Real.log p + 11)
          + (Nat.log 2 (c * hi + j) : ℝ) * (p * Real.log 4)) / Real.log 2
        ≤ (((hi - lo) * (2 * Nat.log 2 p + 18)
            + 2 * p * Nat.log 2 (c * hi + j) : ℕ) : ℝ) := by
      rw [div_le_iff₀ hlog2pos, h3, hlog4]
      have ht1 := mul_le_mul_of_nonneg_left h2logp (Nat.cast_nonneg (hi - lo))
      nlinarith [ht1]
    exact h1.trans h2
  exact Nat.cast_le.mp hfinal

/-! ### Headline theorems on the dyadic band `[B/2, B]` -/

/-- **Erdős bound, exact prime-sum form**, for `r ∈ [B/2, B]`:

  `T·log(c·⌊B/2⌋ + j) ≤ B·∑_{q ≤ p} log q/(q−1) + log₂(cB+j)·∑_{q ≤ p} log q`. -/
theorem Tsmooth_mul_log_le {B c j p : ℕ} (hcj : Nat.Coprime c j) :
    (Tsmooth B c j p : ℝ) * Real.log ↑(c * (B / 2) + j) ≤
      (B : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1))
        + (Nat.log 2 (c * B + j) : ℝ) * (∑ q ∈ Nat.primesLE p, Real.log q) := by
  have h := apSmoothParamCount_mul_log_le (lo := B / 2) (hi := B) (c := c) (j := j)
    (p := p) hcj
  have hle : ((B - B / 2 : ℕ) : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hA : 0 ≤ (∑ q ∈ Nat.primesLE p, Real.log q / ((q : ℝ) - 1)) :=
    Finset.sum_nonneg fun q hq =>
      div_nonneg (Real.log_natCast_nonneg q) (by
        have h2 : (2 : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primesLE hq).two_le
        linarith)
  exact h.trans
    (add_le_add (mul_le_mul_of_nonneg_right hle hA) le_rfl)

/-- **Erdős bound, explicit form** for the dyadic band:
`T·log(c·⌊B/2⌋+j) ≤ B·(2 log p + 11) + p·log 4·⌊log₂(cB+j)⌋` for `p ≥ 1`. -/
theorem Tsmooth_mul_log_le_explicit {B c j p : ℕ} (hcj : Nat.Coprime c j)
    (hp : 1 ≤ p) :
    (Tsmooth B c j p : ℝ) * Real.log ↑(c * (B / 2) + j) ≤
      (B : ℝ) * (2 * Real.log p + 11)
        + (Nat.log 2 (c * B + j) : ℝ) * (p * Real.log 4) := by
  have h := apSmoothParamCount_mul_log_le_explicit (lo := B / 2) (hi := B) (c := c)
    (j := j) (p := p) hcj hp
  have hle : ((B - B / 2 : ℕ) : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hA : (0 : ℝ) ≤ 2 * Real.log p + 11 := by
    have := Real.log_natCast_nonneg p
    linarith
  exact h.trans
    (add_le_add (mul_le_mul_of_nonneg_right hle hA) le_rfl)

/-- **Erdős bound, integer form**:
`T·⌊log₂(c·⌊B/2⌋+j)⌋ ≤ B·(2·⌊log₂ p⌋ + 18) + 2·p·⌊log₂(cB+j)⌋` for `p ≥ 1`. -/
theorem Tsmooth_mul_natlog_le {B c j p : ℕ} (hcj : Nat.Coprime c j)
    (hp : 1 ≤ p) :
    Tsmooth B c j p * Nat.log 2 (c * (B / 2) + j) ≤
      B * (2 * Nat.log 2 p + 18) + 2 * p * Nat.log 2 (c * B + j) := by
  have h := apSmoothParamCount_mul_natlog_le (lo := B / 2) (hi := B) (c := c)
    (j := j) (p := p) hcj hp
  refine h.trans ?_
  have h1 := Nat.mul_le_mul_right (2 * Nat.log 2 p + 18) (Nat.sub_le B (B / 2))
  omega

/-! ### Bridge to the naive AP count -/

/-- `APsmoothCount B c a p`: the number of `n ∈ [1, B]` with `n ≡ a (mod c)`
that are `p`-smooth. -/
def APsmoothCount (B c a p : ℕ) : ℕ :=
  ((Finset.Icc 1 B).filter fun n => n % c = a % c ∧ largestPrimeFactor n ≤ p).card

/-- Writing `n = c·(n/c) + (a % c)` maps the AP count into the parametrized
count over `r ∈ [0, B/c]` (the map `n ↦ n/c` lands there since
`c·(n/c) ≤ n ≤ B`). -/
theorem APsmoothCount_le_apSmoothParamCount (B c a p : ℕ) :
    APsmoothCount B c a p ≤ apSmoothParamCount 0 (B / c) c (a % c) p := by
  unfold APsmoothCount apSmoothParamCount
  have hsub : ((Finset.Icc 1 B).filter
        fun n => n % c = a % c ∧ largestPrimeFactor n ≤ p)
      ⊆ ((Finset.Icc 0 (B / c)).filter
          fun r => largestPrimeFactor (c * r + a % c) ≤ p).image
            (fun r => c * r + a % c) := by
    intro n hn
    obtain ⟨hnIcc, hmod, hlp⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, hB⟩ := Finset.mem_Icc.mp hnIcc
    refine Finset.mem_image.mpr ⟨n / c, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos c with hc | hc
        · simp [hc]
        · exact Nat.div_le_div_right hB
      · have h : c * (n / c) + a % c = n := by
          have h2 := Nat.div_add_mod n c
          omega
        rw [h]
        exact hlp
    · have h2 := Nat.div_add_mod n c
      omega
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end JSP314
