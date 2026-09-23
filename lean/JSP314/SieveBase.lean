import JSP314.Defs
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# JSP-000314 — elementary sieve upper bounds

This file collects elementary *upper-bound* sieve estimates used to control
counts of smooth numbers and sifted integer sets.

## Main results

* `geom_sum_le_one_sub_inv`: finite geometric series bound
  `∑_{i < n} r^i ≤ (1 - r)⁻¹` for `0 ≤ r < 1` over `ℝ`.

* `sum_rpow_neg_factoredNumbers_le` (finite Euler product bound):
  for a finset `s` of primes and `σ > 0`,
  `∑_{n ≤ x, n s-factored} n^{-σ} ≤ ∏_{q ∈ s} (1 - q^{-σ})⁻¹`,
  proved by induction on `s` via `n ↦ q^{v_q(n)} · (n / q^{v_q(n)})`.

* `smoothCount_rpow_le` (**Rankin's trick**): for `σ > 0`,
  `#{n ≤ x : largestPrimeFactor n ≤ p} ≤ x^σ · ∏_{q ∈ primesLE p} (1 - q^{-σ})⁻¹`.
  Every summand is `≥ 1` after multiplying by `(x/n)^σ`, and the resulting
  `∑ n^{-σ}` over smooth numbers is bounded by the Euler product.

No placeholders; kernel-checkable.
-/

namespace JSP314

open Finset

namespace SieveBase

/-- Finite geometric series bound: for `0 ≤ r < 1`,
`∑_{i < n} r^i ≤ (1 - r)⁻¹`. -/
theorem geom_sum_le_one_sub_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, r ^ i ≤ (1 - r)⁻¹ := by
  rw [Finset.range_eq_Ico]
  refine (geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hr0 hr1).trans ?_
  rw [pow_zero, one_div]

/-- **Finite Euler-product bound.** For a finset `s` consisting of primes and
`σ > 0`, the sum of `n^{-σ}` over `s`-factored `n ∈ [1, x]` is at most
`∏_{q ∈ s} (1 - q^{-σ})⁻¹`. -/
theorem sum_rpow_neg_factoredNumbers_le {σ : ℝ} (hσ : 0 < σ) (x : ℕ) :
    ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) →
      ∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s), (n : ℝ) ^ (-σ)
        ≤ ∏ q ∈ s, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _
      rw [Finset.prod_empty]
      have hF : (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers ∅) ⊆ {1} := by
        intro n hn
        rw [Finset.mem_filter, Nat.factoredNumbers_empty] at hn
        exact Finset.mem_singleton.mpr hn.2
      refine (Finset.sum_le_sum_of_subset_of_nonneg hF fun i _ _ =>
        Real.rpow_nonneg (Nat.cast_nonneg i) _).trans ?_
      rw [Finset.sum_singleton]
      simp
  | @insert q s hqnot ih =>
      intro hprimes
      have hqprime : q.Prime := hprimes q (Finset.mem_insert_self q s)
      have hs' : ∀ r ∈ s, r.Prime := fun r hr => hprimes r (Finset.mem_insert_of_mem hr)
      -- Every `insert q s`-factored `n` is uniquely `q^e * m` with `m`
      -- `s`-factored; this gives a subset of the image of
      -- `range (x+1) ×ˢ B` under `(e, m) ↦ q^e * m`.
      have hsub : (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers (insert q s)) ⊆
          (Finset.range (x + 1) ×ˢ
            (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s)).image
            (fun em : ℕ × ℕ => q ^ em.1 * em.2) := by
        intro n hn
        obtain ⟨hnIcc, hnfac⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hnIcc
        have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_factoredNumbers hnfac
        refine Finset.mem_image.mpr
          ⟨⟨n.factorization q, ordCompl[q] n⟩, ?_, ?_⟩
        · rw [Finset.mem_product]
          constructor
          · rw [Finset.mem_range]
            have hdvd : q ^ n.factorization q ∣ n := Nat.ordProj_dvd n q
            have hle : q ^ n.factorization q ≤ n :=
              Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
            have hlt : n.factorization q < q ^ n.factorization q :=
              (n.factorization q).lt_pow_self hqprime.one_lt
            omega
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_Icc.mpr
              ⟨Nat.ordCompl_pos q hn0, (Nat.ordCompl_le n q).trans hnx⟩, ?_⟩
            rw [Nat.mem_factoredNumbers]
            refine ⟨(Nat.ordCompl_pos q hn0).ne', fun r hr => ?_⟩
            rw [Nat.mem_primeFactorsList'] at hr
            have hrn : r ∣ n := hr.2.1.trans (Nat.ordCompl_dvd n q)
            have hrs : r ∈ insert q s :=
              hnfac.2 r ((Nat.mem_primeFactorsList hn0).mpr ⟨hr.1, hrn⟩)
            rcases Finset.mem_insert.mp hrs with rfl | h
            · exact absurd hr.2.1 (Nat.not_dvd_ordCompl hqprime hn0)
            · exact h
        · exact Nat.ordProj_mul_ordCompl_eq_self n q
      -- The map `(e, m) ↦ q^e * m` is injective on `range (x+1) ×ˢ B`:
      -- `e` is recovered as the `q`-adic valuation since `q ∤ m`.
      have hinj : ∀ a ∈ Finset.range (x + 1) ×ˢ
              (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s),
          ∀ b ∈ Finset.range (x + 1) ×ˢ
              (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s),
          (fun em : ℕ × ℕ => q ^ em.1 * em.2) a =
            (fun em : ℕ × ℕ => q ^ em.1 * em.2) b → a = b := by
        rintro ⟨e₁, m₁⟩ h₁ ⟨e₂, m₂⟩ h₂ hEq
        dsimp only at hEq
        rw [Finset.mem_product] at h₁ h₂
        have hm1 : m₁ ∈ Nat.factoredNumbers s := (Finset.mem_filter.mp h₁.2).2
        have hm2 : m₂ ∈ Nat.factoredNumbers s := (Finset.mem_filter.mp h₂.2).2
        have hqnm : ∀ {m : ℕ}, m ∈ Nat.factoredNumbers s → ¬ q ∣ m := by
          intro m hm hd
          have hqm : q ∈ m.primeFactorsList :=
            (Nat.mem_primeFactorsList (Nat.ne_zero_of_mem_factoredNumbers hm)).mpr
              ⟨hqprime, hd⟩
          exact hqnot ((Nat.mem_factoredNumbers.mp hm).2 q hqm)
        have key : ∀ {e m : ℕ}, m ∈ Nat.factoredNumbers s →
            (q ^ e * m).factorization q = e := by
          intro e m hm
          rw [Nat.factorization_mul (pow_ne_zero _ hqprime.ne_zero)
              (Nat.ne_zero_of_mem_factoredNumbers hm),
            Finsupp.add_apply, Nat.factorization_pow_self hqprime,
            Nat.factorization_eq_zero_of_not_dvd (hqnm hm), add_zero]
        have hee : e₁ = e₂ := by
          have h1 := key (e := e₁) hm1
          have h2 := key (e := e₂) hm2
          rw [hEq] at h1
          rw [← h1, h2]
        have hEq' := hEq
        rw [← hee] at hEq'
        have hmm : m₁ = m₂ := Nat.mul_left_cancel (pow_pos hqprime.pos _) hEq'
        exact Prod.ext hee hmm
      -- `(q^e * m)^{-σ} = (q^{-σ})^e * m^{-σ}`.
      have hterm : ∀ e m : ℕ,
          ((q ^ e * m : ℕ) : ℝ) ^ (-σ) = ((q : ℝ) ^ (-σ)) ^ e * (m : ℝ) ^ (-σ) := by
        intro e m
        rw [Nat.cast_mul, Nat.cast_pow,
          Real.mul_rpow (show (0 : ℝ) ≤ (q : ℝ) ^ e by positivity)
            (Nat.cast_nonneg m)]
        congr 1
        rw [← Real.rpow_natCast (q : ℝ) e, ← Real.rpow_mul (Nat.cast_nonneg q),
          mul_comm (e : ℝ) (-σ), Real.rpow_mul (Nat.cast_nonneg q), Real.rpow_natCast]
      have hr : (q : ℝ) ^ (-σ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast hqprime.one_lt) (neg_lt_zero.mpr hσ)
      have hr0 : (0 : ℝ) ≤ (q : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg q) _
      have hgeom : ∑ e ∈ Finset.range (x + 1), ((q : ℝ) ^ (-σ)) ^ e ≤
          (1 - (q : ℝ) ^ (-σ))⁻¹ := geom_sum_le_one_sub_inv hr0 hr _
      have hSB := ih hs'
      have hSBpos : (0 : ℝ) ≤
          ∑ m ∈ (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s), (m : ℝ) ^ (-σ) :=
        Finset.sum_nonneg fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _
      have hinv : (0 : ℝ) ≤ (1 - (q : ℝ) ^ (-σ))⁻¹ :=
        inv_nonneg.mpr (sub_pos.mpr hr).le
      calc ∑ n ∈ (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers (insert q s)),
              (n : ℝ) ^ (-σ)
          ≤ ∑ em ∈ Finset.range (x + 1) ×ˢ
                (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s),
              ((q : ℝ) ^ (-σ)) ^ em.1 * (em.2 : ℝ) ^ (-σ) := by
            refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
              Real.rpow_nonneg (Nat.cast_nonneg i) _).trans ?_
            rw [Finset.sum_image hinj]
            exact Finset.sum_le_sum fun ⟨e, m⟩ _ => (hterm e m).le
        _ = (∑ e ∈ Finset.range (x + 1), ((q : ℝ) ^ (-σ)) ^ e) *
              ∑ m ∈ (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers s),
                (m : ℝ) ^ (-σ) := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
        _ ≤ (1 - (q : ℝ) ^ (-σ))⁻¹ * ∏ r ∈ s, (1 - (r : ℝ) ^ (-σ))⁻¹ :=
            mul_le_mul hgeom hSB hSBpos hinv
        _ = ∏ r ∈ insert q s, (1 - (r : ℝ) ^ (-σ))⁻¹ := by
            rw [Finset.prod_insert hqnot]

/-- Numbers in `[1, x]` whose largest prime factor is `≤ p` are `(p + 1)`-smooth. -/
theorem mem_smoothNumbers_of_largestPrimeFactor_le {x p n : ℕ}
    (hn : n ∈ (Finset.Icc 1 x).filter (fun n => largestPrimeFactor n ≤ p)) :
    n ∈ Nat.smoothNumbers (p + 1) := by
  obtain ⟨hnIcc, hlpf⟩ := Finset.mem_filter.mp hn
  have hn1 := (Finset.mem_Icc.mp hnIcc).1
  rw [Nat.mem_smoothNumbers']
  intro q hq hqd
  rcases eq_or_lt_of_le hn1 with h | h2
  · subst h
    exact absurd hqd hq.not_dvd_one
  · have := prime_dvd_le_largestPrimeFactor h2 hq hqd
    omega

/-- `(p + 1)`-smooth numbers up to `x` are exactly the `primesLE p`-factored
numbers in `[1, x]`. -/
theorem smoothNumbersUpTo_succ_eq_filter (x p : ℕ) :
    Nat.smoothNumbersUpTo x (p + 1) =
      (Finset.Icc 1 x).filter (· ∈ Nat.factoredNumbers (Nat.primesLE p)) := by
  ext n
  rw [Nat.mem_smoothNumbersUpTo, Finset.mem_filter, Finset.mem_Icc,
    Nat.smoothNumbers_eq_factoredNumbers_primesBelow]
  constructor
  · rintro ⟨hx, hfac⟩
    exact ⟨⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_factoredNumbers hfac), hx⟩, hfac⟩
  · rintro ⟨⟨_, hx⟩, hfac⟩
    exact ⟨hx, hfac⟩

/-- **Rankin's trick**: for `σ > 0`, the number of `n ∈ [1, x]` with
`largestPrimeFactor n ≤ p` is at most
`x^σ · ∏_{q ≤ p prime} (1 - q^{-σ})⁻¹`. -/
theorem smoothCount_rpow_le (x p : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (((Finset.Icc 1 x).filter fun n => largestPrimeFactor n ≤ p).card : ℝ) ≤
      (x : ℝ) ^ σ * ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
  classical
  set S := (Finset.Icc 1 x).filter fun n => largestPrimeFactor n ≤ p with hS
  have hterm : ∀ n ∈ S, (1 : ℝ) ≤ (x : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
    intro n hn
    obtain ⟨h1, hx⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
    have hnsx : (n : ℝ) ^ σ ≤ (x : ℝ) ^ σ :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hx) hσ.le
    have hnpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hn0 σ
    calc (1 : ℝ) = (n : ℝ) ^ σ * ((n : ℝ) ^ σ)⁻¹ := (mul_inv_cancel₀ hnpos.ne').symm
      _ ≤ (x : ℝ) ^ σ * ((n : ℝ) ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right hnsx (inv_nonneg.mpr hnpos.le)
      _ = (x : ℝ) ^ σ * (n : ℝ) ^ (-σ) := by
          rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hcard : (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := by
    rw [Finset.card_eq_sum_ones]
    push_cast
    rfl
  have hsub : S ⊆ Nat.smoothNumbersUpTo x (p + 1) := by
    intro n hn
    exact Nat.mem_smoothNumbersUpTo.mpr
      ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2,
        mem_smoothNumbers_of_largestPrimeFactor_le hn⟩
  calc (S.card : ℝ) = ∑ _n ∈ S, (1 : ℝ) := hcard
    _ ≤ ∑ n ∈ S, (x : ℝ) ^ σ * (n : ℝ) ^ (-σ) := Finset.sum_le_sum hterm
    _ = (x : ℝ) ^ σ * ∑ n ∈ S, (n : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ (x : ℝ) ^ σ *
          ∑ n ∈ Nat.smoothNumbersUpTo x (p + 1), (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
            Real.rpow_nonneg (Nat.cast_nonneg i) _)
          (Real.rpow_nonneg (Nat.cast_nonneg x) σ)
    _ = (x : ℝ) ^ σ * ∑ n ∈ (Finset.Icc 1 x).filter
          (· ∈ Nat.factoredNumbers (Nat.primesLE p)), (n : ℝ) ^ (-σ) := by
        rw [smoothNumbersUpTo_succ_eq_filter]
    _ ≤ (x : ℝ) ^ σ * ∏ q ∈ Nat.primesLE p, (1 - (q : ℝ) ^ (-σ))⁻¹ :=
        mul_le_mul_of_nonneg_left
          (sum_rpow_neg_factoredNumbers_le hσ x _ fun q hq =>
            Nat.prime_of_mem_primesLE hq)
          (Real.rpow_nonneg (Nat.cast_nonneg x) σ)

end SieveBase

end JSP314
