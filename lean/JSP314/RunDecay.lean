import JSP314.RunSieve
import JSP314.BrunSieve
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# JSP-000314 — sieve decay of run counts

This file attacks the quantitative decay of `rightRunCount x p k` /
`leftRunCount x p k` (the summands of `BandSum.runCountSum`, whose
`S(x)·(log x)^{-1+o(1)}` bound is the last remaining hypothesis for
`badNonSingleton_interval_bound`).

## What is proved

* `runSiftedRight_eq_siftedSet` — the `RunSieve` sifted set *is*
  `JointSieve.siftedSet`, so `rightRunCount ≤ #siftedSet (2x/p²) p k w`.
* `rightRunCount_le_brun`, `rightRunCount_le_brun_subset_exp` — the Brun
  upper-bound sieve applied to the run counts: for any sieve prime set
  `T ⊆ (p, w]`, any truncation `t` and Rankin parameter `z ≥ 1`,

    `rightRunCount x p k ≤ y·∏_{q∈T}(1 - min k q/q)
      + y·exp(z·k·∑_{q∈T} q⁻¹)/z^{2t} + (1 + #T·k)^{2t}`, `y = 2x/p²`.

* `runSiftedLeft_card_le_siftedOver_add`, `leftRunCount_le_brun` — the left
  runs are handled by the **reflection** `r ↦ M·P - r` (with
  `P = ∏_{q∈T} q`): `p²·r - j ≡ 0 (mod q)` iff `p²·(−r) + j ≡ 0`, so modulo
  every sieve prime the reflected element is right-sifted.  The `r` with
  `p²r ≤ k` (where the truncated subtraction is vacuous) contribute `≤ k`.

* `prod_one_sub_min_le_exp` — the main-term bound
  `∏_{q∈T}(1 - min k q/q) ≤ exp(-k·∑_{q∈T, k<q} q⁻¹)`.

No placeholders; kernel-checkable.
-/

namespace JSP314

open Finset
open scoped Nat.Prime

section Embeddings

/-- The `RunSieve` right sifted set is literally `JointSieve.siftedSet`. -/
theorem runSiftedRight_eq_siftedSet (y p k w : ℕ) :
    runSiftedRight y p k w = siftedSet y p k w := by
  ext r
  simp only [runSiftedRight, siftedSet, Finset.mem_filter]

/-- `rightRunCount x p k ≤ #siftedSet (2x/p²) p k w` for every cutoff `w`. -/
theorem rightRunCount_le_siftedSet {x p k w : ℕ} (hp : p.Prime) :
    rightRunCount x p k ≤ (siftedSet (2 * x / p ^ 2) p k w).card := by
  rw [← runSiftedRight_eq_siftedSet]
  exact rightRunCount_le_runSiftedRight hp

end Embeddings

section BrunApplication

/-- **Brun bound on the right run count**: direct application of
`siftedSet_card_le_brun` to `rightRunCount ≤ #siftedSet`. -/
theorem rightRunCount_le_brun {p : ℕ} (hp : p.Prime) (x k w t : ℕ) :
    (rightRunCount x p k : ℝ) ≤
      ((2 * x / p ^ 2 : ℕ) : ℝ) * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime,
          (1 - ((min k q : ℕ) : ℝ) / q)
        + ((2 * x / p ^ 2 : ℕ) : ℝ) *
            ∑ s ∈ ((Finset.Ioc p w).filter Nat.Prime).powerset
              with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
        + (1 + ((Finset.Ioc p w).filter Nat.Prime).card * k : ℝ) ^ (2 * t) := by
  refine (Nat.cast_le.mpr
    (rightRunCount_le_siftedSet (w := w) hp)).trans ?_
  exact siftedSet_card_le_brun hp _ k w t

/-- **Brun bound, restricted prime set + exponential tail** applied to
`rightRunCount`. -/
theorem rightRunCount_le_brun_subset_exp {p : ℕ} (hp : p.Prime) (x k w t : ℕ)
    (T : Finset ℕ) (hT : T ⊆ (Finset.Ioc p w).filter Nat.Prime) {z : ℝ}
    (hz : 1 ≤ z) :
    (rightRunCount x p k : ℝ) ≤
      ((2 * x / p ^ 2 : ℕ) : ℝ) * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
        + ((2 * x / p ^ 2 : ℕ) : ℝ) *
            Real.exp (z * k * ∑ q ∈ T, (q : ℝ)⁻¹) / z ^ (2 * t)
        + (1 + T.card * k : ℝ) ^ (2 * t) := by
  refine (Nat.cast_le.mpr
    (rightRunCount_le_siftedSet (w := w) hp)).trans ?_
  exact siftedSet_card_le_brun_subset_exp hp _ k w t T hT hz

end BrunApplication

section LeftReflection

/-- For `q ∣ M` and `j ≤ p²r`, `q ∣ p²·(M - r) + j ↔ q ∣ p²·r - j` — the
reflection `r ↦ M - r` turns left-sifted conditions into right-sifted ones
modulo every `q ∣ M`. -/
theorem dvd_sq_mul_sub_iff {p q M r j : ℕ} (hqM : q ∣ M) (hr : r ≤ M)
    (hj : j ≤ p ^ 2 * r) :
    q ∣ p ^ 2 * (M - r) + j ↔ q ∣ p ^ 2 * r - j := by
  have hM : (M : ZMod q) = 0 := ZMod.natCast_eq_zero_iff.mpr hqM
  have hMr : ((M - r : ℕ) : ZMod q) = (M : ZMod q) - r := Nat.cast_sub hr
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hMr, hM, zero_sub,
    Nat.cast_sub hj, Nat.cast_mul, Nat.cast_pow, mul_neg, neg_add_eq_zero,
    sub_eq_zero]

/-- **Reflection bound for the left sifted set.**  With `T` the primes of
`(p, w]` and `P = ∏_{q∈T} q`, `M = (y/P + 1)·P` (`≤ y + P`), the map
`r ↦ M - r` sends left-sifted `r` with `k < p²r` to right-sifted `s ∈
[1, M]`, and the remaining `r` satisfy `r ≤ k`. -/
theorem runSiftedLeft_card_le_siftedOver_add (y p k w : ℕ) :
    (runSiftedLeft y p k w).card ≤
      (siftedOver ((y / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
          * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q) p k
        ((Finset.Ioc p w).filter Nat.Prime)).card + k := by
  classical
  set T := (Finset.Ioc p w).filter Nat.Prime with hT
  set P := ∏ q ∈ T, q with hP
  set M := (y / P + 1) * P with hM
  have hP0 : 0 < P := Finset.prod_pos fun q hq =>
    (Finset.mem_filter.mp hq).2.pos
  -- `M > y` since `y % P < P`.
  have hyM : y < M := by
    have h1 : y = (y / P) * P + y % P := (Nat.div_add_mod y P).symm
    have h2 : y % P < P := Nat.mod_lt y hP0
    omega
  -- split `runSiftedLeft` into `k < p²r` (reflected) and `p²r ≤ k`
  -- (exceptional, `≤ k` of them).
  have hsplit := Finset.card_filter_add_card_filter_not
    (p := fun r => k < p ^ 2 * r) (s := runSiftedLeft y p k w)
  have hex : ((runSiftedLeft y p k w).filter (fun r => ¬ k < p ^ 2 * r)).card
      ≤ k := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · -- `p = 0`: bound by `y ≤ M ≤ M + k`.
      refine le_trans ?_ (Nat.le_add_right _ _)
      have hsub : (runSiftedLeft y 0 k w).filter (fun r => ¬ k < 0 ^ 2 * r)
          ⊆ Finset.Icc 1 y := Finset.filter_subset _ _ |>.trans
        (Finset.filter_subset _ _)
      exact (Finset.card_le_card hsub).trans (by
        rw [Nat.card_Icc]; omega)
    · have hsub : (runSiftedLeft y p k w).filter (fun r => ¬ k < p ^ 2 * r)
          ⊆ Finset.Icc 1 k := by
        intro r hr
        rw [Finset.mem_filter, mem_runSiftedLeft] at hr
        rw [Finset.mem_Icc] at hr ⊢
        have : r ≤ k := le_trans (Nat.le_mul_of_pos_left r hp0)
          (by omega : p ^ 2 * r ≤ k)
        exact ⟨by omega, this⟩
      exact (Finset.card_le_card hsub).trans (by rw [Nat.card_Icc])
  have hmain : ((runSiftedLeft y p k w).filter (fun r => k < p ^ 2 * r)).card
      ≤ (siftedOver M p k T).card := by
    apply Finset.card_le_card_of_injOn (fun r => M - r)
    · intro r hr
      rw [Finset.mem_coe, Finset.mem_filter] at hr
      obtain ⟨hrm, hkr⟩ := hr
      rw [mem_runSiftedLeft] at hrm
      obtain ⟨hr1, hcond⟩ := Finset.mem_Icc.mp hrm.1, hrm.2
      rw [siftedOver, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩, ?_⟩
      intro q hq j hj
      have hqP : q ∣ P := Finset.dvd_prod_of_mem _ hq
      have hqM : q ∣ M := hqP.trans (dvd_mul_left _ _)
      have hjr : j ≤ p ^ 2 * r := by
        have := (Finset.mem_Icc.mp hj).2
        omega
      rw [dvd_sq_mul_sub_iff hqM (le_trans hrm.1.2 hyM.le) hjr]
      exact hrm.2 q hq j hj (by omega)
    · intro a ha b hb hab
      have haM : a ≤ M := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1
        rw [mem_runSiftedLeft] at this
        exact le_trans (Finset.mem_Icc.mp this.1).2 hyM.le
      have hbM : b ≤ M := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
        rw [mem_runSiftedLeft] at this
        exact le_trans (Finset.mem_Icc.mp this.1).2 hyM.le
      exact (tsub_right_inj haM hbM).mp hab
  omega

/-- **Brun bound on the left run count**: the reflection embedding plus
`siftedOver_card_le_brun`, with `M = (y/P + 1)·P ≤ y + P`. -/
theorem leftRunCount_le_brun {p : ℕ} (hp : p.Prime) (x k w t : ℕ) :
    (leftRunCount x p k : ℝ) ≤
      ((((2 * x / p ^ 2)
            / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
          * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q : ℕ) : ℝ) *
          ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime,
            (1 - ((min k q : ℕ) : ℝ) / q)
        + ((((2 * x / p ^ 2)
              / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
            * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q : ℕ) : ℝ) *
            ∑ s ∈ ((Finset.Ioc p w).filter Nat.Prime).powerset
              with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
        + (1 + ((Finset.Ioc p w).filter Nat.Prime).card * k : ℝ) ^ (2 * t)
        + k := by
  have hle := (leftRunCount_le_runSiftedLeft hp).trans
    (runSiftedLeft_card_le_siftedOver_add (2 * x / p ^ 2) p k w)
  have hbrun := siftedOver_card_le_brun hp
    ((2 * x / p ^ 2 / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
      * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q) k t
    ((Finset.Ioc p w).filter Nat.Prime)
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1)
  have hcast : (leftRunCount x p k : ℝ)
      ≤ ((siftedOver ((2 * x / p ^ 2
              / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
            * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q) p k
          ((Finset.Ioc p w).filter Nat.Prime)).card : ℝ) + k := by
    exact_mod_cast hle
  linarith [hbrun]

end LeftReflection

section ProductBound

/-- The `min k q` main term is bounded by the `exp(-k·∑ q⁻¹)` exponential:
factors with `q ≤ k` are `0` (or `1` at `q = 0`), factors with `k < q` are
`1 - k/q ≤ e^{-k/q}`. -/
theorem prod_one_sub_min_le_exp (k : ℕ) (T : Finset ℕ) :
    ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
      ≤ Real.exp (-(k : ℝ) * ∑ q ∈ T.filter (fun q => k < q), (q : ℝ)⁻¹) := by
  classical
  set S := T.filter (fun q => k < q) with hS
  -- split `T` into `k < q` and `q ≤ k` parts
  have hsplit : ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
      = (∏ q ∈ S, (1 - ((min k q : ℕ) : ℝ) / q))
        * ∏ q ∈ T.filter (fun q => ¬ k < q), (1 - ((min k q : ℕ) : ℝ) / q) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  -- each factor lies in `[0, 1]`
  have h01 : ∀ q : ℕ, (0:ℝ) ≤ 1 - ((min k q : ℕ) : ℝ) / q
      ∧ 1 - ((min k q : ℕ) : ℝ) / q ≤ 1 := by
    intro q
    have hnn : (0:ℝ) ≤ ((min k q : ℕ) : ℝ) / q := div_nonneg
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hle : ((min k q : ℕ) : ℝ) / q ≤ 1 := by
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · rw [div_le_one (Nat.cast_pos.mpr hq)]
        exact Nat.cast_le.mpr (min_le_right k q)
    exact ⟨sub_nonneg.mpr hle, sub_le_self 1 hnn⟩
  have hprodS : ∏ q ∈ S, (1 - ((min k q : ℕ) : ℝ) / q)
      = ∏ q ∈ S, (1 - (k : ℝ) / q) := by
    apply Finset.prod_congr rfl
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    rw [min_eq_left hq.2.le]
  have hrest : ∏ q ∈ T.filter (fun q => ¬ k < q), (1 - ((min k q : ℕ) : ℝ) / q)
      ≤ 1 :=
    Finset.prod_le_one₀ (fun q _ => (h01 q).1) (fun q _ => (h01 q).2)
  have hmain : ∏ q ∈ S, (1 - (k : ℝ) / q)
      ≤ Real.exp (-(k : ℝ) * ∑ q ∈ S, (q : ℝ)⁻¹) := by
    have hterm : ∀ q ∈ S, (1 - (k : ℝ) / q)
        ≤ Real.exp (-(k : ℝ) * (q : ℝ)⁻¹) := by
      intro q hq
      rw [hS, Finset.mem_filter] at hq
      have hneg : -(k : ℝ) / q = -(k : ℝ) * (q : ℝ)⁻¹ := by
        rw [neg_div, mul_inv]
      calc (1 - (k : ℝ) / q)
          = 1 + -(k : ℝ) * (q : ℝ)⁻¹ := by rw [hneg]; ring
        _ ≤ Real.exp (-(k : ℝ) * (q : ℝ)⁻¹) :=
            Real.add_one_le_exp _
    have hnn : ∀ q ∈ S, (0:ℝ) ≤ 1 - (k : ℝ) / q := by
      intro q hq
      rw [hS, Finset.mem_filter] at hq
      have hq1 : (0:ℝ) < q := Nat.cast_pos.mpr (by omega)
      rw [sub_nonneg, div_le_one hq1]
      exact Nat.cast_le.mpr hq.2.le
    calc ∏ q ∈ S, (1 - (k : ℝ) / q)
        ≤ ∏ q ∈ S, Real.exp (-(k : ℝ) * (q : ℝ)⁻¹) :=
          Finset.prod_le_prod hnn hterm
      _ = Real.exp (∑ q ∈ S, -(k : ℝ) * (q : ℝ)⁻¹) := by
          rw [← Real.exp_sum]
      _ = Real.exp (-(k : ℝ) * ∑ q ∈ S, (q : ℝ)⁻¹) := by
          rw [← Finset.sum_neg_distrib]
          simp [Finset.mul_sum, mul_comm]
  rw [hsplit, hprodS]
  calc (∏ q ∈ S, (1 - (k : ℝ) / q))
        * ∏ q ∈ T.filter (fun q => ¬ k < q), (1 - ((min k q : ℕ) : ℝ) / q)
      ≤ (∏ q ∈ S, (1 - (k : ℝ) / q)) * 1 :=
        mul_le_mul_of_nonneg_left hrest
          (Finset.prod_nonneg fun q _ => hnn q _)
    _ = ∏ q ∈ S, (1 - (k : ℝ) / q) := mul_one _
    _ ≤ Real.exp (-(k : ℝ) * ∑ q ∈ S, (q : ℝ)⁻¹) := hmain

end ProductBound

end JSP314
