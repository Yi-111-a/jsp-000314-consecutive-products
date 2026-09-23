import JSP314.PairSmooth
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# JSP-000314 — the squarefree-kernel (Pell) parametrization of smooth pairs

If `j, j + 1` are both `(p + 1)`-smooth, Mathlib's kernel decomposition
`Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers` writes

    j     = s^2 · a,     j + 1 = t^2 · a'

with `a, a'` products of *distinct* primes `< p + 1` (hence divisors of the
primorial `p#`, and coprime since `j, j + 1` are coprime).  The pair therefore
solves the generalized Pell equation

    a'·t² − a·s² = 1.

## What is proved

* `consecSmoothPair_exists_kernel` — the kernel decomposition of a
  consecutive `p`-smooth pair `n, n + 1` (for `1 ≤ n`), including
  `a, a' ∣ ∏_{q ≤ p} q` and `Nat.Coprime a a'`;
* `pell_consec_growth` — **the elementary Pell growth lemma**: two solutions
  `(s, t) < (s', t')` of `a'·t² = a·s² + 1` satisfy `2t ≤ t'`.
  The proof is the classical descent done purely in `ℤ`: the putative ratio
  `u + v√D` (with `u = a'tt' − ss'a`, `v = ts' − t's`) is a norm-1 unit
  (`u² − aa'v² = 1`), `v = 0` forces `t' = t`, `v ≥ 1` gives `t' = ut + asv`,
  and `v ≤ −1` contradicts `ts = t's' + (−v)(a'tt' + ass') > ts`;
* `pellSolFinset_card_le_log` — the solution count
  `#{t ≤ T : ∃ s, a'·t² = a·s² + 1} ≤ Nat.log 2 T + 1`, via strict
  monotonicity of `Nat.log 2` on the solution set;
* `consecSmoothPairCount_le_kernel_mul_log` — **the headline bound**:
  `consecSmoothPairCount x p ≤ 1 + 4^{π'(p+1)}·(Nat.log 2 (x+1) + 1)`,
  where `π'(k) = (Nat.primesBelow k).card`.  For `p = O(log x)` this is
  `x^{o(1)}` — power-saving on the small-prime slice;
* `consecSmoothPairCount_le_kernel_mul_sqrt` — the coarser
  `≤ 1 + 4^{π'(p+1)}·(√(x+1) + 1)` bound (deliverable form);
* `consecSmoothPair_le_one` / `consecSmoothPairCount_two` — for `p = 2`
  the only pair beginnings are `n ∈ {0, 1}` (two naturals both powers of
  `2` differ by `1` only for `1, 2`), giving `consecSmoothPairCount x 2 ≤ 2`
  and the exact value `min x 1 + 1`.

The counting argument is injection-free: the pair beginnings `≤ x` lie in
the image of the kernel-solution sigma type `pairKernelSigma` under
`((k₁, k₂), t) ↦ k₂.prod · t² − 1`, plus possibly `0`.
-/

namespace JSP314

open Classical

section KernelDecomposition

/-- **Squarefree-kernel decomposition of a consecutive smooth pair.**
If `n, n + 1` are both `p`-smooth (with `1 ≤ n`), then
`n = m₁²·a` and `n + 1 = m₂²·a'` where `a, a'` are products of distinct
primes `< p + 1` — hence both divide `∏_{q ≤ p} q` (the primorial `p#`) —
and `Nat.Coprime a a'`. -/
theorem consecSmoothPair_exists_kernel {n p : ℕ} (hn : 1 ≤ n)
    (h : consecSmoothPair n p) :
    ∃ s₁ s₂ : Finset ℕ, ∃ m₁ m₂ : ℕ,
      s₁ ⊆ Nat.primesBelow (p + 1) ∧ s₂ ⊆ Nat.primesBelow (p + 1) ∧
        s₁.prod id ∣ (Nat.primesBelow (p + 1)).prod id ∧
        s₂.prod id ∣ (Nat.primesBelow (p + 1)).prod id ∧
        n = m₁ ^ 2 * s₁.prod id ∧ n + 1 = m₂ ^ 2 * s₂.prod id ∧
        Nat.Coprime (s₁.prod id) (s₂.prod id) := by
  obtain ⟨h1, h2⟩ := h
  have hmem1 : n ∈ Nat.smoothNumbers (p + 1) := mem_smoothNumbers_of_lpf_le hn h1
  have hmem2 : n + 1 ∈ Nat.smoothNumbers (p + 1) :=
    mem_smoothNumbers_of_lpf_le (by omega) h2
  obtain ⟨s₁, hs₁, m₁, hm₁⟩ := Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers hmem1
  obtain ⟨s₂, hs₂, m₂, hm₂⟩ := Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers hmem2
  rw [Finset.mem_powerset] at hs₁ hs₂
  refine ⟨s₁, s₂, m₁, m₂, hs₁, hs₂,
    Finset.prod_dvd_prod_of_subset _ _ _ hs₁,
    Finset.prod_dvd_prod_of_subset _ _ _ hs₂, hm₁, hm₂, ?_⟩
  have hcop : Nat.Coprime n (n + 1) :=
    (Nat.coprime_self_add_right (m := n) (n := 1)).mpr (Nat.coprime_one_right n)
  have hd1 : s₁.prod id ∣ n := by
    rw [hm₁]
    exact dvd_mul_left _ _
  have hd2 : s₂.prod id ∣ n + 1 := by
    rw [hm₂]
    exact dvd_mul_left _ _
  exact Nat.Coprime.of_dvd_right hd2 (Nat.Coprime.of_dvd_left hd1 hcop)

end KernelDecomposition

section PellGrowth

/-- **Pell growth lemma.**  If `(s, t)` and `(s', t')` are solutions of the
generalized Pell equation `a'·t² − a·s² = 1` in naturals with `t < t'` and
`a, a' ≥ 1`, then `t' ≥ 2t`.  The proof is pure `ℤ` arithmetic: with
`u = a'tt' − ass'` and `v = ts' − t's` one checks `u ≥ 1`,
`u² − aa'v² = 1`, `t' = ut + asv`, `s' = us + a'tv`; then `v = 0` forces
`u = 1` and `t' = t`, `v ≥ 1` gives `t' ≥ 2t + 1`, and `v ≤ −1` yields
`ts = t's' + (−v)(a'tt' + ass') ≥ ts + 2`, a contradiction. -/
theorem pell_consec_growth {a a' s t s' t' : ℕ} (ha : 1 ≤ a) (ha' : 1 ≤ a')
    (h : a' * t ^ 2 = a * s ^ 2 + 1) (h' : a' * t' ^ 2 = a * s' ^ 2 + 1)
    (hlt : t < t') : 2 * t ≤ t' := by
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · exfalso
      subst h0
      simp at h
    · exact h0
  have hs' : 1 ≤ s' := by
    rcases Nat.eq_zero_or_pos s' with h0 | h0
    · exfalso
      subst h0
      have h'' : a' * t' ^ 2 = 1 := by simpa using h'
      have ht'2 : 2 ≤ t' := by omega
      have h4 : (4 : ℕ) ≤ a' * t' ^ 2 := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ t' ^ 2 := Nat.pow_le_pow_left ht'2 _
          _ = 1 * t' ^ 2 := (one_mul _).symm
          _ ≤ a' * t' ^ 2 := Nat.mul_le_mul ha' (le_refl _)
      omega
    · exact h0
  rcases Nat.eq_zero_or_pos s with hs0 | hs
  · -- `s = 0` forces `a' * t^2 = 1`, so `t = 1`, and `t' ≥ 2 = 2t`.
    subst hs0
    have h'' : a' * t ^ 2 = 1 := by simpa using h
    have ht_le : t ≤ 1 := by
      by_contra hc
      push Not at hc
      have h4 : (4 : ℕ) ≤ a' * t ^ 2 := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ t ^ 2 := Nat.pow_le_pow_left hc _
          _ = 1 * t ^ 2 := (one_mul _).symm
          _ ≤ a' * t ^ 2 := Nat.mul_le_mul ha' (le_refl _)
      omega
    omega
  · -- `s ≥ 1`: the ℤ computation.
    have hss' : s < s' := by
      have hlt2 : t ^ 2 < t' ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
      have h1 : a' * t ^ 2 < a' * t' ^ 2 :=
        mul_lt_mul_of_pos_left hlt2 (by omega)
      have h2 : a * s ^ 2 < a * s' ^ 2 := by omega
      have h3 : s ^ 2 < s' ^ 2 := by
        by_contra hc
        push Not at hc
        have h4 := Nat.mul_le_mul (le_refl a) hc
        omega
      by_contra hc
      push Not at hc
      have h5 := Nat.pow_le_pow_left hc 2
      omega
    -- Integer data.
    have h1z : (a' : ℤ) * (t : ℤ) ^ 2 - (a : ℤ) * (s : ℤ) ^ 2 = 1 := by
      have hz : (a' : ℤ) * (t : ℤ) ^ 2 = (a : ℤ) * (s : ℤ) ^ 2 + 1 := by
        exact_mod_cast h
      linarith
    have h2z : (a' : ℤ) * (t' : ℤ) ^ 2 - (a : ℤ) * (s' : ℤ) ^ 2 = 1 := by
      have hz : (a' : ℤ) * (t' : ℤ) ^ 2 = (a : ℤ) * (s' : ℤ) ^ 2 + 1 := by
        exact_mod_cast h'
      linarith
    have hU2 : ((a' : ℤ) * t * t' - (a : ℤ) * s * s') ^ 2 =
        (a : ℤ) * a' * ((t : ℤ) * s' - t' * s) ^ 2 + 1 := by
      linear_combination ((a' : ℤ) * (t' : ℤ) ^ 2 - (a : ℤ) * (s' : ℤ) ^ 2) * h1z
        + h2z
    have hte : (t' : ℤ) = ((a' : ℤ) * t * t' - (a : ℤ) * s * s') * t
        + (a : ℤ) * s * ((t : ℤ) * s' - t' * s) := by
      linear_combination (-(t' : ℤ)) * h1z
    have hse : (s' : ℤ) = ((a' : ℤ) * t * t' - (a : ℤ) * s * s') * s
        + (a' : ℤ) * t * ((t : ℤ) * s' - t' * s) := by
      linear_combination (-(s' : ℤ)) * h1z
    have hUpos : (0 : ℤ) < (a' : ℤ) * t * t' - (a : ℤ) * s * s' := by
      have hsq : ((a : ℤ) * s * s') ^ 2 < ((a' : ℤ) * t * t') ^ 2 := by
        have e : ((a' : ℤ) * t * t') ^ 2 =
            ((a' : ℤ) * t ^ 2) * ((a' : ℤ) * t' ^ 2) := by ring
        rw [e]
        have h1e : (a' : ℤ) * (t : ℤ) ^ 2 = (a : ℤ) * (s : ℤ) ^ 2 + 1 := by
          linarith
        have h2e : (a' : ℤ) * (t' : ℤ) ^ 2 = (a : ℤ) * (s' : ℤ) ^ 2 + 1 := by
          linarith
        rw [h1e, h2e]
        have e2 : ((a : ℤ) * (s : ℤ) ^ 2 + 1) * ((a : ℤ) * (s' : ℤ) ^ 2 + 1) =
            ((a : ℤ) * s * s') ^ 2 + ((a : ℤ) * (s : ℤ) ^ 2
              + (a : ℤ) * (s' : ℤ) ^ 2 + 1) := by ring
        rw [e2]
        have hpos : (0 : ℤ) ≤ (a : ℤ) * (s : ℤ) ^ 2 + (a : ℤ) * (s' : ℤ) ^ 2 := by
          positivity
        linarith
      have hlt' := abs_lt_of_sq_lt_sq hsq
        (by positivity : (0 : ℤ) ≤ (a' : ℤ) * t * t')
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (a : ℤ) * s * s')] at hlt'
      exact sub_pos.mpr hlt'
    set U : ℤ := (a' : ℤ) * t * t' - (a : ℤ) * s * s' with hUdef
    set V : ℤ := (t : ℤ) * s' - (t' : ℤ) * s with hVdef
    -- basic casts
    have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have ha'1 : (1 : ℤ) ≤ (a' : ℤ) := by exact_mod_cast ha'
    have ht1z : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht
    have hs1z : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast hs
    have hs'1z : (1 : ℤ) ≤ (s' : ℤ) := by exact_mod_cast hs'
    have ht'z : (t : ℤ) + 1 ≤ (t' : ℤ) := by exact_mod_cast hlt
    have ht'1z : (1 : ℤ) ≤ (t' : ℤ) := by linarith
    have hs'z : (s : ℤ) + 1 ≤ (s' : ℤ) := by exact_mod_cast hss'
    rcases lt_trichotomy V 0 with hVn | hV0 | hVp
    · -- `V ≤ -1`: `ts = t's' + (-V)(a'tt' + ass') > ts`, contradiction.
      have hV1 : (1 : ℤ) ≤ -V := by linarith
      have e1 : U * t = (t' : ℤ) - (a : ℤ) * s * V := by
        linear_combination -hte
      have e2 : U * s = (s' : ℤ) - (a' : ℤ) * t * V := by
        linear_combination -hse
      have e3 : U ^ 2 * ((t : ℤ) * s) =
          ((t' : ℤ) - (a : ℤ) * s * V) * ((s' : ℤ) - (a' : ℤ) * t * V) := by
        calc U ^ 2 * ((t : ℤ) * s) = (U * t) * (U * s) := by ring
          _ = _ := by rw [e1, e2]
      have key : (t : ℤ) * s =
          t' * s' + (-V) * ((a' : ℤ) * t * t' + (a : ℤ) * s * s') := by
        linear_combination e3 - ((t : ℤ) * s) * hU2
      have h1' : (1 : ℤ) ≤ (a' : ℤ) * t * t' := by
        have h2' : (1 : ℤ) ≤ (a' : ℤ) * t := by
          have hm := mul_le_mul ha'1 ht1z (show (0 : ℤ) ≤ 1 by norm_num)
            (by positivity : (0 : ℤ) ≤ a')
          rwa [one_mul] at hm
        have hm := mul_le_mul h2' ht'1z (show (0 : ℤ) ≤ 1 by norm_num)
          (by linarith only [h2'] : (0 : ℤ) ≤ (a' : ℤ) * t)
        rwa [one_mul] at hm
      have hP : (1 : ℤ) ≤ (a' : ℤ) * t * t' + (a : ℤ) * s * s' := by
        have hnn : (0 : ℤ) ≤ (a : ℤ) * s * s' := by positivity
        linarith only [h1', hnn]
      have hWP : (1 : ℤ) ≤ (-V) * ((a' : ℤ) * t * t' + (a : ℤ) * s * s') := by
        have hm := mul_le_mul hV1 hP (show (0 : ℤ) ≤ 1 by norm_num)
          (by linarith only [hV1] : (0 : ℤ) ≤ -V)
        rwa [one_mul] at hm
      have hprod : (t : ℤ) * s + 1 ≤ t' * s' := by
        have hmul : ((t : ℤ) + 1) * ((s : ℤ) + 1) ≤ t' * s' :=
          mul_le_mul ht'z hs'z (by linarith only [hs1z]) (by linarith only [ht'1z])
        have e : ((t : ℤ) + 1) * ((s : ℤ) + 1) =
            (t : ℤ) * s + t + s + 1 := by ring
        linarith only [hmul, e, ht1z, hs1z]
      exfalso
      linarith only [key, hWP, hprod]
    · -- `V = 0`: `u² = 1`, `u ≥ 1` gives `u = 1`, then `t' = t`.
      rw [hV0] at hU2 hte
      simp at hU2 hte
      obtain hu | hu := hU2
      · rw [hu, one_mul] at hte
        have htt : t' = t := by exact_mod_cast hte
        omega
      · rw [hu] at hUpos
        norm_num at hUpos
    · -- `V ≥ 1`: `u ≥ 2`, hence `t' = ut + asv ≥ 2t + 1`.
      have hV1 : (1 : ℤ) ≤ V := hVp
      have hUge : (2 : ℤ) ≤ U := by
        have hV2 : (1 : ℤ) ≤ V ^ 2 := by
          have hm := mul_le_mul hV1 hV1 (show (0 : ℤ) ≤ 1 by norm_num)
            (by linarith only [hV1] : (0 : ℤ) ≤ V)
          rwa [one_mul, ← pow_two] at hm
        have haa : (1 : ℤ) ≤ (a : ℤ) * a' := by
          have hm := mul_le_mul ha1 ha'1 (show (0 : ℤ) ≤ 1 by norm_num)
            (by positivity : (0 : ℤ) ≤ a)
          rwa [one_mul] at hm
        have h2 : (2 : ℤ) ≤ U ^ 2 := by
          have hmul : (1 : ℤ) ≤ ((a : ℤ) * a') * V ^ 2 := by
            have hm := mul_le_mul haa hV2 (show (0 : ℤ) ≤ 1 by norm_num)
              (by positivity : (0 : ℤ) ≤ (a : ℤ) * a')
            rwa [one_mul] at hm
          linarith only [hU2, hmul]
        rcases lt_or_ge U 2 with h2U | h2U
        · exfalso
          have hU1 : U = 1 := by omega
          rw [hU1] at h2
          norm_num at h2
        · exact h2U
      have hUt : (2 : ℤ) * t ≤ U * t :=
        mul_le_mul hUge (le_refl _) (by positivity) hUpos.le
      have hasV : (1 : ℤ) ≤ (a : ℤ) * s * V := by
        have has : (1 : ℤ) ≤ (a : ℤ) * s := by
          have hm := mul_le_mul ha1 hs1z (show (0 : ℤ) ≤ 1 by norm_num)
            (by positivity : (0 : ℤ) ≤ a)
          rwa [one_mul] at hm
        have hm := mul_le_mul has hV1 (show (0 : ℤ) ≤ 1 by norm_num)
          (by linarith only [has] : (0 : ℤ) ≤ (a : ℤ) * s)
        rwa [one_mul] at hm
      have hbig : (2 : ℤ) * t + 1 ≤ (t' : ℤ) := by linarith only [hte, hUt, hasV]
      have hfinal : (2 : ℤ) * t ≤ (t' : ℤ) := by linarith only [hbig]
      exact_mod_cast hfinal

end PellGrowth

section Counting

/-- `pellSolFinset a a' T`: the `t ≤ T` for which `a'·t² = a·s² + 1` has a
natural solution `s`. -/
noncomputable def pellSolFinset (a a' T : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter fun t => ∃ s : ℕ, a' * t ^ 2 = a * s ^ 2 + 1

theorem mem_pellSolFinset {a a' T t : ℕ} :
    t ∈ pellSolFinset a a' T ↔ t ≤ T ∧ ∃ s : ℕ, a' * t ^ 2 = a * s ^ 2 + 1 := by
  rw [pellSolFinset, Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]

/-- The Pell solution count is logarithmic: doubling of consecutive
solutions (`pell_consec_growth`) makes `Nat.log 2` strictly monotone, hence
injective, on `pellSolFinset`, with image in `range (Nat.log 2 T + 1)`. -/
theorem pellSolFinset_card_le_log (a a' T : ℕ) (ha : 1 ≤ a) (ha' : 1 ≤ a') :
    (pellSolFinset a a' T).card ≤ Nat.log 2 T + 1 := by
  have hcard : (pellSolFinset a a' T).card ≤
      (Finset.range (Nat.log 2 T + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun t => Nat.log 2 t)
    · intro t ht
      rw [Finset.mem_coe, mem_pellSolFinset] at ht
      rw [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_add_one_iff.mpr (Nat.log_mono_right ht.1)
    · intro t₁ ht₁ t₂ ht₂ hlog
      rw [Finset.mem_coe, mem_pellSolFinset] at ht₁ ht₂
      obtain ⟨ht₁T, s₁, hs₁⟩ := ht₁
      obtain ⟨ht₂T, s₂, hs₂⟩ := ht₂
      have hlog' : Nat.log 2 t₁ = Nat.log 2 t₂ := hlog
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hg := pell_consec_growth ha ha' hs₁ hs₂ hlt
        have ht1 : t₁ ≠ 0 := by
          intro h0
          rw [h0] at hs₁
          simp only [pow_two, mul_zero] at hs₁
          omega
        have hmono : Nat.log 2 t₁ + 1 ≤ Nat.log 2 t₂ := by
          calc Nat.log 2 t₁ + 1 = Nat.log 2 (t₁ * 2) :=
                (Nat.log_mul_base one_lt_two ht1).symm
            _ = Nat.log 2 (2 * t₁) := by rw [Nat.mul_comm]
            _ ≤ Nat.log 2 t₂ := Nat.log_mono_right hg
        omega
      · have hg := pell_consec_growth ha ha' hs₂ hs₁ hgt
        have ht2 : t₂ ≠ 0 := by
          intro h0
          rw [h0] at hs₂
          simp only [pow_two, mul_zero] at hs₂
          omega
        have hmono : Nat.log 2 t₂ + 1 ≤ Nat.log 2 t₁ := by
          calc Nat.log 2 t₂ + 1 = Nat.log 2 (t₂ * 2) :=
                (Nat.log_mul_base one_lt_two ht2).symm
            _ = Nat.log 2 (2 * t₂) := by rw [Nat.mul_comm]
            _ ≤ Nat.log 2 t₁ := Nat.log_mono_right hg
        omega
  rwa [Finset.card_range] at hcard

/-- Trivial bound: `pellSolFinset ⊆ range (T + 1)`. -/
theorem pellSolFinset_card_le (a a' T : ℕ) :
    (pellSolFinset a a' T).card ≤ T + 1 := by
  unfold pellSolFinset
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- The kernel–solution sigma finset: pairs `(k₁, k₂)` of subsets of the
primes `≤ p` (i.e. `< p + 1`), together with a `t ≤ T` solving
`k₂.prod·t² = k₁.prod·s² + 1` for some `s`. -/
noncomputable def pairKernelSigma (p T : ℕ) :
    Finset (Σ _ : Finset ℕ × Finset ℕ, ℕ) :=
  ((Nat.primesBelow (p + 1)).powerset ×ˢ (Nat.primesBelow (p + 1)).powerset).sigma
    fun kk => pellSolFinset (kk.1.prod id) (kk.2.prod id) T

/-- The product of a subset of `primesBelow` is at least `1`. -/
theorem one_le_kernel_prod {p : ℕ} {s : Finset ℕ}
    (hs : s ∈ (Nat.primesBelow (p + 1)).powerset) : 1 ≤ s.prod id := by
  rw [Finset.mem_powerset] at hs
  exact Finset.one_le_prod fun i hi =>
    (Nat.prime_of_mem_primesBelow (hs hi)).one_le

/-- Every pair beginning `n ≤ x` with `1 ≤ n` is captured by a kernel pair
and a Pell solution; `n = 0` is added separately. -/
theorem consecSmoothPairFinset_subset_image (x p : ℕ) :
    (Finset.range (x + 1)).filter (fun n => consecSmoothPair n p) ⊆
      insert 0 ((pairKernelSigma p (Nat.sqrt (x + 1))).image
        fun kk => kk.1.2.prod id * kk.2 ^ 2 - 1) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hnx, hpair⟩ := hn
  rcases Nat.eq_zero_or_pos n with h0 | hn1
  · subst h0
    exact Finset.mem_insert_self _ _
  · rw [Finset.mem_insert]
    right
    obtain ⟨s₁, s₂, m₁, m₂, hs₁, hs₂, _, _, hn₁eq, hn₂eq, _⟩ :=
      consecSmoothPair_exists_kernel hn1 hpair
    rw [Finset.mem_image]
    refine ⟨Sigma.mk (s₁, s₂) m₂, ?_, ?_⟩
    · rw [pairKernelSigma, Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr hs₁, Finset.mem_powerset.mpr hs₂⟩
      · show m₂ ∈ pellSolFinset (s₁.prod id) (s₂.prod id) (Nat.sqrt (x + 1))
        rw [mem_pellSolFinset]
        have hprod1 : 1 ≤ s₂.prod id := Finset.one_le_prod fun i hi =>
          (Nat.prime_of_mem_primesBelow (hs₂ hi)).one_le
        have hm₂sq : m₂ ^ 2 ≤ x + 1 := by
          have hle : m₂ ^ 2 * 1 ≤ m₂ ^ 2 * s₂.prod id :=
            Nat.mul_le_mul (le_refl _) hprod1
          rw [mul_one] at hle
          omega
        refine ⟨Nat.le_sqrt'.mpr hm₂sq, m₁, ?_⟩
        have e1 : s₂.prod id * m₂ ^ 2 = m₂ ^ 2 * s₂.prod id := Nat.mul_comm _ _
        have e2 : m₁ ^ 2 * s₁.prod id = s₁.prod id * m₁ ^ 2 := Nat.mul_comm _ _
        omega
    · show s₂.prod id * m₂ ^ 2 - 1 = n
      have e1 : s₂.prod id * m₂ ^ 2 = m₂ ^ 2 * s₂.prod id := Nat.mul_comm _ _
      omega

/-- `consecSmoothPairCount x p` is at most `1 + #pairKernelSigma`. -/
theorem consecSmoothPairCount_le_kernelSigma (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + (pairKernelSigma p (Nat.sqrt (x + 1))).card := by
  unfold consecSmoothPairCount
  have h0 := Finset.card_le_card (consecSmoothPairFinset_subset_image x p)
  have h1 := Finset.card_insert_le (0 : ℕ)
    ((pairKernelSigma p (Nat.sqrt (x + 1))).image
      fun kk => kk.1.2.prod id * kk.2 ^ 2 - 1)
  have h2 : (((pairKernelSigma p (Nat.sqrt (x + 1))).image
        fun kk => kk.1.2.prod id * kk.2 ^ 2 - 1)).card ≤
      (pairKernelSigma p (Nat.sqrt (x + 1))).card := Finset.card_image_le
  omega

/-- The sigma cardinality is bounded by `4^{π'(p+1)} · (log₂ T + 1)`. -/
theorem pairKernelSigma_card_le_log (p T : ℕ) :
    (pairKernelSigma p T).card ≤
      4 ^ (Nat.primesBelow (p + 1)).card * (Nat.log 2 T + 1) := by
  unfold pairKernelSigma
  rw [Finset.card_sigma]
  have h4 : (2 : ℕ) ^ (Nat.primesBelow (p + 1)).card *
      2 ^ (Nat.primesBelow (p + 1)).card =
      4 ^ (Nat.primesBelow (p + 1)).card := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ∑ kk ∈ (Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset,
        (pellSolFinset (kk.1.prod id) (kk.2.prod id) T).card
      ≤ ∑ _kk ∈ (Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset,
        (Nat.log 2 T + 1) := by
        apply Finset.sum_le_sum
        intro kk hkk
        rw [Finset.mem_product] at hkk
        exact pellSolFinset_card_le_log _ _ _
          (one_le_kernel_prod hkk.1) (one_le_kernel_prod hkk.2)
    _ = ((Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset).card * (Nat.log 2 T + 1) :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = 4 ^ (Nat.primesBelow (p + 1)).card * (Nat.log 2 T + 1) := by
        rw [Finset.card_product, Finset.card_powerset, h4]

/-- The sigma cardinality is also bounded by `4^{π'(p+1)} · (T + 1)`. -/
theorem pairKernelSigma_card_le (p T : ℕ) :
    (pairKernelSigma p T).card ≤
      4 ^ (Nat.primesBelow (p + 1)).card * (T + 1) := by
  unfold pairKernelSigma
  rw [Finset.card_sigma]
  have h4 : (2 : ℕ) ^ (Nat.primesBelow (p + 1)).card *
      2 ^ (Nat.primesBelow (p + 1)).card =
      4 ^ (Nat.primesBelow (p + 1)).card := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ∑ kk ∈ (Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset,
        (pellSolFinset (kk.1.prod id) (kk.2.prod id) T).card
      ≤ ∑ _kk ∈ (Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset,
        (T + 1) := by
        apply Finset.sum_le_sum
        intro kk _hkk
        exact pellSolFinset_card_le _ _ _
    _ = ((Nat.primesBelow (p + 1)).powerset ×ˢ
          (Nat.primesBelow (p + 1)).powerset).card * (T + 1) :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = 4 ^ (Nat.primesBelow (p + 1)).card * (T + 1) := by
        rw [Finset.card_product, Finset.card_powerset, h4]

/-- **Headline bound (logarithmic per-kernel form).**
`consecSmoothPairCount x p ≤ 1 + 4^{π'(p+1)}·(log₂ √(x+1) + 1)`: the number
of consecutive `p`-smooth pair beginnings `≤ x` is at most the number of
kernel pairs `4^{π'(p+1)}` times the logarithmic Pell solution count.  For
`p ≤ c·log x` this is `x^{o(1)}`. -/
theorem consecSmoothPairCount_le_kernel_mul_log (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + 4 ^ (Nat.primesBelow (p + 1)).card *
        (Nat.log 2 (Nat.sqrt (x + 1)) + 1) :=
  (consecSmoothPairCount_le_kernelSigma x p).trans
    (add_le_add (le_refl 1) (pairKernelSigma_card_le_log _ _))

/-- Relaxed form with `log₂ (x + 1)` instead of `log₂ √(x + 1)`. -/
theorem consecSmoothPairCount_le_kernel_mul_log' (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + 4 ^ (Nat.primesBelow (p + 1)).card * (Nat.log 2 (x + 1) + 1) := by
  refine (consecSmoothPairCount_le_kernel_mul_log x p).trans ?_
  apply add_le_add (le_refl 1)
  apply Nat.mul_le_mul (le_refl _)
  exact add_le_add (Nat.log_mono_right (Nat.sqrt_le_self _)) (le_refl 1)

/-- **Deliverable bound (sqrt per-kernel form)**:
`consecSmoothPairCount x p ≤ 1 + 4^{π'(p+1)}·(√(x+1) + 1)`.  Weaker than
`consecSmoothPairCount_le_kernel_mul_log` but matching the requested shape
`(kernel count)²·(√x + 1)`. -/
theorem consecSmoothPairCount_le_kernel_mul_sqrt (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + 4 ^ (Nat.primesBelow (p + 1)).card * (Nat.sqrt (x + 1) + 1) :=
  (consecSmoothPairCount_le_kernelSigma x p).trans
    (add_le_add (le_refl 1) (pairKernelSigma_card_le _ _))

end Counting

section SmallPrime

/-- If `m ≥ 2` and `largestPrimeFactor m ≤ 2`, then `2 ∣ m`: the least prime
factor `minFac m` is a prime `≤ largestPrimeFactor m ≤ 2`, hence `= 2`. -/
theorem two_dvd_of_lpf_le_two {m : ℕ} (hm : 2 ≤ m)
    (h : largestPrimeFactor m ≤ 2) : 2 ∣ m := by
  have hprime : Nat.Prime (Nat.minFac m) := Nat.minFac_prime (by omega)
  have hle : Nat.minFac m ≤ largestPrimeFactor m :=
    prime_dvd_le_largestPrimeFactor hm hprime (Nat.minFac_dvd m)
  have heq : Nat.minFac m = 2 := le_antisymm (by omega) hprime.two_le
  exact heq ▸ Nat.minFac_dvd m

/-- A 2-smooth consecutive pair beginning is at most `1`: if `n ≥ 2` then
`2 ∣ n` and `2 ∣ n + 1`, contradiction. -/
theorem consecSmoothPair_le_one {n : ℕ} (h : consecSmoothPair n 2) : n ≤ 1 := by
  by_contra hc
  push Not at hc
  have hn2 : 2 ≤ n := by omega
  have hn1 : 2 ≤ n + 1 := by omega
  have h1 := two_dvd_of_lpf_le_two hn2 h.1
  have h2 := two_dvd_of_lpf_le_two hn1 h.2
  omega

/-- `consecSmoothPair 0 2` holds (both `0` and `1` have `largestPrimeFactor`
equal to `1`). -/
theorem consecSmoothPair_zero : consecSmoothPair 0 2 := by
  have h0 : largestPrimeFactor 0 = 1 :=
    largestPrimeFactor_eq_one_iff.mpr (by omega)
  have h1 : largestPrimeFactor (0 + 1) = 1 :=
    largestPrimeFactor_eq_one_iff.mpr (by omega)
  exact ⟨by omega, by omega⟩

/-- `largestPrimeFactor 2 = 2`, so `consecSmoothPair 1 2` holds (the pair
`1, 2`). -/
theorem consecSmoothPair_one : consecSmoothPair 1 2 := by
  have h1 : largestPrimeFactor 1 = 1 :=
    largestPrimeFactor_eq_one_iff.mpr (le_refl 1)
  have h2 : largestPrimeFactor 2 = 2 := by
    rw [largestPrimeFactor_eq_maxPrimeFac (by norm_num)]
    apply le_antisymm
    · rw [Nat.maxPrimeFac_le_iff (by norm_num)]
      intro q _hq hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    · exact Nat.le_maxPrimeFac (by norm_num) Nat.prime_two (Nat.dvd_refl 2)
  have h2' : largestPrimeFactor (1 + 1) = 2 := h2
  exact ⟨by omega, by omega⟩

/-- `consecSmoothPairCount x 2 ≤ 2`: the only 2-smooth pair beginnings are
`n = 0` and `n = 1` (the pair `1, 2`). -/
theorem consecSmoothPairCount_two_le (x : ℕ) : consecSmoothPairCount x 2 ≤ 2 := by
  have hsub : (Finset.range (x + 1)).filter (fun n => consecSmoothPair n 2) ⊆
      {0, 1} := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hle := consecSmoothPair_le_one hn.2
    rw [Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold consecSmoothPairCount
  exact (Finset.card_le_card hsub).trans
    (le_of_eq (Finset.card_pair (by norm_num : (0 : ℕ) ≠ 1)))

/-- Exact value: `consecSmoothPairCount x 2 = min x 1 + 1`. -/
theorem consecSmoothPairCount_two (x : ℕ) :
    consecSmoothPairCount x 2 = min x 1 + 1 := by
  have hset : (Finset.range (x + 1)).filter (fun n => consecSmoothPair n 2) =
      (Finset.range (x + 1)).filter (fun n => n ≤ 1) := by
    apply Finset.filter_congr
    intro n _
    constructor
    · intro h
      exact consecSmoothPair_le_one h
    · intro h
      interval_cases n
      · exact consecSmoothPair_zero
      · exact consecSmoothPair_one
  rw [consecSmoothPairCount, hset]
  have hset2 : (Finset.range (x + 1)).filter (fun n => n ≤ 1) =
      Finset.range (min x 1 + 1) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    omega
  rw [hset2, Finset.card_range]

end SmallPrime

end JSP314
