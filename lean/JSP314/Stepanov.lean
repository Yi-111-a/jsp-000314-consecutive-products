import Mathlib

/-!
# Stage-0 utilities for the Stepanov/Weil character-sum bound

Pure polynomial algebra over `ZMod p`, supporting the Stepanov method:

* `hasseDeriv_frobenius_pow`: Hasse derivatives of order `0 < k < p` kill `X^(j*p)`
  (a consequence of Lucas's theorem: `p ∣ (j*p).choose k`).
* `pow_sub_hasseDeriv_dvd_pow`: `f^(M-k) ∣ hasseDeriv k (f^M)` for `k ≤ M`.
* `dvd_pow_card_sub_X_iff_vanish`: `(X^p - X) ∣ S ↔ ∀ x : ZMod p, S.eval x = 0`.
* `pow_dvd_of_hasseDeriv_eval_eq_zero`: vanishing of all Hasse derivatives of order `< M`
  at `x₀` implies `(X - C x₀)^M ∣ r` (via the Taylor expansion).
* `card_le_natDegree_of_hasseDeriv_vanish`: distinct high-order zeros force
  `M * #T ≤ r.natDegree` for nonzero `r`.
-/

namespace JSP314

open Polynomial FiniteField

variable (p : ℕ) [Fact p.Prime]

/-- Frobenius invisibility: Hasse derivatives of order `0 < k < p`
kill `X^(j*p)` over `ZMod p` (Lucas's theorem: `(j*p).choose k ≡ 0`). -/
lemma hasseDeriv_frobenius_pow {k j : ℕ} (hk : 0 < k) (hkp : k < p) :
    hasseDeriv k ((X : (ZMod p)[X]) ^ (j * p)) = 0 := by
  have hdvd : p ∣ (j * p).choose k := by
    have hLuc :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := j * p) (k := k) (p := p)
    rw [Nat.mul_mod_right, Nat.mod_eq_of_lt hkp, Nat.choose_eq_zero_of_lt hk, zero_mul] at hLuc
    exact Nat.modEq_zero_iff_dvd.mp hLuc
  have hX : (X : (ZMod p)[X]) ^ (j * p) = monomial (j * p) 1 := by
    rw [← monomial_one_one_eq_X, monomial_pow, one_pow, one_mul]
  rw [hX, hasseDeriv_monomial, mul_one,
    (CharP.cast_eq_zero_iff (ZMod p) p _).mpr hdvd, monomial_zero_right]

/-- `f^(M-k)` divides the `k`-th Hasse derivative of `f^M` for `k ≤ M`. -/
lemma pow_sub_hasseDeriv_dvd_pow (f : (ZMod p)[X]) {k M : ℕ} (h : k ≤ M) :
    f ^ (M - k) ∣ hasseDeriv k (f ^ M) := by
  induction M generalizing k with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero h
    simp
  | succ M ih =>
    rw [pow_succ', hasseDeriv_mul]
    apply Finset.dvd_sum
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp only [zero_add] at hij
      subst hij
      rw [hasseDeriv_zero']
      by_cases hkM : k ≤ M
      · have hd := ih hkM
        rw [show M + 1 - k = M - k + 1 by omega, pow_succ']
        exact mul_dvd_mul_left f hd
      · have : k = M + 1 := by omega
        subst this
        simp
    · have hj : j ≤ M := by omega
      have hd := ih hj
      have hle : M + 1 - k ≤ M - j := by omega
      exact (pow_dvd_pow f hle).trans (dvd_mul_of_dvd_left hd _)

/-- A polynomial over `ZMod p` vanishing at every `x : ZMod p` is
divisible by `X^p - X`. -/
lemma dvd_pow_card_sub_X_iff_vanish (S : (ZMod p)[X]) :
    (X ^ p - X) ∣ S ↔ ∀ x : ZMod p, S.eval x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ x
    rw [eval_mul, eval_sub, eval_pow, eval_X, ZMod.pow_card, sub_self, zero_mul]
  · intro h
    by_cases hS : S = 0
    · subst hS; exact dvd_zero _
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
      have hr := FiniteField.roots_X_pow_card_sub_X (ZMod p)
      rwa [ZMod.card p] at hr
    have hprod : (X ^ p - X : (ZMod p)[X]) = ∏ x : ZMod p, (X - C x) := by
      have hcard : Multiset.card (roots (X ^ p - X : (ZMod p)[X])) = (X ^ p - X).natDegree := by
        rw [hroots, ← Finset.card_def, Finset.card_univ, ZMod.card p,
          FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp1]
      have hmonic : (X ^ p - X : (ZMod p)[X]).Monic :=
        (monic_X_pow p).sub_of_left (by
          rw [degree_X_pow, degree_X]
          exact_mod_cast hp1)
      have key := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
      rw [hroots] at key
      exact key.symm
    rw [hprod]
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy))
    · intro x _
      exact dvd_iff_isRoot.mpr (IsRoot.def.mpr (h x))

/-- If all Hasse derivatives of order `< M` of `r` vanish at `x₀`,
then `(X - C x₀)^M ∣ r`. -/
lemma pow_dvd_of_hasseDeriv_eval_eq_zero (r : (ZMod p)[X]) (x₀ : ZMod p) (M : ℕ)
    (h : ∀ j < M, (hasseDeriv j r).eval x₀ = 0) :
    (X - C x₀) ^ M ∣ r := by
  have hdvd : (X : (ZMod p)[X]) ^ M ∣ taylor x₀ r := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [taylor_coeff, h d hd]
  obtain ⟨g, hg⟩ := hdvd
  have hrr : taylor (-x₀) (taylor x₀ r) = r := by
    rw [taylor_taylor, neg_add_cancel, taylor_zero]
  have hX : taylor (-x₀) (X : (ZMod p)[X]) = X - C x₀ := by
    rw [taylor_X, C_neg, sub_eq_add_neg]
  rw [← hrr, hg, taylor_mul, taylor_pow, hX]
  exact dvd_mul_right _ _

/-- Distinct points give coprime power factors: if `r` vanishes to order `M`
at each point of a finite set `T ⊆ ZMod p`, then `M * #T ≤ r.natDegree`
provided `r ≠ 0`. -/
lemma card_le_natDegree_of_hasseDeriv_vanish (r : (ZMod p)[X]) (hr : r ≠ 0)
    (M : ℕ) (hM : 0 < M) (T : Finset (ZMod p))
    (h : ∀ x₀ ∈ T, ∀ j < M, (hasseDeriv j r).eval x₀ = 0) :
    M * T.card ≤ r.natDegree := by
  have hdvd : (∏ x ∈ T, (X - C x) ^ M : (ZMod p)[X]) ∣ r := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact IsCoprime.pow
        (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy)))
    · intro x hx
      exact pow_dvd_of_hasseDeriv_eval_eq_zero p r x M (h x hx)
  have hdeg : (∏ x ∈ T, (X - C x) ^ M : (ZMod p)[X]).natDegree = M * T.card := by
    rw [natDegree_prod (fun x _ => pow_ne_zero M (monic_X_sub_C x).ne_zero)]
    simp_rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  calc M * T.card = (∏ x ∈ T, (X - C x) ^ M : (ZMod p)[X]).natDegree := hdeg.symm
    _ ≤ r.natDegree := natDegree_le_of_dvd hdvd hr

end JSP314
