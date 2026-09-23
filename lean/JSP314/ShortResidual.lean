import JSP314.PairSmooth
import JSP314.SSBound

/-!
# Singleton-free reduction of the short bad-interval count

The earlier reduction `smoothArcCoveredCount_le_badSingleton_add_pairCount`
bounds `T_arc(x)` by `S(2x) + 2·Σ_p consecSmoothPairCount x p`.  The `S(2x)`
term is too large to be absorbed by `S(x)·(log x)^{-1+ε}` (the truth is
`S(x) = x^{1-o(1)}`), so it must not pass through the residual bound.

This file sharpens the pointwise reduction: **every** point `n` covered by a
short (non-singleton) bad interval is `nearPairCovered`, *including* the
witness `n = m` itself — since `u < v` forces a `p`-smooth neighbour `m ± 1`
of `m` inside the interval.  Hence there is no singleton summand:

```
shortBadCount x ≤ Σ_{p ≤ √(2x)} nearPairCoveredCount x p
```

and, combined with `SSBound.badNonSingletonCount_le_short_add_const`,

```
badNonSingletonCount x ≤ Σ_p nearPairCoveredCount x p + (2·10^16 + 1).
```

The residual analytic core is therefore exactly a bound on the windowed
consecutive-smooth-pair count `Σ_p nearPairCoveredCount x p`.
-/

namespace JSP314

open Classical

/-- Every point `n` of a short bad interval `[u,v]` (`u < v`, `v - u < P`)
is one member `j` or `j + 1` of a consecutive `P`-smooth pair within `P`
of the interval's `P²`-witness `m`.

Case `n < v`: take `j = n` — then `n + 1 ∈ [u,v]` is `P`-smooth.
Case `n = v`: take `j = n - 1` — then `n - 1 ∈ [u,v]` is `P`-smooth
(needs `u < v`, so `n - 1 ≥ u`).  This covers `n = m` as well. -/
theorem inShortBadInterval_nearPairCovered {x n : ℕ} (hx : n ≤ x)
    (h : InShortBadInterval n) :
    ∃ p, p ∈ Nat.primesLE (Nat.sqrt (2 * x)) ∧ nearPairCovered x n p := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := h
  obtain ⟨m, hmI, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf := sq_dvd_mem_lpf_eq hbad hmI hdvd
  have hbs := sq_dvd_mem_is_bad_singleton' hbad hmI hdvd
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  set p := largestPrimeFactor m with hpdef
  have hp_prime : p.Prime := largestPrimeFactor_prime (by omega : 2 ≤ m)
  have hp2 : 2 ≤ p := hp_prime.two_le
  have hmIcc := Finset.mem_Icc.mp hmI
  have hm2x : m ≤ 2 * x := by omega
  have hp_le : p ≤ Nat.sqrt (2 * x) := by
    have h1 : p ^ 2 ≤ m := Nat.le_of_dvd (by omega) hbs.2
    have h2 : p * p ≤ 2 * x := by
      have := h1.trans hm2x
      nlinarith
    exact Nat.le_sqrt.mpr h2
  have hshort' : v - u < p := by rwa [← hlpf] at hshort
  have hall : ∀ j ∈ Finset.Icc u v, largestPrimeFactor j ≤ p := by
    intro j hj
    calc largestPrimeFactor j
        ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
          short_bad_interval_all_lpf_le hbad j hj
      _ = p := hlpf.symm
  refine ⟨p, Nat.mem_primesLE.mpr ⟨hp_le, hp_prime⟩, ?_⟩
  rcases lt_or_eq_of_le hnv with hlt | heq
  · -- `j = n`: `n + 1 ∈ [u, v]`.
    have hn1 : n + 1 ∈ Finset.Icc u v :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    refine ⟨n, m, ⟨hall n (Finset.mem_Icc.mpr ⟨hun, hnv⟩), hall (n + 1) hn1⟩,
      Or.inl rfl, by omega, by omega, hbs.1, hbs.2, hpdef.symm, hm2x⟩
  · -- `n = v`: `j = n - 1 ∈ [u, v]`.
    have hn1 : n - 1 ∈ Finset.Icc u v :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hnpos : 1 ≤ n := by omega
    refine ⟨n - 1, m, ⟨hall (n - 1) hn1, ?_⟩, Or.inr ?_, by omega, by omega,
      hbs.1, hbs.2, hpdef.symm, hm2x⟩
    · have : n - 1 + 1 = n := by omega
      rw [this]
      exact hall n (Finset.mem_Icc.mpr ⟨hun, hnv⟩)
    · omega

/-- `T_short(x) ≤ Σ_{p ≤ √(2x)} nearPairCoveredCount x p` — no singleton
summand. -/
theorem shortBadCount_le_nearPair_sum (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p := by
  classical
  unfold shortBadCount nearPairCoveredCount
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      (Nat.primesLE (Nat.sqrt (2 * x))).biUnion
        (fun p => (Finset.range (x + 1)).filter fun n => nearPairCovered x n p) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨p, hp, hnp⟩ :=
      inShortBadInterval_nearPairCovered (Nat.lt_add_one_iff.mp hn.1) hn.2
    rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnp⟩⟩
  calc ((Finset.range (x + 1)).filter fun n => InShortBadInterval n).card
      ≤ ((Nat.primesLE (Nat.sqrt (2 * x))).biUnion
          (fun p => (Finset.range (x + 1)).filter
            fun n => nearPairCovered x n p)).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ((Finset.range (x + 1)).filter fun n => nearPairCovered x n p).card :=
        Finset.card_biUnion_le

/-- **The residual decomposition**: the non-singleton bad-interval count is
bounded by the windowed consecutive-smooth-pair sum plus the absolute
constant `2·10^16 + 1` (the long branch, `SSBound`). -/
theorem badNonSingletonCount_le_nearPair_sum_add_const (x : ℕ) :
    badNonSingletonCount x ≤
      (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_short_add_const x
  have h2 := shortBadCount_le_nearPair_sum x
  omega

end JSP314
