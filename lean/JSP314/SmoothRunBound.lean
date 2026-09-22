import JSP314.ShortLong

/-!
# JSP-000314 — composite-run structure of smooth runs

Structural and quantitative consequences of the smooth-run machinery of
`JSP314.ShortLong`.

* `smoothRun_not_prime`: in a smooth run `[u, v]` every element exceeding the
  smoothness bound `v - u` is composite (a prime `i` would satisfy
  `largestPrimeFactor i = i ≤ v - u < i`).
* `bad_long_interval_all_composite`: for a *long* non-singleton bad interval
  (`P ≤ v - u`), the dyadic squeeze `v + 2 ≤ 2u` puts every element above
  `v - u`, so the whole interval is composite.
* `InCompositeRun n L`: `n` lies in a run of `≥ L` consecutive composites.
  Every long-bad-covered point satisfies `InCompositeRun n 2`, and a composite
  run `[u, v]` sits inside a prime gap of length `≥ v + 2 - u`.
* Counting: with `longBadCount` (points covered by long bad intervals) and
  `compositeRunCount` (points in composite runs of length `≥ 2`) one gets
  `badNonSingletonCount x ≤ shortBadCount x + compositeRunCount x`.
-/

namespace JSP314

open Classical

section PrimesInRuns

/-- The largest prime factor of a prime is the prime itself. -/
theorem largestPrimeFactor_eq_self_of_prime {p : ℕ} (hp : Nat.Prime p) :
    largestPrimeFactor p = p := by
  rw [largestPrimeFactor_eq_maxPrimeFac hp.two_le]
  exact Nat.Prime.maxPrimeFac_eq_self hp

/-- No element of a smooth run `[u, v]` that exceeds the smoothness bound
`v - u` can be prime: a prime `i` has `largestPrimeFactor i = i`, which would
give `i ≤ v - u < i`. -/
theorem smoothRun_not_prime {u v i : ℕ} (h : IsSmoothRun u v)
    (hi : i ∈ Finset.Icc u v) (hLi : v - u < i) : ¬ i.Prime := by
  intro hp
  have hle := h.2 i hi
  rw [largestPrimeFactor_eq_self_of_prime hp] at hle
  omega

/-- In a smooth run, every element of `[max u (v - u + 1), v]` is composite. -/
theorem smoothRun_forall_not_prime {u v : ℕ} (h : IsSmoothRun u v) :
    ∀ i ∈ Finset.Icc u v, v - u + 1 ≤ i → ¬ i.Prime := by
  intro i hi hLi
  exact smoothRun_not_prime h hi (by omega)

/-- Every element of a *long* non-singleton bad interval (`P ≤ v - u`) is
composite.  The squeeze `v + 2 ≤ 2u` gives `v - u < u ≤ i`, so every member
exceeds the smoothness bound and `smoothRun_not_prime` applies.

In other words a long bad interval is a run of `L = v - u + 1` consecutive
composite numbers, hence sits inside a prime gap of length `≥ L + 1`. -/
theorem bad_long_interval_all_composite {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hlong : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u) :
    ∀ i ∈ Finset.Icc u v, ¬ i.Prime := by
  have hs : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  have hr : IsSmoothRun u v := bad_interval_isSmoothRun_of_long hbad huv hlong
  intro i hi
  have hI := Finset.mem_Icc.mp hi
  exact smoothRun_not_prime hr hi (by omega)

/-- A point covered by a long non-singleton bad interval is composite. -/
theorem inLongBadInterval_not_prime {n : ℕ} (h : InLongBadInterval n) :
    ¬ n.Prime := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hlong⟩ := h
  exact bad_long_interval_all_composite hbad huv hlong n
    (Finset.mem_Icc.mpr ⟨hun, hnv⟩)

/-- Explicit-existential form of `inLongBadInterval_not_prime`: a point
covered by a non-singleton bad interval with `P ≤ v - u` is composite. -/
theorem smoothRunCovered_composite_of_bad {n : ℕ}
    (h : ∃ u v, IsBadInterval u v ∧ u < v ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u ∧
      u ≤ n ∧ n ≤ v) : ¬ n.Prime := by
  obtain ⟨u, v, hbad, huv, hlong, hun, hnv⟩ := h
  exact inLongBadInterval_not_prime ⟨u, v, huv, hbad, hun, hnv, hlong⟩

end PrimesInRuns

section CompositeRuns

/-- `n` lies in a run of at least `L` consecutive composite integers. -/
def InCompositeRun (n L : ℕ) : Prop :=
  ∃ u v : ℕ, L ≤ v + 1 - u ∧ (∀ i ∈ Finset.Icc u v, ¬ i.Prime) ∧
    u ≤ n ∧ n ≤ v

/-- Any point of a composite run is composite. -/
theorem inCompositeRun_not_prime {n L : ℕ} (h : InCompositeRun n L) :
    ¬ n.Prime := by
  obtain ⟨u, v, -, hcomp, hun, hnv⟩ := h
  exact hcomp n (Finset.mem_Icc.mpr ⟨hun, hnv⟩)

/-- A point covered by a long non-singleton bad interval lies in a composite
run of length at least `2` (in fact of length `v - u + 1 ≥ 2`). -/
theorem inLongBadInterval_inCompositeRun {n : ℕ} (h : InLongBadInterval n) :
    InCompositeRun n 2 := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hlong⟩ := h
  exact ⟨u, v, by omega, bad_long_interval_all_composite hbad huv hlong,
    hun, hnv⟩

/-- More precisely, a point covered by a long bad interval lies in a
composite run of length exactly `v - u + 1`. -/
theorem inLongBadInterval_inCompositeRun_length {n : ℕ}
    (h : InLongBadInterval n) :
    ∃ L : ℕ, 2 ≤ L ∧ InCompositeRun n L := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hlong⟩ := h
  exact ⟨v + 1 - u, by omega, u, v, le_refl _,
    bad_long_interval_all_composite hbad huv hlong, hun, hnv⟩

/-- **Prime-gap bound**: a composite run `[u, v]` with `u ≥ 2` sits strictly
between two primes `p < u ≤ v < q`, so the surrounding prime gap `q - p` has
length at least `v + 2 - u` — one more than the run length `v + 1 - u`.

Here `p = 2` works since a composite `u ≥ 2` satisfies `u ≥ 4`, and `q` is
supplied by Bertrand's postulate. -/
theorem compositeRun_prime_gap {u v : ℕ} (hu : 2 ≤ u) (huv : u ≤ v)
    (h : ∀ i ∈ Finset.Icc u v, ¬ i.Prime) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < u ∧ v < q ∧ v + 2 - u ≤ q - p := by
  have huc : ¬ u.Prime := h u (Finset.mem_Icc.mpr ⟨le_refl u, huv⟩)
  have hu4 : 4 ≤ u := by
    rcases (by omega : u = 2 ∨ u = 3 ∨ 4 ≤ u) with rfl | rfl | h4
    · exact absurd Nat.prime_two huc
    · exact absurd Nat.prime_three huc
    · exact h4
  obtain ⟨q, hq, hvq, -⟩ :=
    Nat.exists_prime_lt_and_le_two_mul v (by omega)
  exact ⟨2, q, Nat.prime_two, hq, by omega, hvq, by omega⟩

end CompositeRuns

section Counts

/-- Count of `n ≤ x` covered by a *long* non-singleton bad interval. -/
noncomputable def longBadCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InLongBadInterval n).card

/-- Count of `n ≤ x` lying in a composite run of length at least `2`. -/
noncomputable def compositeRunCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InCompositeRun n 2).card

/-- Long-bad-covered points are covered by composite runs of length `≥ 2`:
`longBadCount x ≤ compositeRunCount x`. -/
theorem longBadCount_le_compositeRunCount (x : ℕ) :
    longBadCount x ≤ compositeRunCount x := by
  unfold longBadCount compositeRunCount
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, inLongBadInterval_inCompositeRun hn.2⟩

/-- Long-bad-covered points are smooth-run covered:
`longBadCount x ≤ smoothRunCoveredCount x`. -/
theorem longBadCount_le_smoothRunCoveredCount (x : ℕ) :
    longBadCount x ≤ smoothRunCoveredCount x := by
  unfold longBadCount smoothRunCoveredCount
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, inLongBadInterval_smoothRunCovered hn.2⟩

/-- Refined decomposition bound: `N(x) ≤ T_short(x) + L_long(x)`. -/
theorem badNonSingletonCount_le_short_add_longBad (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + longBadCount x := by
  unfold badNonSingletonCount shortBadCount longBadCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, hnbad⟩ := hn
  rcases inNonSingletonBadInterval_iff_short_or_long.mp hnbad with h | h
  · exact Or.inl ⟨hnx, h⟩
  · exact Or.inr ⟨hnx, h⟩

/-- `N(x) ≤ T_short(x) + C(x)`: the non-singleton bad count is bounded by the
short-interval count plus the number of points lying in composite runs of
length `≥ 2`. -/
theorem badNonSingletonCount_le_short_add_compositeRun (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + compositeRunCount x :=
  (badNonSingletonCount_le_short_add_longBad x).trans
    (Nat.add_le_add_left (longBadCount_le_compositeRunCount x) _)

/-- Trivial cardinality bound `smoothRunCoveredCount x ≤ x + 1`. -/
theorem smoothRunCoveredCount_le (x : ℕ) : smoothRunCoveredCount x ≤ x + 1 := by
  unfold smoothRunCoveredCount
  refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
  rw [Finset.card_range]

end Counts

end JSP314
