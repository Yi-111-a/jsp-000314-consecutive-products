import JSP314.Defs
import JSP314.Squeeze
import JSP314.Type2Run
import JSP314.Main
import Mathlib.Tactic.Push

/-!
# JSP-000314 — type-1 / type-2 decomposition of non-singleton bad intervals

Every point `n` covered by a non-singleton bad interval `[u, v]` falls into one
of two regimes, according to whether some element of `[u, v]` is divisible by
`P²`, where `P` is the largest prime factor of `∏_{i=u}^{v} i`:

* **Type 1** (`InType1BadInterval`): the interval contains a `P²`-multiple.
* **Type 2** (`InType2BadInterval`): no element of the interval is divisible
  by `P²` (then `P ≤ v - u` by `bad_interval_largestPrimeFactor_le_sub` in
  `JSP314.Type2Run`).

This file defines the associated counting functions `type1Count`/`type2Count`,
proves the pointwise dichotomy `nonSingleton_iff_type1_or_type2` and the
counting bound `badNonSingletonCount x ≤ type1Count x + type2Count x`
(mimicking `B_le_badSingletonCount_add_badNonSingletonCount` in
`JSP314/Main.lean`), and records the search-space bound coming from
`JSP314.Squeeze`: a non-singleton bad interval containing `n` lies inside
`[u, 2n - 2]`, i.e. `v ≤ 2n - 2` (`bad_interval_v_le_two_mul_sub_two`,
`bad_interval_mem_le`, `bad_interval_v_le_two_mul`,
`inNonSingletonBadInterval_exists_bounded`).
-/

namespace JSP314

open Classical

/-- `n` is covered by a *type-1* non-singleton bad interval `[u, v]`: one
containing an element `m` divisible by `P²`, where `P` is the largest prime
factor of the interval product `∏_{i=u}^{v} i`. -/
def InType1BadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
    ∃ m ∈ Finset.Icc u v,
      (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m

/-- `n` is covered by a *type-2* non-singleton bad interval `[u, v]`: one in
which *no* element is divisible by `P²`, where `P` is the largest prime factor
of the interval product `∏_{i=u}^{v} i`. -/
def InType2BadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧
    ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m

/-- `T₁(x)`: count of `n ≤ x` covered by a type-1 non-singleton bad interval. -/
noncomputable def type1Count (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InType1BadInterval n).card

/-- `T₂(x)`: count of `n ≤ x` covered by a type-2 non-singleton bad interval. -/
noncomputable def type2Count (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InType2BadInterval n).card

/-- Pointwise dichotomy: lying in a non-singleton bad interval is equivalent to
being type-1 covered or type-2 covered, by the excluded middle on
`∃ m ∈ [u, v], P² ∣ m` for the witness interval. -/
theorem nonSingleton_iff_type1_or_type2 {n : ℕ} :
    InNonSingletonBadInterval n ↔
      InType1BadInterval n ∨ InType2BadInterval n := by
  constructor
  · rintro ⟨u, v, huv, hbad, hun, hnv⟩
    by_cases h : ∃ m ∈ Finset.Icc u v,
        (largestPrimeFactor ((Finset.Icc u v).prod id)) ^ 2 ∣ m
    · exact Or.inl ⟨u, v, huv, hbad, hun, hnv, h⟩
    · push_neg at h
      exact Or.inr ⟨u, v, huv, hbad, hun, hnv, h⟩
  · rintro (⟨u, v, huv, hbad, hun, hnv, -⟩ | ⟨u, v, huv, hbad, hun, hnv, -⟩)
    · exact ⟨u, v, huv, hbad, hun, hnv⟩
    · exact ⟨u, v, huv, hbad, hun, hnv⟩

/-- Counting bound: `N(x) ≤ T₁(x) + T₂(x)`.  Same proof pattern as
`B_le_badSingletonCount_add_badNonSingletonCount`: the filtered set injects
into the union of the two type filters, then `Finset.card_union_le`. -/
theorem badNonSingletonCount_le_type1_add_type2 (x : ℕ) :
    badNonSingletonCount x ≤ type1Count x + type2Count x := by
  unfold badNonSingletonCount type1Count type2Count
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, hnbad⟩ := hn
  rcases (nonSingleton_iff_type1_or_type2 (n := n)).mp hnbad with h | h
  · exact Or.inl ⟨hnx, h⟩
  · exact Or.inr ⟨hnx, h⟩

/-- A non-singleton bad interval `[u, v]` containing `n` satisfies
`v ≤ 2 * n - 2`: from the squeeze lemma `v + 2 ≤ 2u` and `u ≤ n`. -/
theorem bad_interval_v_le_two_mul_sub_two {u v n : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hn : n ∈ Finset.Icc u v) : v ≤ 2 * n - 2 := by
  have hsqueeze := bad_interval_v_add_two_le hbad huv
  have hun : u ≤ n := (Finset.mem_Icc.mp hn).1
  omega

/-- Every element of a non-singleton bad interval containing `n` is at most
`2 * n - 2`. -/
theorem bad_interval_mem_le {u v n : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hn : n ∈ Finset.Icc u v) :
    ∀ m ∈ Finset.Icc u v, m ≤ 2 * n - 2 := by
  have hv := bad_interval_v_le_two_mul_sub_two hbad huv hn
  intro m hm
  have hmv : m ≤ v := (Finset.mem_Icc.mp hm).2
  omega

/-- Corollary: if `n ≤ x` lies in the non-singleton bad interval `[u, v]`,
then `v ≤ 2 * x`. -/
theorem bad_interval_v_le_two_mul {u v n x : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v) (hun : u ≤ n) (hnv : n ≤ v) (hnx : n ≤ x) : v ≤ 2 * x := by
  have hv := bad_interval_v_le_two_mul_sub_two hbad huv
    (Finset.mem_Icc.mpr ⟨hun, hnv⟩)
  omega

/-- Bounded-quantifier reformulation: a point covered by a non-singleton bad
interval is covered by one whose right endpoint is at most `2 * n - 2`.  This
bounds the interval search space for `InNonSingletonBadInterval n`. -/
theorem inNonSingletonBadInterval_exists_bounded {n : ℕ}
    (h : InNonSingletonBadInterval n) :
    ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v ∧ v ≤ 2 * n - 2 := by
  obtain ⟨u, v, huv, hbad, hun, hnv⟩ := h
  exact ⟨u, v, huv, hbad, hun, hnv,
    bad_interval_v_le_two_mul_sub_two hbad huv (Finset.mem_Icc.mpr ⟨hun, hnv⟩)⟩

end JSP314
