import JSP314.ShortLong

/-!
# JSP-000314 — sharpened short-interval reduction: smooth arcs to singletons

The pointwise covering lemma `shortBadCovered_exists_singleton` in
`JSP314.ShortLong` records only `|n - m| ≤ √(2x)`.  The truth is sharper: in a
*short* bad interval `v - u < P` (where `P` is the largest prime factor of the
interval product and `P² ∣ m` for some `m ∈ [u, v]`), every element of `[u, v]`
is `P`-smooth and `|n - m| ≤ v - u < P`.  Hence every short-covered `n` lies on
a `P(m)`-smooth arc between it and a bad singleton `m ≤ 2n`.

This file formalizes that refinement:

* `short_bad_interval_all_lpf_le` — every element of a bad interval has
  largest prime factor `≤ P` (restated from `bad_interval_forall_lpf_le`);
* `InSmoothArcToSingleton` — `n` lies on a `lpf(m)`-smooth arc with a bad
  singleton `m ≤ 2n` at distance `≤ lpf(m)`;
* `shortBadCovered_inSmoothArc` — the pointwise reduction for short bad
  intervals;
* `smoothArcCoveredCount` and `shortBadCount_le_smoothArcCoveredCount` — the
  counting version `T_short(x) ≤ T_arc(x)`;
* `badNonSingleton_interval_bound_of_arc` — the conditional bridge with the
  short component replaced by the arc component.
-/

namespace JSP314

open Classical

section SmoothArc

/-- Every element of a bad interval has largest prime factor at most the
largest prime factor `P` of the interval product.  In particular this holds in
the short regime `v - u < P`. -/
theorem short_bad_interval_all_lpf_le {u v : ℕ} (hbad : IsBadInterval u v) :
    ∀ i ∈ Finset.Icc u v,
      largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
  bad_interval_forall_lpf_le hbad

/-- `n` lies on a smooth arc to a bad singleton: there exists `m > 1` with
`(lpf m)² ∣ m` and `m ≤ 2n` such that the whole arc `Icc (min n m) (max n m)`
is `lpf m`-smooth and `|n - m| ≤ lpf m`. -/
def InSmoothArcToSingleton (n : ℕ) : Prop :=
  ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ m ≤ 2 * n ∧
    (∀ j ∈ Finset.Icc (min n m) (max n m),
      largestPrimeFactor j ≤ largestPrimeFactor m) ∧
    n ≤ m + largestPrimeFactor m ∧ m ≤ n + largestPrimeFactor m

/-- A point covered by a short bad interval lies on a `P(m)`-smooth arc to a
bad singleton `m ≤ 2n` at distance `≤ v - u < P = lpf m`. -/
theorem shortBadCovered_inSmoothArc {n : ℕ} (h : InShortBadInterval n) :
    InSmoothArcToSingleton n := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := h
  obtain ⟨m, hm, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf := sq_dvd_mem_lpf_eq hbad hm hdvd
  have hbs := sq_dvd_mem_is_bad_singleton' hbad hm hdvd
  have hnm : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
  have hmI := Finset.mem_Icc.mp hm
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  obtain ⟨h1, h2⟩ := mem_Icc_cover hnm hm
  rw [← hlpf] at hshort
  refine ⟨m, hbs.1, hbs.2, by omega, ?_, by omega, by omega⟩
  intro j hj
  have hjI : j ∈ Finset.Icc u v := by
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr
      ⟨le_trans (le_min hun hmI.1) hj1, le_trans hj2 (max_le hnv hmI.2)⟩
  calc largestPrimeFactor j
      ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
        short_bad_interval_all_lpf_le hbad j hjI
    _ = largestPrimeFactor m := hlpf.symm

/-- `smoothArcCoveredCount x`: the number of `n ≤ x` lying on a smooth arc to
a bad singleton `m ≤ 2n` (hence `m ≤ 2x`). -/
noncomputable def smoothArcCoveredCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InSmoothArcToSingleton n).card

/-- The sharpened pointwise reduction, counted:
`T_short(x) ≤ T_arc(x)`. -/
theorem shortBadCount_le_smoothArcCoveredCount (x : ℕ) :
    shortBadCount x ≤ smoothArcCoveredCount x := by
  unfold shortBadCount smoothArcCoveredCount
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, shortBadCovered_inSmoothArc hn.2⟩

end SmoothArc

/-- **Conditional bridge, arc version**: if the sum of the smooth-arc count and
the bounded smooth-run count is eventually `≤ (log x)^{-1+ε} · S(x)` for every
`ε > 0`, then so is `badNonSingletonCount`, via
`badNonSingletonCount_le_short_add_smooth` composed with
`shortBadCount_le_smoothArcCoveredCount`. -/
theorem badNonSingleton_interval_bound_of_arc
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (smoothArcCoveredCount x : ℝ) + (smoothRunCoveredCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [h ε hε] with x hx
  have hN : (badNonSingletonCount x : ℝ) ≤
      (smoothArcCoveredCount x : ℝ) + (smoothRunCoveredCount x : ℝ) := by
    have h1 := badNonSingletonCount_le_short_add_smooth x
    have h2 := shortBadCount_le_smoothArcCoveredCount x
    have h3 : badNonSingletonCount x ≤
        smoothArcCoveredCount x + smoothRunCoveredCount x := by omega
    exact_mod_cast h3
  linarith

end JSP314
