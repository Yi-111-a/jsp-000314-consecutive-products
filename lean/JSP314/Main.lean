import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Linarith
import JSP314.Defs
import JSP314.Bounds

/-!
# JSP-000314 — Tao consecutive-products / bad-interval asymptotic (Ta26c)

Erdős–Graham conjecture (Tao, Ta26c, arXiv:2603.27990):
`B(x) = (1 + O((log x)^{-1+o(1)})) · S(x)`, where `B x` counts `n ≤ x` lying in
some "bad" interval `[u,v]` (the product `∏_{i=u}^v i` is divisible by the square
of its largest prime factor) and `badSingletonCount x` counts `n ≤ x` with
`P(n)^2 ∣ n`.

The definitions `largestPrimeFactor`, `IsBadInterval`, `B`, `badSingletonCount`
live in `JSP314/Defs.lean`; elementary bounds (`badSingletonCount_le_B`,
`B_le`, `isBadInterval_self_iff`) live in `JSP314/Bounds.lean`.

## Structure of this file

* `InNonSingletonBadInterval`, `badNonSingletonCount`: points `n` covered by a
  bad interval of length `≥ 2`.
* `B_le_badSingletonCount_add_badNonSingletonCount`: **proved** combinatorial
  reduction — every `n ≤ x` in a bad interval is either itself a bad singleton
  or lies in a non-singleton bad interval. Hence `B ≤ S + N`.
* `badNonSingleton_interval_bound`: the **hard analytic core** of Ta26c
  (`N(x) ≤ (log x)^{-1+ε} · S(x)`). This is the deep content of the paper and is
  left as a single unproved placeholder, clearly marked.
* `bad_interval_excess_bound`: proved from the two previous items.
* `bad_interval_count_asymptotic`: the headline theorem, proved in full modulo
  `badNonSingleton_interval_bound` (the absolute value is removed via
  `badSingletonCount_le_B`, so `|B - S| = B - S`).
-/

namespace JSP314

open Nat Filter Classical

/-- `n` lies in some bad interval `[u,v]` with `u < v` (length `≥ 2`). -/
def InNonSingletonBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u < v ∧ IsBadInterval u v ∧ u ≤ n ∧ n ≤ v

/-- `N(x)`: count of `n ≤ x` lying in a non-singleton bad interval. -/
noncomputable def badNonSingletonCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InNonSingletonBadInterval n).card

/-- Combinatorial reduction: `B(x) ≤ S(x) + N(x)`.

If `n ≤ x` belongs to a bad interval `[u,v]`, then either `u = v` — which forces
`u = v = n`, so `n` itself is a bad singleton by `isBadInterval_self_iff` — or
`u < v`, so `n` lies in a non-singleton bad interval. -/
theorem B_le_badSingletonCount_add_badNonSingletonCount (x : ℕ) :
    B x ≤ badSingletonCount x + badNonSingletonCount x := by
  unfold B badSingletonCount badNonSingletonCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, u, v, hbad, hun, hnv⟩ := hn
  rcases eq_or_lt_of_le hbad.1 with huv | huv
  · -- `u = v`; together with `u ≤ n ≤ v` this gives `u = v = n`,
    -- so `n` itself is a bad singleton.
    refine Or.inl ⟨hnx, ?_⟩
    subst v -- eliminates `v` using `huv : u = v`
    obtain rfl : n = u := le_antisymm hnv hun
    exact isBadInterval_self_iff.mp hbad
  · -- `u < v`: a non-singleton bad interval covering `n`.
    exact Or.inr ⟨hnx, u, v, huv, hbad, hun, hnv⟩

/-- **Hard analytic core of Ta26c (single unproved placeholder).**

Non-singleton bad intervals cover at most `(log x)^{-1+ε} · S(x)` points `n ≤ x`,
eventually in `x`. This is the deep estimate of Tao's resolution of the
Erdős–Graham conjecture: every element of a bad interval `[u,v]` (`u < v`) with
largest prime factor `p` either lies at distance `≤ x/p`-controlled positions
from a multiple of `p²`, or the interval has length `≥ p`; the full argument
(fourier-analytic / combinatorial decomposition of Ta26c) shows these points are
`o((log x)^{-1+ε})`-dense relative to the singleton count `S(x)`.

No placeholder is spread elsewhere: the entire remaining mathematical content of
the conjecture is isolated in this one lemma. -/
theorem badNonSingleton_interval_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  -- Honest attempt log (no elementary proof exists — this is the ~50-page
  -- analytic core of Ta26c).  Dead ends checked:
  --
  -- * Trivial bound `badNonSingletonCount x ≤ x + 1` (subset of `range (x+1)`):
  --   insufficient.  The RHS is `(log x)^{-1+ε} · S(x) = o(S(x))`, and
  --   `S(x) = o(x)`, so `N ≤ x+1` is larger than the target by a factor
  --   diverging to `∞`.  One needs `N(x)/S(x) → 0` at a polylogarithmic rate.
  --
  -- * Vacuity/false-premises shortcuts: impossible.  The interval `[8,9]` is
  --   bad (product `72`, `P = 3`, `3² ∣ 72`), so `N(x) ≥ 2` for all `x ≥ 9`
  --   (proved in `JSP314.AnalyticCore`), and the RHS genuinely tends to `∞`
  --   because `S(x) ≥ π(√x) → ∞`
  --   (`JSP314.Counting.badSingletonCount_ge_primeCounting`).  The claim is a
  --   real asymptotic between two diverging counts.
  --
  -- * Covering bound `JSP314.Covering.covered_by_short_type1_interval_card_le`:
  --   points covered by short type-1 intervals are `≤ S(x+L)·(2L+1)` — a
  --   *constant* factor `2L+1 ≥ 1` over `S`, already exceeding the required
  --   vanishing factor `(log x)^{-1+ε}`.  Beating it needs Tao's refined
  --   length-scale decomposition, not the union bound.
  --
  -- * Dichotomy `JSP314.Dichotomy.bad_interval_sq_multiple_or_long`: splits
  --   each non-singleton bad interval into "contains a `P²` multiple" (the
  --   covered case above) or "`P ≤ v - u`" (long intervals).  The long branch
  --   has no elementary counting bound — every `n` trivially lies in
  --   `p`-smooth runs of length `≥ p`; only the badness constraint
  --   `P² ∣ prod` makes the condition rare, which is the deep input.
  sorry

/-- The excess `B(x) - S(x)` is `≤ (log x)^{-1+ε} · S(x)`, eventually in `x`.
Proved from `B ≤ S + N` (combinatorial) + `badNonSingleton_interval_bound`
(analytic core). -/
theorem bad_interval_excess_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      (B x : ℝ) - (badSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [badNonSingleton_interval_bound ε hε] with x hx
  have hB : (B x : ℝ) ≤ badSingletonCount x + badNonSingletonCount x := by
    exact_mod_cast B_le_badSingletonCount_add_badNonSingletonCount x
  linarith

/-- Ta26c full asymptotic: `|B(x) - S(x)| ≤ (log x)^{-1+ε} · S(x)` eventually.

Since every bad singleton `n` yields the bad interval `[n,n]`
(`badSingletonCount_le_B` from `JSP314.Bounds`), `S ≤ B` pointwise, so the
absolute value is `B - S` and the claim reduces to `bad_interval_excess_bound`.
The only unproved input is the single analytic core lemma
`badNonSingleton_interval_bound`. -/
theorem bad_interval_count_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop,
      |(B x : ℝ) - (badSingletonCount x : ℝ)| ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [bad_interval_excess_bound ε hε] with x hx
  have hle : (badSingletonCount x : ℝ) ≤ B x := by
    exact_mod_cast badSingletonCount_le_B x
  rwa [abs_of_nonneg (sub_nonneg.mpr hle)]

end JSP314
