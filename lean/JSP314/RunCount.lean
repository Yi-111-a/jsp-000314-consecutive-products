import JSP314.ShortLong
import JSP314.SmoothRunBound
import JSP314.PrimeGap
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

/-!
# JSP-000314 — smooth-run coverage is trivial; composite-run coverage is not

This file records the structural facts about the *counting* problem that can be
proved without analytic input, including one genuinely surprising collapse:

* `smoothRunCovered_iff_one_le`: `smoothRunCovered n ↔ 1 ≤ n`.  Every positive
  integer `n` is covered by the trivial smooth run `[0, n]` (every `i ≤ n`
  satisfies `largestPrimeFactor i ≤ i ≤ n = n - 0`).  Consequently
  `smoothRunCoveredCount x = x` **exactly**: the smooth-run relaxation used in
  the short/long decomposition `badNonSingletonCount ≤ shortBadCount +
  smoothRunCoveredCount` is lossless — it recovers only the trivial bound.
  Any power-saving bound on `badNonSingletonCount` must therefore exploit the
  badness hypothesis `P² ∣ prod` (equivalently the dyadic squeeze
  `v + 2 ≤ 2u`), not merely `(v − u)`-smoothness.

* `smoothRun_prime_le`, `smoothRun_card_primes_le`,
  `smoothRun_card_composites_ge`: a smooth run `[u, v]` contains at most
  `π(v - u)` primes — every prime member `i` satisfies `i = lpf i ≤ v - u` —
  and hence at least `v + 1 - u - π(v - u)` composites.  In the
  *self-overlapping* regime `v < 2u` (which the bad-interval squeeze
  `v + 2 ≤ 2u` supplies) the entire run is composite
  (`smoothRun_all_composite_of_lt`).

* `inCompositeRun_two_iff`: `InCompositeRun n 2 ↔ ¬n.Prime ∧ (¬(n−1).Prime ∨
  ¬(n+1).Prime)` — composite runs of length `≥ 2` are exactly the non-isolated
  composites.  Hence `compositeRunCount` equals the count of non-isolated
  composites (`compositeRunCount_eq_nonIsolated`).

* `compositeRunLengthCount x L`: count of `n ≤ x` in a composite run of length
  `≥ L`.  Bounds: `≤ x + 1 − π(x)` (such `n` are composite), and for `n ≥ 2`
  they are exactly the points strictly inside consecutive-prime gaps of width
  `≥ L + 1` (`inCompositeRun_iff_inWidePrimeGap`).  With
  `nextPrime v` = least prime `> v` this yields
  `compositeRunLengthCount x L ≤ 2 + ∑_{p ∈ primesLE x, nextPrime p − p ≥ L+1}
  (nextPrime p − p − 1)` — the coverage count is bounded by the total length
  of wide prime gaps below `x`.
-/

namespace JSP314

open Classical

section EndpointBounds

/-- Unpacking `smoothRunCovered`: the covering run `[u, v]` satisfies
`u < v`, `u ≤ n ≤ v`, `v ≤ 2n`; moreover `n` itself is `(v - u)`-smooth
(`largestPrimeFactor n ≤ v - u`), `v - u ≤ 2n`, and `1 ≤ n` (so `n = 0` is
never covered). -/
theorem smoothRunCovered_spec {n : ℕ} (h : smoothRunCovered n) :
    ∃ u v : ℕ, u < v ∧ u ≤ n ∧ n ≤ v ∧ v ≤ 2 * n ∧
      (∀ i ∈ Finset.Icc u v, largestPrimeFactor i ≤ v - u) ∧
      largestPrimeFactor n ≤ v - u ∧ v - u ≤ 2 * n ∧ 1 ≤ n := by
  obtain ⟨u, v, hsr, hun, hnv, hv⟩ := h
  have h1n : 1 ≤ n := by
    by_contra hc
    push Not at hc
    have huv := hsr.1
    omega
  exact ⟨u, v, hsr.1, hun, hnv, hv, hsr.2,
    hsr.2 n (Finset.mem_Icc.mpr ⟨hun, hnv⟩),
    (Nat.sub_le _ _).trans hv, h1n⟩

end EndpointBounds

section Triviality

/-- For `i ≥ 1`, the largest prime factor does not exceed `i`. -/
theorem largestPrimeFactor_le_self {i : ℕ} (hi : 1 ≤ i) :
    largestPrimeFactor i ≤ i := by
  rcases Nat.lt_or_ge i 2 with h | h
  · rw [largestPrimeFactor_eq_one_iff.mpr (show i ≤ 1 by omega)]
    exact hi
  · exact Nat.le_of_dvd (by omega) (largestPrimeFactor_dvd h)

/-- `[0, v]` is a smooth run for every `v ≥ 1`: every `i ≤ v` satisfies
`largestPrimeFactor i ≤ i ≤ v = v - 0`, and `largestPrimeFactor 0 = 1 ≤ v`. -/
theorem isSmoothRun_zero {v : ℕ} (hv : 1 ≤ v) : IsSmoothRun 0 v := by
  refine ⟨by omega, fun i hi => ?_⟩
  have hI := Finset.mem_Icc.mp hi
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst i
    rw [largestPrimeFactor_eq_one_iff.mpr zero_le_one]
    omega
  · exact (largestPrimeFactor_le_self h0).trans (by omega)

/-- Every positive `n` is covered by the trivial smooth run `[0, n]`. -/
theorem smoothRunCovered_of_one_le {n : ℕ} (hn : 1 ≤ n) : smoothRunCovered n :=
  ⟨0, n, isSmoothRun_zero hn, Nat.zero_le _, le_refl _, by omega⟩

/-- **Collapse of the smooth-run predicate**: `smoothRunCovered n ↔ 1 ≤ n`.
The bounded smooth-run condition covers *every* positive integer — including
all primes — so it cannot by itself yield any saving over the trivial count. -/
theorem smoothRunCovered_iff_one_le {n : ℕ} : smoothRunCovered n ↔ 1 ≤ n := by
  refine ⟨fun h => ?_, smoothRunCovered_of_one_le⟩
  obtain ⟨u, v, hsr, hun, hnv, hv⟩ := h
  by_contra hc
  push Not at hc
  have huv := hsr.1
  omega

/-- **The smooth-run count is exactly `x`**: the relaxation used in the
short/long decomposition is lossless.  The analytic content of Ta26c lives
entirely in the badness condition, not in `(v - u)`-smoothness. -/
theorem smoothRunCoveredCount_eq (x : ℕ) : smoothRunCoveredCount x = x := by
  unfold smoothRunCoveredCount
  have hset : (Finset.range (x + 1)).filter (fun n => smoothRunCovered n)
      = Finset.Icc 1 x := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
      smoothRunCovered_iff_one_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by omega⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h1⟩
  rw [hset, Nat.card_Icc]
  omega

end Triviality

section PrimesInSmoothRuns

/-- A prime in a smooth run `[u, v]` is at most `v - u`. -/
theorem smoothRun_prime_le {u v i : ℕ} (h : IsSmoothRun u v)
    (hi : i ∈ Finset.Icc u v) (hp : i.Prime) : i ≤ v - u := by
  have hle := h.2 i hi
  rwa [largestPrimeFactor_eq_self_of_prime hp] at hle

/-- A smooth run `[u, v]` contains at most `π (v - u)` primes. -/
theorem smoothRun_card_primes_le {u v : ℕ} (h : IsSmoothRun u v) :
    ((Finset.Icc u v).filter Nat.Prime).card ≤ Nat.primeCounting (v - u) := by
  have hsub : (Finset.Icc u v).filter Nat.Prime ⊆ Nat.primesLE (v - u) := by
    intro i hi
    obtain ⟨hmem, hp⟩ := Finset.mem_filter.mp hi
    exact Nat.mem_primesLE.mpr ⟨smoothRun_prime_le h hmem hp, hp⟩
  exact (Finset.card_le_card hsub).trans
    (le_of_eq (Nat.primesLE_card_eq_primeCounting (v - u)))

/-- Hence a smooth run `[u, v]` contains at least `v + 1 - u - π(v - u)`
non-prime (composite or `≤ 1`) elements. -/
theorem smoothRun_card_composites_ge {u v : ℕ} (h : IsSmoothRun u v) :
    v + 1 - u - Nat.primeCounting (v - u) ≤
      ((Finset.Icc u v).filter fun i => ¬ i.Prime).card := by
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.Icc u v)
    Nat.Prime
  rw [Nat.card_Icc] at hcard
  have hπ := smoothRun_card_primes_le h
  omega

/-- **Self-overlapping smooth runs are composite runs**: if `v < 2u`
(equivalently `v - u < u`), every element of `[u, v]` exceeds the smoothness
bound `v - u`, so no element can be prime.  For long bad intervals the squeeze
`v + 2 ≤ 2u` supplies exactly this hypothesis. -/
theorem smoothRun_all_composite_of_lt {u v : ℕ} (h : IsSmoothRun u v)
    (h2 : v < 2 * u) : ∀ i ∈ Finset.Icc u v, ¬ i.Prime := by
  intro i hi hp
  have hI := Finset.mem_Icc.mp hi
  exact smoothRun_not_prime h hi (by omega) hp

/-- A point of a self-overlapping smooth run lies in a composite run of length
`v + 1 - u`. -/
theorem inCompositeRun_of_smoothRun_selfoverlap {n u v : ℕ}
    (h : IsSmoothRun u v) (h2 : v < 2 * u) (hun : u ≤ n) (hnv : n ≤ v) :
    InCompositeRun n (v + 1 - u) :=
  ⟨u, v, le_refl _, smoothRun_all_composite_of_lt h h2, hun, hnv⟩

/-- Any point covered by a self-overlapping smooth run lies in a composite run
of length at least `2`.  This is the regime actually reached by long bad
intervals. -/
theorem inCompositeRun_two_of_selfoverlap {n : ℕ}
    (h : ∃ u v, IsSmoothRun u v ∧ u ≤ n ∧ n ≤ v ∧ v < 2 * u) :
    InCompositeRun n 2 := by
  obtain ⟨u, v, ⟨huv, hsm⟩, hun, hnv, hlt⟩ := h
  exact ⟨u, v, by omega, smoothRun_all_composite_of_lt ⟨huv, hsm⟩ hlt, hun, hnv⟩

end PrimesInSmoothRuns

section CompositeRunCounts

/-- `InCompositeRun` is antitone in the length parameter. -/
theorem inCompositeRun_mono {n L M : ℕ} (h : InCompositeRun n L) (hLM : M ≤ L) :
    InCompositeRun n M := by
  obtain ⟨u, v, hlen, hcomp, hun, hnv⟩ := h
  exact ⟨u, v, hLM.trans hlen, hcomp, hun, hnv⟩

/-- A composite run of length `≥ 2` through `n` reaches a neighbor of `n`:
`n - 1` or `n + 1` is composite. -/
theorem inCompositeRun_adjacent {n L : ℕ} (h : InCompositeRun n L)
    (hL : 2 ≤ L) : ¬ Nat.Prime (n - 1) ∨ ¬ Nat.Prime (n + 1) := by
  obtain ⟨u, v, hlen, hcomp, hun, hnv⟩ := h
  rcases Nat.lt_or_ge u n with hlt | hge
  · exact Or.inl (hcomp (n - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  · exact Or.inr (hcomp (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

/-- Conversely, a composite `n` with a composite neighbor lies in a composite
run of length `2`. -/
theorem inCompositeRun_two_iff {n : ℕ} :
    InCompositeRun n 2 ↔
      ¬ n.Prime ∧ (¬ (n - 1).Prime ∨ ¬ (n + 1).Prime) := by
  refine ⟨fun h => ⟨inCompositeRun_not_prime h,
    inCompositeRun_adjacent h (le_refl 2)⟩, ?_⟩
  rintro ⟨hn, h | h⟩
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst n
      refine ⟨0, 1, by norm_num, ?_, le_refl _, by norm_num⟩
      intro i hi
      have hI := Finset.mem_Icc.mp hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact h
      · exact Nat.not_prime_one
    · refine ⟨n - 1, n, by omega, ?_, by omega, le_refl n⟩
      intro i hi
      have hI := Finset.mem_Icc.mp hi
      rcases (by omega : i = n - 1 ∨ i = n) with rfl | rfl
      · exact h
      · exact hn
  · refine ⟨n, n + 1, by omega, ?_, le_refl n, by omega⟩
    intro i hi
    have hI := Finset.mem_Icc.mp hi
    rcases (by omega : i = n ∨ i = n + 1) with rfl | rfl
    · exact hn
    · exact h

/-- Count of `n ≤ x` lying in a composite run of length at least `L`. -/
noncomputable def compositeRunLengthCount (x L : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InCompositeRun n L).card

/-- `compositeRunLengthCount` is antitone in `L`. -/
theorem compositeRunLengthCount_anti {L M : ℕ} (hLM : M ≤ L) (x : ℕ) :
    compositeRunLengthCount x L ≤ compositeRunLengthCount x M := by
  unfold compositeRunLengthCount
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, inCompositeRun_mono hn.2 hLM⟩

/-- `compositeRunCount` is the `L = 2` case of `compositeRunLengthCount`. -/
theorem compositeRunCount_eq_compositeRunLengthCount (x : ℕ) :
    compositeRunCount x = compositeRunLengthCount x 2 := rfl

/-- Points covered by composite runs are composite, hence the count is bounded
by the number of non-primes below `x + 1`. -/
theorem compositeRunLengthCount_le_not_prime (x L : ℕ) :
    compositeRunLengthCount x L ≤
      ((Finset.range (x + 1)).filter fun n => ¬ Nat.Prime n).card := by
  unfold compositeRunLengthCount
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, inCompositeRun_not_prime hn.2⟩

/-- The number of non-primes in `range (x + 1)` is `x + 1 - π(x)`. -/
theorem card_not_prime_range (x : ℕ) :
    ((Finset.range (x + 1)).filter fun n => ¬ Nat.Prime n).card =
      x + 1 - Nat.primeCounting x := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (x + 1))
    Nat.Prime
  rw [← Nat.primesLE_eq_filter_range x, Nat.primesLE_card_eq_primeCounting,
    Finset.card_range] at h
  omega

/-- **First quantitative bound**: at most `x + 1 - π(x)` points `n ≤ x` lie in
a composite run of length `≥ L` — a genuine `π(x)` saving over the trivial
`x + 1`. -/
theorem compositeRunLengthCount_le (x L : ℕ) :
    compositeRunLengthCount x L ≤ x + 1 - Nat.primeCounting x :=
  (compositeRunLengthCount_le_not_prime x L).trans
    (le_of_eq (card_not_prime_range x))

/-- The `L = 2` case: `compositeRunCount x ≤ x + 1 - π(x)`. -/
theorem compositeRunCount_le (x : ℕ) :
    compositeRunCount x ≤ x + 1 - Nat.primeCounting x :=
  compositeRunLengthCount_le x 2

/-- Count of `n ≤ x` that are composite with at least one composite neighbor
(i.e. non-isolated composites). -/
noncomputable def nonIsolatedCompositeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n =>
    ¬ Nat.Prime n ∧ (¬ Nat.Prime (n - 1) ∨ ¬ Nat.Prime (n + 1))).card

/-- **Exact count**: `compositeRunCount x` equals the number of non-isolated
composite `n ≤ x`. -/
theorem compositeRunCount_eq_nonIsolated (x : ℕ) :
    compositeRunCount x = nonIsolatedCompositeCount x := by
  unfold compositeRunCount nonIsolatedCompositeCount
  congr 1
  apply Finset.filter_congr
  intro n _
  exact inCompositeRun_two_iff

theorem nonIsolatedCompositeCount_le (x : ℕ) :
    nonIsolatedCompositeCount x ≤ x + 1 - Nat.primeCounting x := by
  unfold nonIsolatedCompositeCount
  refine (Finset.card_le_card ?_).trans (le_of_eq (card_not_prime_range x))
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.1⟩

end CompositeRunCounts

section PrimeGapStructure

/-- Some prime exceeds `v` (Euclid). -/
theorem exists_prime_gt (v : ℕ) : ∃ q : ℕ, v < q ∧ q.Prime := by
  obtain ⟨Q, hQge, hQprime⟩ := Nat.exists_infinite_primes (v + 1)
  exact ⟨Q, by omega, hQprime⟩

/-- `nextPrime v` is the least prime strictly exceeding `v`. -/
noncomputable def nextPrime (v : ℕ) : ℕ := Nat.find (exists_prime_gt v)

theorem nextPrime_spec (v : ℕ) : v < nextPrime v ∧ (nextPrime v).Prime :=
  Nat.find_spec (exists_prime_gt v)

theorem nextPrime_lt (v : ℕ) : v < nextPrime v := (nextPrime_spec v).1

theorem nextPrime_prime (v : ℕ) : (nextPrime v).Prime := (nextPrime_spec v).2

/-- `nextPrime v` is the *least* prime exceeding `v`. -/
theorem nextPrime_min {v r : ℕ} (hr : v < r) (hrr : r.Prime) :
    nextPrime v ≤ r :=
  Nat.find_min' (exists_prime_gt v) ⟨hr, hrr⟩

/-- If `p < q` are primes with no prime strictly between, then `q` is the
least prime exceeding `p`: `nextPrime p = q`. -/
theorem nextPrime_eq_of_gap {p q : ℕ} (_hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hconsec : ∀ r : ℕ, p < r → r < q → ¬ r.Prime) :
    nextPrime p = q := by
  apply le_antisymm (nextPrime_min hpq hq)
  obtain ⟨hlt, hpr⟩ := nextPrime_spec p
  by_contra hc
  push Not at hc
  exact hconsec _ hlt hc hpr

/-- `n` lies strictly inside a gap between consecutive primes `p < q` of width
`≥ L + 1` (i.e. a prime-free interval containing `≥ L` integers). -/
def InWidePrimeGap (n L : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ∧ n < q ∧ L + 1 ≤ q - p ∧
    ∀ r : ℕ, p < r → r < q → ¬ r.Prime

/-- Points strictly inside a prime gap are composite. -/
theorem inWidePrimeGap_not_prime {n L : ℕ} (h : InWidePrimeGap n L) :
    ¬ n.Prime := by
  obtain ⟨p, q, -, -, hpn, hnq, -, hconsec⟩ := h
  exact hconsec n hpn hnq

/-- **Composite runs live inside prime gaps**: a composite run of length
`≥ L` containing `n ≥ 2` sits strictly inside a consecutive-prime gap
`(p, q)` with `q - p ≥ L + 1`.  The prime `p` is the greatest prime `< u`
(which exists since `u ≥ 4`) and `q = nextPrime v`. -/
theorem inCompositeRun_inWidePrimeGap {n L : ℕ} (hn : 2 ≤ n)
    (h : InCompositeRun n L) : InWidePrimeGap n L := by
  obtain ⟨u, v, hlen, hcomp, hun, hnv⟩ := h
  have hu2 : 2 ≤ u := by
    by_contra hc
    push Not at hc
    exact hcomp 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) Nat.prime_two
  have hu4 : 4 ≤ u := by
    have huc := hcomp u (Finset.mem_Icc.mpr ⟨le_refl u, by omega⟩)
    rcases (by omega : u = 2 ∨ u = 3 ∨ 4 ≤ u) with rfl | rfl | h4
    · exact absurd Nat.prime_two huc
    · exact absurd Nat.prime_three huc
    · exact h4
  set p := Nat.findGreatest Nat.Prime (u - 1) with hp_def
  have hpprime : p.Prime :=
    Nat.findGreatest_spec (show 2 ≤ u - 1 by omega) Nat.prime_two
  have hpu : p ≤ u - 1 := Nat.findGreatest_le (u - 1)
  have hpgt : ∀ r : ℕ, r.Prime → r ≤ u - 1 → r ≤ p :=
    fun r hrr hru => Nat.le_findGreatest hru hrr
  have hnp : v < nextPrime v := nextPrime_lt v
  refine ⟨p, nextPrime v, hpprime, nextPrime_prime v, by omega, by omega, ?_, ?_⟩
  · omega
  · intro r hpr hrq hrr
    have hrv : r ≤ v := by
      by_contra hc
      push Not at hc
      exact Nat.find_min (exists_prime_gt v) hrq ⟨hc, hrr⟩
    have hru : u ≤ r := by
      by_contra hc
      push Not at hc
      have : r ≤ p := hpgt r hrr (by omega)
      omega
    exact hcomp r (Finset.mem_Icc.mpr ⟨hru, hrv⟩) hrr

/-- Conversely, the open interval `(p, q)` between consecutive primes is a
composite run of length `q - p - 1`; if `q - p ≥ L + 1` it witnesses
`InCompositeRun n L` for each of its members. -/
theorem inWidePrimeGap_inCompositeRun {n L : ℕ} (h : InWidePrimeGap n L) :
    InCompositeRun n L := by
  obtain ⟨p, q, hp, hq, hpn, hnq, hwidth, hconsec⟩ := h
  refine ⟨p + 1, q - 1, ?_, ?_, by omega, by omega⟩
  · omega
  · intro i hi
    have hI := Finset.mem_Icc.mp hi
    exact hconsec i (by omega) (by omega)

/-- For `n ≥ 2`, lying in a composite run of length `≥ L` is exactly lying
inside a consecutive-prime gap of width `≥ L + 1`. -/
theorem inCompositeRun_iff_inWidePrimeGap {n L : ℕ} (hn : 2 ≤ n) :
    InCompositeRun n L ↔ InWidePrimeGap n L :=
  ⟨inCompositeRun_inWidePrimeGap hn, inWidePrimeGap_inCompositeRun⟩

/-- A composite run through `n ≤ 1` has length at most `2` (it is a subset of
`{0, 1}`, since `2` is prime). -/
theorem inCompositeRun_le_two_of_le_one {n L : ℕ} (hn : n ≤ 1)
    (h : InCompositeRun n L) : L ≤ 2 := by
  obtain ⟨u, v, hlen, hcomp, hun, hnv⟩ := h
  have hv1 : v ≤ 1 := by
    by_contra hc
    push Not at hc
    exact hcomp 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) Nat.prime_two
  omega

/-- Count of `n ≤ x` lying strictly inside a consecutive-prime gap of width
`≥ L + 1`. -/
noncomputable def widePrimeGapCount (x L : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InWidePrimeGap n L).card

theorem widePrimeGapCount_le_not_prime (x L : ℕ) :
    widePrimeGapCount x L ≤
      ((Finset.range (x + 1)).filter fun n => ¬ Nat.Prime n).card := by
  unfold widePrimeGapCount
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, inWidePrimeGap_not_prime hn.2⟩

/-- `widePrimeGapCount x L ≤ x + 1 - π(x)`: points in wide prime gaps are
composite. -/
theorem widePrimeGapCount_le (x L : ℕ) :
    widePrimeGapCount x L ≤ x + 1 - Nat.primeCounting x :=
  (widePrimeGapCount_le_not_prime x L).trans
    (le_of_eq (card_not_prime_range x))

/-- **Prime-gap covering bound**: points `n ≤ x` in a composite run of length
`≥ L` are, apart from the two exceptional points `n ≤ 1`, exactly the points
inside wide prime gaps. -/
theorem compositeRunLengthCount_le_widePrimeGapCount_add_two (x L : ℕ) :
    compositeRunLengthCount x L ≤ widePrimeGapCount x L + 2 := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InCompositeRun n L) ⊆
      ((Finset.range (x + 1)).filter fun n => InWidePrimeGap n L) ∪ {0, 1} := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · rw [Finset.mem_union]
      right
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    · rw [Finset.mem_union]
      left
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hn.1, inCompositeRun_inWidePrimeGap hge hn.2⟩
  have hcard : (((Finset.range (x + 1)).filter fun n => InWidePrimeGap n L) ∪
      ({0, 1} : Finset ℕ)).card ≤ widePrimeGapCount x L + 2 := by
    refine (Finset.card_union_le _ _).trans ?_
    have h2 : ({0, 1} : Finset ℕ).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr (by norm_num)
    rw [h2]
    unfold widePrimeGapCount
    exact le_rfl
  unfold compositeRunLengthCount
  exact (Finset.card_le_card hsub).trans hcard

/-- For `L ≥ 3` the exceptional points `n ≤ 1` cannot occur, so the bound is
clean: `compositeRunLengthCount x L ≤ widePrimeGapCount x L`. -/
theorem compositeRunLengthCount_le_widePrimeGapCount {x L : ℕ} (hL : 3 ≤ L) :
    compositeRunLengthCount x L ≤ widePrimeGapCount x L := by
  unfold compositeRunLengthCount widePrimeGapCount
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · exfalso
    have hle := inCompositeRun_le_two_of_le_one (by omega) hn.2
    omega
  · exact inCompositeRun_inWidePrimeGap hge hn.2

/-- **Gap-length sum bound**: the number of `n ≤ x` lying inside
consecutive-prime gaps of width `≥ L + 1` is at most the total length
`∑ (nextPrime p - p - 1)` of those gaps: each such `n` lies in
`[p + 1, nextPrime p - 1]` for a unique bounding prime `p ≤ x`. -/
theorem widePrimeGapCount_le_sum (x L : ℕ) :
    widePrimeGapCount x L ≤
      ∑ p ∈ ((Nat.primesLE x).filter fun p => L + 1 ≤ nextPrime p - p),
        (nextPrime p - p - 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InWidePrimeGap n L) ⊆
      ((Nat.primesLE x).filter fun p => L + 1 ≤ nextPrime p - p).biUnion
        (fun p => Finset.Icc (p + 1) (nextPrime p - 1)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, p, q, hp, hq, hpn, hnq, hw, hconsec⟩ := hn
    have hqeq : nextPrime p = q :=
      nextPrime_eq_of_gap hp hq (by omega) hconsec
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, ?_⟩
    · rw [Finset.mem_filter, Nat.mem_primesLE]
      refine ⟨⟨by omega, hp⟩, ?_⟩
      rw [hqeq]
      exact hw
    · rw [Finset.mem_Icc]
      omega
  unfold widePrimeGapCount
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro p _hp
  rw [Nat.card_Icc]
  have hpgt : p < nextPrime p := nextPrime_lt p
  omega

/-- Combined bound: `compositeRunLengthCount x L` is at most `2` plus the total
length of the wide prime gaps below `x`. -/
theorem compositeRunLengthCount_le_sum_add_two (x L : ℕ) :
    compositeRunLengthCount x L ≤
      (∑ p ∈ ((Nat.primesLE x).filter fun p => L + 1 ≤ nextPrime p - p),
        (nextPrime p - p - 1)) + 2 :=
  (compositeRunLengthCount_le_widePrimeGapCount_add_two x L).trans
    (Nat.add_le_add_right (widePrimeGapCount_le_sum x L) 2)

/-- The `L = 3` clean version: no `+ 2`. -/
theorem compositeRunLengthCount_le_sum {x L : ℕ} (hL : 3 ≤ L) :
    compositeRunLengthCount x L ≤
      ∑ p ∈ ((Nat.primesLE x).filter fun p => L + 1 ≤ nextPrime p - p),
        (nextPrime p - p - 1) :=
  (compositeRunLengthCount_le_widePrimeGapCount hL).trans
    (widePrimeGapCount_le_sum x L)

/-- Consequence for the bad-interval problem: the non-singleton bad count is
bounded by the short component plus the number of composites `≤ x`. -/
theorem badNonSingletonCount_le_short_add_composites (x : ℕ) :
    badNonSingletonCount x ≤
      shortBadCount x + (x + 1 - Nat.primeCounting x) :=
  (badNonSingletonCount_le_short_add_compositeRun x).trans
    (Nat.add_le_add_left (compositeRunCount_le x) _)

/-- `longBadCount x ≤ x + 1 - π(x)`: points covered by long bad intervals are
composite. -/
theorem longBadCount_le (x : ℕ) :
    longBadCount x ≤ x + 1 - Nat.primeCounting x :=
  (longBadCount_le_compositeRunCount x).trans (compositeRunCount_le x)

end PrimeGapStructure

end JSP314
