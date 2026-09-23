import JSP314.ShortLong
import JSP314.SmoothRunBound
import JSP314.RunCount
import JSP314.PrimeGap
import JSP314.Squeeze2
import JSP314.SylvesterSchur
import JSP314.SmoothLB
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

/-!
# JSP-000314 — Assault 5: the Sylvester–Schur-witness decomposition

A fresh attack on the residual analytic core `badNonSingleton_interval_bound`
(`JSP314.Main`, the sole unproved hypothesis of the project).

## The new decomposition proved here

A point `n` covered by a *long* non-singleton bad interval `[u, v]`
(`P = largestPrimeFactor (∏ [u,v]) ≤ v - u`) lies on a run of `L = v - u + 1`
consecutive integers `a, …, a + L - 1` with `a = u > L` (the dyadic squeeze
`v + 2 ≤ 2u`), all of whose elements have `largestPrimeFactor ≤ L`.  In other
words the run is a **Sylvester–Schur failure**: no element of the run is
divisible by a prime `> L`.

We isolate such points with the predicate `ssWitness n` and prove, with no
unproved hypotheses:

* `quadRegimeOpen_or_exists_prime_dvd_choose` — the case split of
  `SylvesterSchur.exists_prime_dvd_choose` with the residual branch kept as
  data: for `1 ≤ k`, `2k ≤ n`, either `QuadRegimeOpen n k` holds or `C(n,k)`
  has a prime divisor `> k`.
* `quadRegimeOpen_of_not_sylvesterSchur` — a Sylvester–Schur failure
  `(a, L)` with `L < a` lands in the residual quadratic regime:
  `QuadRegimeOpen (a + L - 1) L`, i.e. `38 ≤ L` and `a + L - 1 ≤ L²`.
* `inLongBadInterval_ssWitness` — every long-bad-covered point is an
  ssWitness point.
* `ssWitness_inCompositeRun_sqrt` — an ssWitness point `n` lies in a
  composite run of length `≥ √n` (since `n ≤ a + L - 1 ≤ L²` and the run is
  automatically composite: an element `> L` with `largestPrimeFactor ≤ L`
  cannot be prime).  Hence `ssWitness_inWidePrimeGap`: `n` sits strictly
  inside a consecutive-prime gap of width `≥ √n + 1`.
* `badNonSingletonCount_le_short_add_ssWitness` — the counting bound
  `N(x) ≤ T_short(x) + T_wit(x)`.
* `ssWitnessCount_le_deepGapCount`, `deepGapCount_le_sum` — chaining to the
  headline elementary bound

    `N(x) ≤ T_short(x) + Σ_{p ≤ x, nextPrime p − p ≥ √p + 1} (nextPrime p − p − 1)`,

  i.e. the residual is bounded by the total length of prime gaps that are
  wider than the square root of their location.  (Conjecturally no such gaps
  exist at all — Cramér's model gives `g(p) ≍ log² p` — but proving
  `g(p) < √p` or any `o(x)` bound on this sum is far beyond current Mathlib.)

## Conditional closures proved here

* `badNonSingleton_interval_bound_of_short_and_quad`: the target follows
  from the quadratic-regime hypothesis `hquad` (which kills `T_wit`
  entirely: `ssWitnessCount_eq_zero`) plus the short-interval estimate
  `T_short(x) ≤ (log x)^{-1+ε}·S(x)`.  This sharpens
  `badNonSingleton_interval_bound_of_sylvesterSchur_short` by isolating the
  *only* missing case of Sylvester–Schur.
* `badNonSingleton_interval_bound_of_short_and_witness`: unconditional
  two-component reduction `T_short + T_wit ≤ (log)^{-1+ε}·S` ⇒ target.
* `badNonSingleton_interval_bound_of_power_saving_83`: using the **proved**
  singleton lower bound `S(x) ≥ c·x^{83/100}/log⁵x` of `SmoothLB`, the
  target follows from any bound `N(x) ≤ C·x^{1−δ}` with `δ > 17/100`.

## Exactly which hypotheses are missing

The theorem `badNonSingleton_interval_bound'` (same statement as
`badNonSingleton_interval_bound` in `Main.lean`) is *not* proved here.  The
analysis above shows the missing input is the conjunction of two facts:

1. `QuadRegimeOpen` — the residual quadratic regime of Sylvester–Schur
   (`38 ≤ k`, `2k+2 ≤ n ≤ k²` ⇒ `∃ q > k` prime dividing `C(n,k)`).  This
   is Erdős's 1934 argument via the iterated primorial bound
   `∏_j θ(n^{1/j}) ≤ 4^{k+O(√n)}`; the analytic scaffolding exists in
   `QuadRegime.lean`/`QuadMertens.lean`/`QuadEasy.lean` but the key strict
   inequality `(2k+1)(2k)^k·∏_{p≤k} p^{⌊log_p n⌋} < 4^k n^k` is not yet
   proved across the whole regime.  Equivalently, and more weakly, one could
   bound the ssWitness/gap-sum term `Σ_{p ≤ x, g(p) ≥ √p+1} (g(p) − 1)` —
   which is in reality *zero* — by `o(x)` or `x^{1−δ}`.
2. The short-interval estimate `T_short(x) ≤ (log x)^{-1+ε}·S(x)` — the
   genuinely deep analytic content of Ta26c (Tao's ~50-page argument).
   Known partial bounds: `T_short ≤ T_arc = O(x log x)`
   (`ArcCount.smoothArcCoveredCount_le_log_bound`), and per-singleton radius
   `√m` (`Assault.shortBadCount_le_sum_sqrt`); both fall short of
   `(log)^{-1+ε}·S`, and every elementary relaxation
   (`x + 1 − π(x)`, `x`, prime-gap-length sums) is linear or worse.

Alternatively, via `badNonSingleton_interval_bound_of_power_saving_83`, a
single power-saving bound `N(x) ≤ C·x^{1−δ}` for some `δ > 17/100` would
suffice in place of both.
-/

namespace JSP314

open Filter Classical

section Dichotomy

/-- **Sylvester–Schur dichotomy** (the case split of
`SylvesterSchur.exists_prime_dvd_choose` with the residual branch kept as
data): for `1 ≤ k` and `2k ≤ n`, either `(n, k)` lies in the residual
quadratic regime `QuadRegimeOpen` (`38 ≤ k`, `2k + 2 ≤ n ≤ k²`) or `C(n,k)`
has a prime divisor `> k`. -/
theorem quadRegimeOpen_or_exists_prime_dvd_choose {n k : ℕ} (hk : 1 ≤ k)
    (h2k : 2 * k ≤ n) :
    _root_.SylvesterSchur.QuadRegimeOpen n k ∨
      ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have hkn : k ≤ n := by omega
  rcases lt_or_ge n (2 * k + 2) with hn | hn
  · exact Or.inr
      (_root_.SylvesterSchur.exists_prime_dvd_choose_of_le hk h2k (by omega))
  · rcases le_or_gt 38 k with hk38 | hk37
    · rcases le_or_gt n (k ^ 2) with hsq | hsq
      · exact Or.inl ⟨hk38, hn, hsq⟩
      · exact Or.inr
          (_root_.SylvesterSchur.exists_prime_dvd_choose_of_sq_lt hk hkn
            (_root_.SylvesterSchur.two_mul_primeCounting_le (by omega))
            (by omega))
    · -- `k ≤ 37`: if no large prime divides `C(n,k)`, the analytic bound
      -- forces `n ≤ 93` (`k ≤ 7`) or `n ≤ 210` (`8 ≤ k ≤ 37`), where the
      -- finite checks supply a large prime divisor — a contradiction, so
      -- this branch always yields `Or.inr`.
      by_cases hcon : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k
      · exact Or.inr hcon
      · have hall : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k :=
          fun q hq hqd => le_of_not_gt fun h2 => hcon ⟨q, hq, h2, hqd⟩
        have hb :=
          _root_.SylvesterSchur.pow_sub_le_of_forall_prime_le hk hkn hall
        rcases lt_or_ge k 8 with hk8 | hk8
        · exact absurd
            (_root_.SylvesterSchur.exists_prime_dvd_choose_small hk
              (by omega) h2k
              (_root_.SylvesterSchur.le_93_of_small hk (by omega) hb))
            hcon
        · exact absurd
            (_root_.SylvesterSchur.exists_prime_dvd_choose_mid hk
              (by omega) (by omega) h2k
              (_root_.SylvesterSchur.le_210_of_mid (by omega) (by omega) hb))
            hcon

/-- A Sylvester–Schur *failure* `¬ SylvesterSchur a L` (with `1 ≤ L < a`)
lands in the residual quadratic regime: `QuadRegimeOpen (a + L - 1) L`.
Equivalently: every Sylvester–Schur failure run has length `L ≥ 38` and ends
at `a + L - 1 ≤ L²`. -/
theorem quadRegimeOpen_of_not_sylvesterSchur {a L : ℕ} (hL : 1 ≤ L)
    (hLa : L < a) (hfail : ¬ SylvesterSchur a L) :
    _root_.SylvesterSchur.QuadRegimeOpen (a + L - 1) L := by
  rcases quadRegimeOpen_or_exists_prime_dvd_choose (k := L) (n := a + L - 1)
      hL (by omega) with hquad | ⟨q, hq, hqL, hqd⟩
  · exact hquad
  · exfalso
    obtain ⟨m, hm, hqm⟩ :=
      _root_.SylvesterSchur.exists_mem_Icc_of_prime_dvd_choose hq hqL
        (by omega : L ≤ a + L - 1) hqd
    have hm' : m ∈ Finset.Icc a (a + L - 1) := by
      have h2 := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨by omega, h2.2⟩
    exact hfail ⟨q, hq, hqL, m, hm', hqm⟩

end Dichotomy

section Witness

/-- `n` is a **Sylvester–Schur witness point**: it lies on a run of `L`
consecutive integers `[a, a + L − 1]` starting at `a > L`, all of whose
elements have `largestPrimeFactor ≤ L` — i.e. no element of the run is
divisible by a prime `> L`, so `[a, a + L − 1]` violates the
Sylvester–Schur conclusion.  Every long-bad-covered point is a witness
(`inLongBadInterval_ssWitness`); the predicate is empty once the quadratic
regime of Sylvester–Schur is proved (`ssWitnessCount_eq_zero`). -/
def ssWitness (n : ℕ) : Prop :=
  ∃ a L : ℕ, 1 ≤ L ∧ L < a ∧ n ∈ Finset.Icc a (a + L - 1) ∧
    ∀ i ∈ Finset.Icc a (a + L - 1), largestPrimeFactor i ≤ L

/-- An ssWitness run is entirely composite: an element `i > L` with
`largestPrimeFactor i ≤ L` cannot be prime, since a prime `i` satisfies
`largestPrimeFactor i = i`. -/
theorem ssWitness_not_prime {a L i : ℕ} (_hL : 1 ≤ L) (hLa : L < a)
    (hsmooth : ∀ j ∈ Finset.Icc a (a + L - 1), largestPrimeFactor j ≤ L)
    (hi : i ∈ Finset.Icc a (a + L - 1)) : ¬ i.Prime := by
  intro hp
  have hle := hsmooth i hi
  rw [largestPrimeFactor_eq_self_of_prime hp] at hle
  have h2 := Finset.mem_Icc.mp hi
  omega

/-- The run underlying an ssWitness point is a Sylvester–Schur failure. -/
theorem not_sylvesterSchur_of_run {a L : ℕ} (hL : 1 ≤ L) (hLa : L < a)
    (hsmooth : ∀ j ∈ Finset.Icc a (a + L - 1), largestPrimeFactor j ≤ L) :
    ¬ SylvesterSchur a L := by
  rintro ⟨p, hp, hpL, i, hi, hpi⟩
  have hI := Finset.mem_Icc.mp hi
  have hi2 : 2 ≤ i := by omega
  have hle := prime_dvd_le_largestPrimeFactor hi2 hp hpi
  have hsm := hsmooth i hi
  omega

/-- Long-bad-covered points are Sylvester–Schur witnesses: a long bad
interval `[u, v]` (`P ≤ v − u`) is a run of `L = v − u + 1` consecutive
`L`-smooth integers starting at `u > L` (the dyadic squeeze `v + 2 ≤ 2u`
gives `u - L = 2u - v - 1 ≥ 1`). -/
theorem inLongBadInterval_ssWitness {n : ℕ} (h : InLongBadInterval n) :
    ssWitness n := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hlong⟩ := h
  have hsqueeze : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  have hv : u + (v - u + 1) - 1 = v := by omega
  refine ⟨u, v - u + 1, by omega, by omega, ?_, ?_⟩
  · rw [hv]
    exact Finset.mem_Icc.mpr ⟨hun, hnv⟩
  · intro i hi
    rw [hv] at hi
    exact (bad_interval_forall_lpf_le hbad i hi).trans
      (hlong.trans (by omega : v - u ≤ v - u + 1))

/-- The count of ssWitness points `≤ x`. -/
noncomputable def ssWitnessCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => ssWitness n).card

/-- `longBadCount ≤ ssWitnessCount`: the witness count dominates the whole
long branch of the short/long decomposition. -/
theorem longBadCount_le_ssWitnessCount (x : ℕ) :
    longBadCount x ≤ ssWitnessCount x := by
  unfold longBadCount ssWitnessCount
  refine Finset.card_le_card ?_
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, inLongBadInterval_ssWitness hn.2⟩

/-- **Witness decomposition bound**: `N(x) ≤ T_short(x) + T_wit(x)`.  This
is strictly sharper than `badNonSingletonCount_le_short_add_smooth`
(`T_run(x) = x` identically) — the long branch contributes only the
Sylvester–Schur-failure points. -/
theorem badNonSingletonCount_le_short_add_ssWitness (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + ssWitnessCount x := by
  unfold badNonSingletonCount shortBadCount ssWitnessCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  obtain ⟨hnx, hnbad⟩ := hn
  rcases inNonSingletonBadInterval_iff_short_or_long.mp hnbad with h | h
  · exact Or.inl ⟨hnx, h⟩
  · exact Or.inr ⟨hnx, inLongBadInterval_ssWitness h⟩

/-- The quadratic-regime content of an ssWitness point: the witnessing run
necessarily lies in `QuadRegimeOpen` — its length is `L ≥ 38`, its start
satisfies `L < a`, and its end satisfies `a + L - 1 ≤ L²`. -/
theorem ssWitness_quadRegimeOpen {n : ℕ} (h : ssWitness n) :
    ∃ a L : ℕ, _root_.SylvesterSchur.QuadRegimeOpen (a + L - 1) L ∧
      n ∈ Finset.Icc a (a + L - 1) ∧
      ∀ i ∈ Finset.Icc a (a + L - 1), largestPrimeFactor i ≤ L := by
  obtain ⟨a, L, hL, hLa, hn, hsmooth⟩ := h
  exact ⟨a, L,
    quadRegimeOpen_of_not_sylvesterSchur hL hLa
      (not_sylvesterSchur_of_run hL hLa hsmooth),
    hn, hsmooth⟩

/-- A witness point `n` lies in a composite run of length `≥ √n`: the run
`[a, a + L − 1]` is composite, has length `L`, and `n ≤ a + L − 1 ≤ L²`
(quadratic regime) gives `√n ≤ L`. -/
theorem ssWitness_inCompositeRun_sqrt {n : ℕ} (h : ssWitness n) :
    InCompositeRun n (Nat.sqrt n) := by
  obtain ⟨a, L, ⟨hL38, h2L, hLsq⟩, hn, hsmooth⟩ := ssWitness_quadRegimeOpen h
  have hLa : L < a := by omega
  have hmem := Finset.mem_Icc.mp hn
  have hnL : n ≤ L * L := by
    have : n ≤ L ^ 2 := le_trans hmem.2 hLsq
    rwa [pow_two] at this
  have hs : Nat.sqrt n ≤ L := by
    rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
    exact lt_of_le_of_lt hnL
      (Nat.mul_self_lt_mul_self_iff.mpr (Nat.lt_succ_self L))
  exact ⟨a, a + L - 1, by omega,
    fun i hi => ssWitness_not_prime (by omega) hLa hsmooth hi, hmem.1, hmem.2⟩

/-- A witness point is `≥ 2` (it exceeds `L ≥ 1`). -/
theorem ssWitness_two_le {n : ℕ} (h : ssWitness n) : 2 ≤ n := by
  obtain ⟨a, L, hL, hLa, hn, -⟩ := h
  have hmem := Finset.mem_Icc.mp hn
  omega

/-- A witness point is composite. -/
theorem ssWitness_not_prime' {n : ℕ} (h : ssWitness n) : ¬ n.Prime :=
  inCompositeRun_not_prime (ssWitness_inCompositeRun_sqrt h)

/-- A witness point sits strictly inside a consecutive-prime gap of width
`≥ √n + 1`. -/
theorem ssWitness_inWidePrimeGap {n : ℕ} (h : ssWitness n) :
    InWidePrimeGap n (Nat.sqrt n) :=
  inCompositeRun_inWidePrimeGap (ssWitness_two_le h)
    (ssWitness_inCompositeRun_sqrt h)

/-- Coarse bound: witness points are composite, so
`ssWitnessCount x ≤ x + 1 − π(x)`. -/
theorem ssWitnessCount_le_not_prime (x : ℕ) :
    ssWitnessCount x ≤ x + 1 - Nat.primeCounting x := by
  have hsub : (Finset.range (x + 1)).filter (fun n => ssWitness n) ⊆
      (Finset.range (x + 1)).filter fun n => ¬ Nat.Prime n := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, ssWitness_not_prime' hn.2⟩
  unfold ssWitnessCount
  exact (Finset.card_le_card hsub).trans (le_of_eq (card_not_prime_range x))

end Witness

section DeepGap

/-- `n` lies strictly inside a consecutive-prime gap of width `≥ √n + 1`
(a "deep" gap relative to its location).  Every ssWitness point is a
deep-gap point (`ssWitness_inWidePrimeGap`). -/
noncomputable def deepGapCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InWidePrimeGap n (Nat.sqrt n)).card

theorem ssWitnessCount_le_deepGapCount (x : ℕ) :
    ssWitnessCount x ≤ deepGapCount x := by
  unfold ssWitnessCount deepGapCount
  refine Finset.card_le_card ?_
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, ssWitness_inWidePrimeGap hn.2⟩

/-- Total length of prime gaps below `x` wider than the square root of
their location:
`Σ_{p ≤ x prime, nextPrime p − p ≥ √p + 1} (nextPrime p − p − 1)`. -/
noncomputable def wideGapLengthSum (x : ℕ) : ℕ :=
  ∑ p ∈ ((Nat.primesLE x).filter
    fun p => Nat.sqrt p + 1 ≤ nextPrime p - p), (nextPrime p - p - 1)

/-- **Deep-gap domination by gap lengths**: points `n ≤ x` inside gaps
`(p, q)` of consecutive primes with `q - p ≥ √n + 1` satisfy
`q - p ≥ √p + 1` (since `p < n` gives `√p ≤ √n`) and lie in
`Icc (p + 1) (nextPrime p - 1)`.  Hence
`deepGapCount x ≤ wideGapLengthSum x`. -/
theorem deepGapCount_le_sum (x : ℕ) :
    deepGapCount x ≤ wideGapLengthSum x := by
  have hsub : (Finset.range (x + 1)).filter
        (fun n => InWidePrimeGap n (Nat.sqrt n)) ⊆
      ((Nat.primesLE x).filter
          fun p => Nat.sqrt p + 1 ≤ nextPrime p - p).biUnion
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
      have hs : Nat.sqrt p ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega)
      omega
    · rw [Finset.mem_Icc]
      omega
  unfold deepGapCount wideGapLengthSum
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro p _hp
  rw [Nat.card_Icc]
  have hpgt : p < nextPrime p := nextPrime_lt p
  omega

/-- **Headline elementary bound of Assault 5**:
`N(x) ≤ T_short(x) + Σ_{p ≤ x, nextPrime p − p ≥ √p + 1} (nextPrime p − p − 1)`,

with the sum packaged as `wideGapLengthSum x`: the total length of all
prime gaps below `x` that are wider than the square root of their
location.  In reality it is zero for all `x` (the largest gaps are
`≍ log² x`); provably bounding it below `x` requires either the quadratic
regime of Sylvester–Schur (via `ssWitnessCount_eq_zero`, which shows the
summand set is empty) or a prime-gap bound `g(p) ≪ p^{1−ε}` — neither is
currently available. -/
theorem badNonSingletonCount_le_short_add_gapSum (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + wideGapLengthSum x :=
  (badNonSingletonCount_le_short_add_ssWitness x).trans
    (Nat.add_le_add_left
      ((ssWitnessCount_le_deepGapCount x).trans (deepGapCount_le_sum x)) _)

end DeepGap

section ConditionalClosures

/-- Under the quadratic-regime hypothesis there are no ssWitness points at
all: a witness run is a Sylvester–Schur failure in `QuadRegimeOpen`, and
`hquad` supplies a prime `> L` dividing some run element — contradicting
`largestPrimeFactor ≤ L`. -/
theorem not_ssWitness_of_quad
    (hquad : ∀ n' k' : ℕ, _root_.SylvesterSchur.QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k')
    {n : ℕ} (h : ssWitness n) : False := by
  obtain ⟨a, L, hL, hLa, hn, hsmooth⟩ := h
  have hfail := not_sylvesterSchur_of_run hL hLa hsmooth
  obtain ⟨q, hq, hqL, hqd⟩ :=
    hquad _ _ (quadRegimeOpen_of_not_sylvesterSchur hL hLa hfail)
  obtain ⟨m, hm, hqm⟩ :=
    _root_.SylvesterSchur.exists_mem_Icc_of_prime_dvd_choose hq hqL
      (by omega : L ≤ a + L - 1) hqd
  have hm' : m ∈ Finset.Icc a (a + L - 1) := by
    have h2 := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega, h2.2⟩
  have hI2 := Finset.mem_Icc.mp hm'
  have hm2 : 2 ≤ m := by omega
  have hle := prime_dvd_le_largestPrimeFactor hm2 hq hqm
  have hsm := hsmooth m hm'
  omega

/-- Under the quadratic-regime hypothesis, `ssWitnessCount` vanishes
identically. -/
theorem ssWitnessCount_eq_zero
    (hquad : ∀ n' k' : ℕ, _root_.SylvesterSchur.QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k') (x : ℕ) :
    ssWitnessCount x = 0 := by
  unfold ssWitnessCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro n hn
  rw [Finset.mem_filter] at hn
  exact not_ssWitness_of_quad hquad hn.2

/-- **Reduction (a): quad regime + short estimate suffice.**
Modulo `QuadRegimeOpen` (the only unproved case of Sylvester–Schur), the
long branch is empty (`ssWitnessCount = 0`), so `N(x) ≤ T_short(x)`; a
bound `T_short(x) ≤ (log x)^{-1+ε}·S(x)` then yields the analytic core.
This sharpens `badNonSingleton_interval_bound_of_sylvesterSchur_short`:
the only obstruction in the Sylvester–Schur hypothesis is the quadratic
regime. -/
theorem badNonSingleton_interval_bound_of_short_and_quad
    (hquad : ∀ n' k' : ℕ, _root_.SylvesterSchur.QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k')
    (hshort : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (shortBadCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [hshort ε hε] with x hx
  have h0 : ssWitnessCount x = 0 := ssWitnessCount_eq_zero hquad x
  have hle : badNonSingletonCount x ≤ shortBadCount x := by
    have h := badNonSingletonCount_le_short_add_ssWitness x
    omega
  have hle' : (badNonSingletonCount x : ℝ) ≤ shortBadCount x := by
    exact_mod_cast hle
  linarith

/-- **Reduction (b): unconditional two-component form.**  If
`T_short(x) + T_wit(x) ≤ (log x)^{-1+ε}·S(x)` eventually for every `ε > 0`,
the analytic core follows.  `T_wit` is identically zero modulo
`QuadRegimeOpen`, so the true analytic input is the short estimate. -/
theorem badNonSingleton_interval_bound_of_short_and_witness
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (shortBadCount x : ℝ) + (ssWitnessCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [h ε hε] with x hx
  have hN : (badNonSingletonCount x : ℝ) ≤
      (shortBadCount x : ℝ) + (ssWitnessCount x : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_short_add_ssWitness x
  linarith

/-- **Reduction (c): short + deep-gap sum estimate suffices**, in a form
mentioning neither Sylvester–Schur nor smoothness: if
`T_short(x) + W(x) ≤ (log x)^{-1+ε}·S(x)` eventually for every `ε > 0`,
where `W(x) = wideGapLengthSum x` is the total length of `√p`-wide prime
gaps below `x`, the analytic core follows.  (`W` is in reality `0`; the
hypothesis isolates a pure prime-gap bound.) -/
theorem badNonSingleton_interval_bound_of_short_and_gap
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (shortBadCount x : ℝ) + (wideGapLengthSum x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  intro ε hε
  filter_upwards [h ε hε] with x hx
  have hN : (badNonSingletonCount x : ℝ) ≤
      (shortBadCount x : ℝ) + (wideGapLengthSum x : ℝ) := by
    exact_mod_cast badNonSingletonCount_le_short_add_gapSum x
  linarith

/-- The singleton lower bound at exponent `83/100` repackaged with `log⁶`
denominator (valid for `log x ≥ 1`, i.e. `x ≥ 3`), feeding
`badNonSingleton_interval_bound_of_squeeze`. -/
theorem badSingletonCount_eventually_ge_log6 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ^ (83 / 100 : ℝ) / (Real.log x) ^ 6 ≤
        (badSingletonCount x : ℝ) := by
  obtain ⟨c, hc, h⟩ := SmoothLB.badSingletonCount_eventually_ge_smooth
  refine ⟨c, hc, ?_⟩
  filter_upwards [h, eventually_ge_atTop 3] with x hx hx3
  have hxR : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have e : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    have hlt : Real.exp 1 ≤ 3 :=
      le_trans (le_of_lt Real.exp_one_lt_d9) (by norm_num)
    rw [← e]
    exact Real.log_le_log (Real.exp_pos 1) hlt
  have hlog1 : (1 : ℝ) ≤ Real.log x :=
    le_trans hlog3 (Real.log_le_log (by norm_num) hxR)
  have hlogpos : 0 < Real.log x := by linarith
  have h56 : Real.log x ^ 5 ≤ Real.log x ^ 6 :=
    pow_le_pow_right₀ hlog1 (by norm_num)
  have hA : (0 : ℝ) ≤ c * (x : ℝ) ^ (83 / 100 : ℝ) :=
    mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  calc c * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log x ^ 6
      ≤ c * (x : ℝ) ^ (83 / 100 : ℝ) / Real.log x ^ 5 := by
        rw [div_le_div_iff₀ (pow_pos hlogpos 6) (pow_pos hlogpos 5)]
        exact mul_le_mul_of_nonneg_left h56 hA
    _ ≤ (badSingletonCount x : ℝ) := hx

/-- **Reduction (d): power saving against the proved `S`-bound.**  Since
`SmoothLB` proves `S(x) ≥ c·x^{83/100}/log⁵x` eventually, any bound
`N(x) ≤ C·x^{1−δ}` with `δ > 17/100` (i.e. `1 − δ < 83/100`) yields the
analytic core via `badNonSingleton_interval_bound_of_squeeze`.  This is
the hypothesis a sibling agent targeting a stronger `N`-bound should
aim at. -/
theorem badNonSingleton_interval_bound_of_power_saving_83
    {δ C : ℝ} (hδ : 17 / 100 < δ)
    (hN : ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤ C * (x : ℝ) ^ (1 - δ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in Filter.atTop,
      (badNonSingletonCount x : ℝ) ≤
        (Real.log x) ^ (-(1 - ε)) * (badSingletonCount x : ℝ) := by
  obtain ⟨c, hc, hS⟩ := badSingletonCount_eventually_ge_log6
  exact badNonSingleton_interval_bound_of_squeeze hc hS (by linarith) hN

end ConditionalClosures

end JSP314
