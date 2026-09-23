import JSP314.ArcCount

/-!
# JSP-000314 — consecutive smooth pairs and the arc count

The crude bound `smoothArcCoveredCount_le_prime_smooth_sum` (in
`JSP314.ArcCount`) counts, for each bad singleton `m`, the whole window
`Icc (m - lpf m) (m + lpf m)` of size `2·lpf m + 1`, ignoring that the covered
`n` must lie on a *run* of `lpf m`-smooth numbers.  This file formalizes the
sharper structural fact underlying Tao's argument: a covered `n` that is not
itself a bad singleton lies **on a consecutive pair of smooth numbers**
adjacent to the `p²`-multiple `m`.

## What is proved

* `consecSmoothPair n p` — `largestPrimeFactor n ≤ p` and
  `largestPrimeFactor (n+1) ≤ p` (with `largestPrimeFactor i = 1` for
  `i ≤ 1`, so `n = 0` satisfies the predicate trivially);
* `consecSmoothPairCount x p` — the number of `n ≤ x` starting such a pair;
* `inSmoothArcToSingleton_eq_or_pair` — **the key structural lemma**: if `n`
  lies on a smooth arc to a bad singleton `m`, then either `n` is itself a bad
  singleton, or there is a prime `p = largestPrimeFactor m` with `p² ∣ m` and
  a consecutive `p`-smooth pair `j, j+1` with `n ∈ {j, j+1}` and
  `|j - m| ≤ p` (i.e. `j ≤ m + p ∧ m ≤ j + p`), with `m ≤ 2n`;
* `nearPairCovered x n p` / `nearPairCoveredCount x p` — the counting
  predicate: `n` is a member of a `p`-smooth pair within `p` of a `p²`-multiple
  `m ≤ 2x` with `largestPrimeFactor m = p`;
* `consecSmoothPairWindow x p` — the finset of pair beginnings `j ≤ x` near a
  `p²`-multiple;
* `smoothArcCoveredCount_le_badSingleton_add_nearPair` — the per-prime count
  bound with **no loss factor**:
  `T_arc(x) ≤ S(2x) + Σ_{p ≤ √(2x) prime} nearPairCoveredCount x p`;
* `nearPairCoveredCount_le_two_mul_window` — each pair beginning contributes
  at most the two values `j, j+1`, so
  `nearPairCoveredCount x p ≤ 2 · (consecSmoothPairWindow x p).card`;
* `smoothArcCoveredCount_le_badSingleton_add_pairWindow` and
  `smoothArcCoveredCount_le_badSingleton_add_pairCount` — the headline
  reductions:
  `T_arc(x) ≤ S(2x) + 2·Σ_{p ≤ √(2x)} (consecSmoothPairWindow x p).card` and
  `T_arc(x) ≤ S(2x) + 2·Σ_{p ≤ √(2x)} consecSmoothPairCount x p`;
* `smoothArcCoveredCount_le_badSingleton_add_explicit` — inserting Mathlib's
  squarefree-kernel bound `Nat.smoothNumbersUpTo_card_le` gives the fully
  explicit unconditional
  `T_arc(x) ≤ S(2x) + 2·(√(2x)+1)·(1 + 2^{π'(√(2x)+1)}·√x)`.

## Honest assessment of the pair count

The only proved bounds on `consecSmoothPairCount x p` here are the trivial
ones: `≤ x + 1`, and `≤ 1 + Ψ(x, p)` via `consecSmoothPairCount_le_...`,
hence `≤ 1 + 2^{π'(p+1)}·√x` (`consecSmoothPairCount_le_exp_sqrt`).  A
genuinely sublinear bound on consecutive `p`-smooth pairs — the input Tao's
argument needs — would have to come from a Pell-type analysis: writing the
pair as `a·s², a'·t²` with `a, a'` squarefree `p`-smooth kernels gives
`a'·t² - a·s² = 1`, and the number of solutions per `(a, a')` is a lattice
count on a conic that Mathlib does not provide.  The reduction proved here is
therefore *sharp in shape but not yet quantitatively useful*: it replaces the
`(2p+1)·Ψ(2x/p², p)` windows of `smoothArcCoveredCount_le_prime_smooth_sum`
by the genuinely smaller object `consecSmoothPairCount`, whose good bounds
remain the analytic content of Ta26c.
-/

namespace JSP314

open Classical

section Pairs

/-- `n` begins a consecutive `p`-smooth pair: both `n` and `n + 1` have
largest prime factor at most `p`.  Since `largestPrimeFactor i = 1` for
`i ≤ 1`, the case `n = 0` holds for every `p`. -/
def consecSmoothPair (n p : ℕ) : Prop :=
  largestPrimeFactor n ≤ p ∧ largestPrimeFactor (n + 1) ≤ p

/-- `consecSmoothPairCount x p`: the number of `n ≤ x` such that `n` and
`n + 1` are both `p`-smooth in the `largestPrimeFactor` sense. -/
noncomputable def consecSmoothPairCount (x p : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => consecSmoothPair n p).card

/-- `nearPairCovered x n p`: `n` is one of the two members `j, j + 1` of a
consecutive `p`-smooth pair sitting within `p` of a `p²`-multiple `m ≤ 2x`
whose largest prime factor is exactly `p`. -/
def nearPairCovered (x n p : ℕ) : Prop :=
  ∃ j m : ℕ, consecSmoothPair j p ∧ (n = j ∨ n = j + 1) ∧
    j ≤ m + p ∧ m ≤ j + p ∧ 1 < m ∧ p ^ 2 ∣ m ∧
    largestPrimeFactor m = p ∧ m ≤ 2 * x

/-- `nearPairCoveredCount x p`: the number of `n ≤ x` with
`nearPairCovered x n p`. -/
noncomputable def nearPairCoveredCount (x p : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => nearPairCovered x n p).card

/-- `consecSmoothPairWindow x p`: the `j ≤ x` that begin a `p`-smooth
consecutive pair lying within `p` of a `p²`-multiple `m ≤ 2x` with
`largestPrimeFactor m = p`. -/
noncomputable def consecSmoothPairWindow (x p : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun j =>
    consecSmoothPair j p ∧
      ∃ m : ℕ, j ≤ m + p ∧ m ≤ j + p ∧ 1 < m ∧ p ^ 2 ∣ m ∧
        largestPrimeFactor m = p ∧ m ≤ 2 * x

/-- **Key structural lemma.**  If `n` lies on a smooth arc to a bad singleton
`m` (`InSmoothArcToSingleton n`), then either `n` is itself a bad singleton,
or — taking `j = n` when `n < m` and `j = n - 1` when `n > m` — `j, j + 1` is
a consecutive `lpf m`-smooth pair containing `n`, at distance at most
`p = lpf m` from `m`. -/
theorem inSmoothArcToSingleton_eq_or_pair {n : ℕ} (h : InSmoothArcToSingleton n) :
    (1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n) ∨
      ∃ p j m : ℕ, Nat.Prime p ∧ consecSmoothPair j p ∧
        (n = j ∨ n = j + 1) ∧ 1 < m ∧ p ^ 2 ∣ m ∧
        largestPrimeFactor m = p ∧ m ≤ 2 * n ∧ j ≤ m + p ∧ m ≤ j + p := by
  obtain ⟨m, hm1, hmsq, hm2n, hsmooth, hnm, hmn⟩ := h
  rcases eq_or_ne n m with heq | hne
  · subst heq
    exact Or.inl ⟨hm1, hmsq⟩
  · right
    have hm2 : 2 ≤ m := hm1
    refine ⟨largestPrimeFactor m, if n ≤ m then n else n - 1, m,
      largestPrimeFactor_prime hm2, ?_, ?_, hm1, hmsq, rfl, hm2n, ?_, ?_⟩
    · -- `consecSmoothPair j (lpf m)`: both `j` and `j + 1` lie on the arc.
      by_cases hnm2 : n ≤ m
      · rw [ite_eq_left hnm2]
        have hlt : n < m := lt_of_le_of_ne hnm2 hne
        exact ⟨hsmooth n (by rw [Finset.mem_Icc]; omega),
          hsmooth (n + 1) (by rw [Finset.mem_Icc]; omega)⟩
      · rw [ite_eq_right hnm2]
        have hlt : m < n := by omega
        exact ⟨hsmooth (n - 1) (by rw [Finset.mem_Icc]; omega),
          hsmooth (n - 1 + 1) (by rw [Finset.mem_Icc]; omega)⟩
    · -- `n = j ∨ n = j + 1`.
      by_cases hnm2 : n ≤ m
      · rw [ite_eq_left hnm2]
        exact Or.inl rfl
      · rw [ite_eq_right hnm2]
        have hlt : m < n := by omega
        exact Or.inr (by omega)
    · -- `j ≤ m + p`.
      by_cases hnm2 : n ≤ m
      · rw [ite_eq_left hnm2]
        have hlt : n < m := lt_of_le_of_ne hnm2 hne
        omega
      · rw [ite_eq_right hnm2]
        omega
    · -- `m ≤ j + p`.
      by_cases hnm2 : n ≤ m
      · rw [ite_eq_left hnm2]
        have hlt : n < m := lt_of_le_of_ne hnm2 hne
        omega
      · rw [ite_eq_right hnm2]
        have hlt : m < n := by omega
        omega

/-- **Per-prime count bound, no loss factor.**  Every `n ≤ x` on a smooth arc
to a bad singleton is either itself a bad singleton `≤ 2x`, or is
`nearPairCovered x n p` for `p = largestPrimeFactor m`, a prime `≤ √(2x)`.
Hence
`smoothArcCoveredCount x ≤ badSingletonCount (2x) +
  Σ_{p ∈ primesLE √(2x)} nearPairCoveredCount x p`. -/
theorem smoothArcCoveredCount_le_badSingleton_add_nearPair (x : ℕ) :
    smoothArcCoveredCount x ≤
      badSingletonCount (2 * x) +
        ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), nearPairCoveredCount x p := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InSmoothArcToSingleton n) ⊆
      badSingletonsBelow (2 * x) ∪
        (Nat.primesLE (Nat.sqrt (2 * x))).biUnion
          (fun p => (Finset.range (x + 1)).filter
            (fun n => nearPairCovered x n p)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hn⟩ := hn
    rcases inSmoothArcToSingleton_eq_or_pair hn with hbad | hpr
    · rw [Finset.mem_union]
      exact Or.inl (mem_badSingletonsBelow.mpr ⟨by omega, hbad.1, hbad.2⟩)
    · obtain ⟨p, j, m, hp, hpair, hncase, hm1, hmsq, hlpf, hm2n, hjm1, hjm2⟩ := hpr
      rw [Finset.mem_union]
      right
      rw [Finset.mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · have hmem : m ∈ badSingletonsBelow (2 * x) := by
          rw [mem_badSingletonsBelow]
          refine ⟨by omega, hm1, ?_⟩
          rw [hlpf]; exact hmsq
        have h := lpf_mem_primesLE_sqrt hmem
        rwa [hlpf] at h
      · rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨hnx, j, m, hpair, hncase, hjm1, hjm2, hm1, hmsq, hlpf, by omega⟩
  unfold smoothArcCoveredCount
  refine (Finset.card_le_card hsub).trans <|
    (Finset.card_union_le _ _).trans <|
      add_le_add (card_badSingletonsBelow _).le Finset.card_biUnion_le

/-- Each `nearPairCovered` value `n` equals `j` or `j + 1` for some
`j ∈ consecSmoothPairWindow x p`, so
`nearPairCoveredCount x p ≤ 2 · (consecSmoothPairWindow x p).card`.  The
factor `2` is genuine: both members of a smooth pair can be covered by the
same arc. -/
theorem nearPairCoveredCount_le_two_mul_window (x p : ℕ) :
    nearPairCoveredCount x p ≤ 2 * (consecSmoothPairWindow x p).card := by
  have hsub : (Finset.range (x + 1)).filter (fun n => nearPairCovered x n p) ⊆
      (consecSmoothPairWindow x p).biUnion (fun j => {j, j + 1}) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, j, m, hpair, hncase, hjm1, hjm2, hm1, hmsq, hlpf, hm2x⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨j, ?_, ?_⟩
    · unfold consecSmoothPairWindow
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, hpair, m, hjm1, hjm2, hm1, hmsq, hlpf, hm2x⟩
      rcases hncase with h | h <;> omega
    · rcases hncase with h | h
      · subst h
        exact Finset.mem_insert_self _ _
      · subst h
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  unfold nearPairCoveredCount
  refine (Finset.card_le_card hsub).trans <| Finset.card_biUnion_le.trans ?_
  apply le_of_eq
  calc ∑ j ∈ consecSmoothPairWindow x p, ({j, j + 1} : Finset ℕ).card
      = ∑ _j ∈ consecSmoothPairWindow x p, 2 :=
        Finset.sum_congr rfl fun j _ => Finset.card_pair (by omega)
    _ = (consecSmoothPairWindow x p).card * 2 :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = 2 * (consecSmoothPairWindow x p).card := Nat.mul_comm _ _

/-- **Headline reduction (window form)**: the smooth-arc count is bounded by
the bad-singleton count plus twice the per-prime count of consecutive
`p`-smooth pairs lying near `p²`-multiples:
`T_arc(x) ≤ S(2x) + 2·Σ_{p ≤ √(2x)} (consecSmoothPairWindow x p).card`. -/
theorem smoothArcCoveredCount_le_badSingleton_add_pairWindow (x : ℕ) :
    smoothArcCoveredCount x ≤
      badSingletonCount (2 * x) +
        2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (consecSmoothPairWindow x p).card := by
  refine (smoothArcCoveredCount_le_badSingleton_add_nearPair x).trans ?_
  rw [Finset.mul_sum]
  exact add_le_add (le_refl _)
    (Finset.sum_le_sum fun p _ => nearPairCoveredCount_le_two_mul_window x p)

/-- The window finset is a subset of the pair beginnings:
`(consecSmoothPairWindow x p).card ≤ consecSmoothPairCount x p`. -/
theorem consecSmoothPairWindow_card_le_count (x p : ℕ) :
    (consecSmoothPairWindow x p).card ≤ consecSmoothPairCount x p := by
  unfold consecSmoothPairWindow consecSmoothPairCount
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.1⟩

/-- Consequently
`nearPairCoveredCount x p ≤ 2 · consecSmoothPairCount x p`. -/
theorem nearPairCoveredCount_le_two_mul_consecSmoothPairCount (x p : ℕ) :
    nearPairCoveredCount x p ≤ 2 * consecSmoothPairCount x p :=
  (nearPairCoveredCount_le_two_mul_window x p).trans
    (Nat.mul_le_mul (le_refl 2) (consecSmoothPairWindow_card_le_count x p))

/-- **Headline reduction (pair-count form)**:
`T_arc(x) ≤ S(2x) + 2·Σ_{p ≤ √(2x)} consecSmoothPairCount x p`. -/
theorem smoothArcCoveredCount_le_badSingleton_add_pairCount (x : ℕ) :
    smoothArcCoveredCount x ≤
      badSingletonCount (2 * x) +
        2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          consecSmoothPairCount x p := by
  refine (smoothArcCoveredCount_le_badSingleton_add_nearPair x).trans ?_
  rw [Finset.mul_sum]
  exact add_le_add (le_refl _)
    (Finset.sum_le_sum fun p _ =>
      nearPairCoveredCount_le_two_mul_consecSmoothPairCount x p)

/-- The same reduction composed with
`shortBadCount_le_smoothArcCoveredCount`:
`T_short(x) ≤ S(2x) + 2·Σ_{p ≤ √(2x)} consecSmoothPairCount x p`. -/
theorem shortBadCount_le_badSingleton_add_pairCount (x : ℕ) :
    shortBadCount x ≤
      badSingletonCount (2 * x) +
        2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          consecSmoothPairCount x p :=
  (shortBadCount_le_smoothArcCoveredCount x).trans
    (smoothArcCoveredCount_le_badSingleton_add_pairCount x)

end Pairs

section TrivialBounds

/-- Trivial bound: `consecSmoothPairCount x p ≤ x + 1`. -/
theorem consecSmoothPairCount_le (x p : ℕ) :
    consecSmoothPairCount x p ≤ x + 1 := by
  unfold consecSmoothPairCount
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- The left member of a `p`-smooth pair is `(p+1)`-smooth in Mathlib's sense
(for `n ≥ 1`; the `n = 0` case contributes the extra `1`), hence
`consecSmoothPairCount x p ≤ 1 + Ψ(x, p)` where
`Ψ(x, p) = (Nat.smoothNumbersUpTo x (p+1)).card`. -/
theorem consecSmoothPairCount_le_smoothNumbersUpTo (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + (Nat.smoothNumbersUpTo x (p + 1)).card := by
  have hsub : (Finset.range (x + 1)).filter (fun n => consecSmoothPair n p) ⊆
      insert 0 (Nat.smoothNumbersUpTo x (p + 1)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, h1, -⟩ := hn
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact Finset.mem_insert_self _ _
    · rw [Finset.mem_insert]
      right
      rw [Nat.mem_smoothNumbersUpTo]
      exact ⟨Nat.lt_add_one_iff.mp hnx, mem_smoothNumbers_of_lpf_le hpos h1⟩
  unfold consecSmoothPairCount
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (0 : ℕ) (Nat.smoothNumbersUpTo x (p + 1))
  omega

/-- Inserting Mathlib's squarefree-kernel bound
`Nat.smoothNumbersUpTo_card_le`: `consecSmoothPairCount x p ≤ 1 +
2^{π'(p+1)}·√x`.  This is the trivial `Ψ`-type bound; no sharper bound on
consecutive smooth pairs is currently available (a Pell-type solution count
would be needed). -/
theorem consecSmoothPairCount_le_exp_sqrt (x p : ℕ) :
    consecSmoothPairCount x p ≤
      1 + 2 ^ (Nat.primesBelow (p + 1)).card * Nat.sqrt x :=
  (consecSmoothPairCount_le_smoothNumbersUpTo x p).trans
    (add_le_add (le_refl 1) (Nat.smoothNumbersUpTo_card_le x (p + 1)))

/-- **Fully explicit unconditional bound**: combining
`smoothArcCoveredCount_le_badSingleton_add_pairCount` with the trivial pair
bound and `π(√(2x)) ≤ √(2x) + 1`,
`T_arc(x) ≤ S(2x) + 2·(√(2x)+1)·(1 + 2^{π'(√(2x)+1)}·√x)`.
This is weaker than `smoothArcCoveredCount_le_log_bound`; it is included only
to record the complete proved reduction chain. -/
theorem smoothArcCoveredCount_le_badSingleton_add_explicit (x : ℕ) :
    smoothArcCoveredCount x ≤
      badSingletonCount (2 * x) +
        2 * ((Nat.sqrt (2 * x) + 1) *
          (1 + 2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card *
            Nat.sqrt x)) := by
  have hsum : ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        consecSmoothPairCount x p ≤
      (Nat.sqrt (2 * x) + 1) *
        (1 + 2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card *
          Nat.sqrt x) := by
    calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), consecSmoothPairCount x p
        ≤ ∑ _p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
            (1 + 2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card *
              Nat.sqrt x) := by
          apply Finset.sum_le_sum
          intro p hp
          have hple : p ≤ Nat.sqrt (2 * x) := Nat.le_of_mem_primesLE hp
          have hsub : Nat.primesBelow (p + 1) ⊆
              Nat.primesBelow (Nat.sqrt (2 * x) + 1) :=
            Nat.primesBelow_mono (by omega)
          have hpow : 2 ^ (Nat.primesBelow (p + 1)).card ≤
              2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card :=
            pow_le_pow_right' (by norm_num) (Finset.card_le_card hsub)
          have hmul := Nat.mul_le_mul hpow (le_refl (Nat.sqrt x))
          have h := consecSmoothPairCount_le_exp_sqrt x p
          omega
      _ = (Nat.primesLE (Nat.sqrt (2 * x))).card *
            (1 + 2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card *
              Nat.sqrt x) :=
          Finset.sum_const_nat fun _ _ => rfl
      _ ≤ (Nat.sqrt (2 * x) + 1) *
            (1 + 2 ^ (Nat.primesBelow (Nat.sqrt (2 * x) + 1)).card *
              Nat.sqrt x) :=
          Nat.mul_le_mul (primesLE_card_le _) (le_refl _)
  refine (smoothArcCoveredCount_le_badSingleton_add_pairCount x).trans ?_
  exact add_le_add (le_refl _) (Nat.mul_le_mul (le_refl 2) hsum)

end TrivialBounds

end JSP314
