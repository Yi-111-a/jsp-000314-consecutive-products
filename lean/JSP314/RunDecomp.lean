import JSP314.PairSmooth

/-!
# JSP-000314 — "runs through the witness" decomposition of `shortBadCount`

The previous reductions (`JSP314.Reach`, `JSP314.PairSmooth`,
`JSP314.ShortResidual`) bound the short bad-interval count by counting covered
points `n` near a `p²`-multiple `m` with `largestPrimeFactor m = p`.  This file
splits that count by *how far the smooth run through `m` extends*:

* `rightRunWitness x p k` — the `m ≤ 2x` with `p² ∣ m`,
  `largestPrimeFactor m = p`, such that the `k` integers `m + 1, …, m + k`
  immediately to the right of `m` are all `p`-smooth;
* `leftRunWitness x p k` — the same with the `k` integers `m - k, …, m - 1`
  to the left (empty arc when `k = 0`, so the condition is vacuous there);
* `rightRunCount`, `leftRunCount` — their cardinalities.

The pointwise lemma `inShortBadInterval_runCovered` says that every `n ≤ x`
covered by a short bad interval `[u, v]` (with `P²`-witness `m` and
`p = largestPrimeFactor m`) satisfies one of:

* `n = m + k` with `m` a right run witness at distance `k ∈ [1, 2p]`
  (the whole arc `Icc (m+1) n ⊆ [u, v]` is `p`-smooth, and
  `k = n - m ≤ v - u < p ≤ 2p`);
* `n = m - k` with `m` a left run witness at distance `k ∈ [1, 2p]`;
* `n = m` — then `u < v` forces a `p`-smooth neighbour `m ± 1 ∈ [u, v]`, so
  `n` itself belongs to `rightRunWitness x p 1 ∪ leftRunWitness x p 1`.

Note that no Bertrand-type cutoff is needed: the distance bound
`|n - m| ≤ v - u < p` already lands `k` inside `[1, 2p]`.

Counting the union gives the headline bound

```
shortBadCount x ≤
  2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)
```

where the factor `2` absorbs the unshifted centre terms
`rightRunWitness x p k ∪ leftRunWitness x p k`.
-/

namespace JSP314

open Classical

/-- **Right run witnesses**: `m ≤ 2x` divisible by `p²`, with
`largestPrimeFactor m = p`, such that `m + 1, …, m + k` are all `p`-smooth.
For `k = 0` the arc `Icc (m+1) m` is empty and the condition is vacuous. -/
noncomputable def rightRunWitness (x p k : ℕ) : Finset ℕ :=
  (Finset.range (2 * x + 1)).filter fun m =>
    p ^ 2 ∣ m ∧ largestPrimeFactor m = p ∧
      (∀ j ∈ Finset.Icc (m + 1) (m + k), largestPrimeFactor j ≤ p)

/-- **Left run witnesses**: `m ≤ 2x` divisible by `p²`, with
`largestPrimeFactor m = p`, such that `m - k, …, m - 1` are all `p`-smooth
(truncated subtraction makes the arc `Icc (m - k) (m - 1)` empty when
`k ≥ m` or `k = 0`). -/
noncomputable def leftRunWitness (x p k : ℕ) : Finset ℕ :=
  (Finset.range (2 * x + 1)).filter fun m =>
    p ^ 2 ∣ m ∧ largestPrimeFactor m = p ∧
      (∀ j ∈ Finset.Icc (m - k) (m - 1), largestPrimeFactor j ≤ p)

/-- The number of right run witnesses. -/
noncomputable def rightRunCount (x p k : ℕ) : ℕ := (rightRunWitness x p k).card

/-- The number of left run witnesses. -/
noncomputable def leftRunCount (x p k : ℕ) : ℕ := (leftRunWitness x p k).card

theorem mem_rightRunWitness {x p k m : ℕ} :
    m ∈ rightRunWitness x p k ↔
      m ≤ 2 * x ∧ p ^ 2 ∣ m ∧ largestPrimeFactor m = p ∧
        ∀ j ∈ Finset.Icc (m + 1) (m + k), largestPrimeFactor j ≤ p := by
  simp only [rightRunWitness, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]

theorem mem_leftRunWitness {x p k m : ℕ} :
    m ∈ leftRunWitness x p k ↔
      m ≤ 2 * x ∧ p ^ 2 ∣ m ∧ largestPrimeFactor m = p ∧
        ∀ j ∈ Finset.Icc (m - k) (m - 1), largestPrimeFactor j ≤ p := by
  simp only [leftRunWitness, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]

/-- **Pointwise run-covering lemma**: every `n ≤ x` covered by a short bad
interval `[u, v]` is accounted for by a run witness `m` (the interval's
`P²`-multiple, `p = largestPrimeFactor m`) at some distance `k ∈ [1, 2p]`,
either to the right (`n = m + k`), to the left (`n = m - k`), or as the centre
itself (`n ∈ rightRunWitness x p 1 ∪ leftRunWitness x p 1`). -/
theorem inShortBadInterval_runCovered {x n : ℕ} (hx : n ≤ x)
    (h : InShortBadInterval n) :
    ∃ p k : ℕ, p ∈ Nat.primesLE (Nat.sqrt (2 * x)) ∧
      k ∈ Finset.Icc 1 (2 * p) ∧
        ((∃ m ∈ rightRunWitness x p k, n = m + k) ∨
          (∃ m ∈ leftRunWitness x p k, n = m - k) ∨
            n ∈ rightRunWitness x p k ∪ leftRunWitness x p k) := by
  classical
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := h
  obtain ⟨m, hmI, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf : largestPrimeFactor m =
      largestPrimeFactor ((Finset.Icc u v).prod id) :=
    sq_dvd_mem_lpf_eq hbad hmI hdvd
  have hbs : 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m :=
    sq_dvd_mem_is_bad_singleton' hbad hmI hdvd
  have hmIcc : u ≤ m ∧ m ≤ v := Finset.mem_Icc.mp hmI
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  have hp_prime : (largestPrimeFactor m).Prime :=
    largestPrimeFactor_prime (by omega)
  have hm2x : m ≤ 2 * x := by omega
  have hp_le : largestPrimeFactor m ≤ Nat.sqrt (2 * x) := by
    have h1 : (largestPrimeFactor m) ^ 2 ≤ m :=
      Nat.le_of_dvd (by omega) hbs.2
    have h2 : largestPrimeFactor m * largestPrimeFactor m ≤ 2 * x := by
      have := h1.trans hm2x
      nlinarith
    exact Nat.le_sqrt.mpr h2
  have hp_mem : largestPrimeFactor m ∈ Nat.primesLE (Nat.sqrt (2 * x)) :=
    Nat.mem_primesLE.mpr ⟨hp_le, hp_prime⟩
  have hshort' : v - u < largestPrimeFactor m := by
    rwa [← hlpf] at hshort
  have hall : ∀ j ∈ Finset.Icc u v,
      largestPrimeFactor j ≤ largestPrimeFactor m := by
    intro j hj
    calc largestPrimeFactor j
        ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
          short_bad_interval_all_lpf_le hbad j hj
      _ = largestPrimeFactor m := hlpf.symm
  rcases lt_trichotomy n m with hnm | hnm | hnm
  · -- `n < m`: the left arc `Icc n (m - 1) ⊆ [u, v]` is `p`-smooth and
    -- `k = m - n ≤ v - u < p`.
    refine ⟨largestPrimeFactor m, m - n, hp_mem, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · refine Or.inr (Or.inl ⟨m, ?_, by omega⟩)
      rw [mem_leftRunWitness]
      refine ⟨hm2x, hbs.2, rfl, ?_⟩
      intro j hj
      apply hall
      rw [Finset.mem_Icc] at hj ⊢
      omega
  · -- `n = m`: `u < v` forces a `p`-smooth neighbour `m ± 1 ∈ [u, v]`, so
    -- `n` itself is a `k = 1` witness on one side.
    subst hnm
    refine ⟨largestPrimeFactor n, 1, hp_mem, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have h2 := hp_prime.two_le
      omega
    · refine Or.inr (Or.inr ?_)
      rw [Finset.mem_union]
      rcases lt_or_eq_of_le hmIcc.2 with hmv | hmv
      · left
        rw [mem_rightRunWitness]
        refine ⟨hm2x, hbs.2, rfl, ?_⟩
        intro j hj
        apply hall
        rw [Finset.mem_Icc] at hj ⊢
        omega
      · right
        rw [mem_leftRunWitness]
        refine ⟨hm2x, hbs.2, rfl, ?_⟩
        intro j hj
        apply hall
        rw [Finset.mem_Icc] at hj ⊢
        omega
  · -- `m < n`: the right arc `Icc (m + 1) n ⊆ [u, v]` is `p`-smooth and
    -- `k = n - m ≤ v - u < p`.
    refine ⟨largestPrimeFactor m, n - m, hp_mem, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · refine Or.inl ⟨m, ?_, by omega⟩
      rw [mem_rightRunWitness]
      refine ⟨hm2x, hbs.2, rfl, ?_⟩
      intro j hj
      apply hall
      rw [Finset.mem_Icc] at hj ⊢
      omega

/-- **Runs-through-the-witness bound**: the short bad-interval count is at
most twice the sum over primes `p ≤ √(2x)` and distances `k ∈ [1, 2p]` of the
right- and left-run witness counts:

`shortBadCount x ≤ 2 * ∑ p, ∑ k, (rightRunCount x p k + leftRunCount x p k)`.

Each `(p, k)`-cell consists of the shifted images of the two witness finsets
(covering `n = m ± k`) together with the witnesses themselves (covering the
centre `n = m` at `k = 1`), which costs `2 · (rightRunCount + leftRunCount)`. -/
theorem shortBadCount_le_run_sum (x : ℕ) :
    shortBadCount x ≤
      2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ k ∈ Finset.Icc 1 (2 * p),
          (rightRunCount x p k + leftRunCount x p k) := by
  classical
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      (Nat.primesLE (Nat.sqrt (2 * x))).biUnion fun p =>
        (Finset.Icc 1 (2 * p)).biUnion fun k =>
          (rightRunWitness x p k).image (· + k) ∪
            ((leftRunWitness x p k).image (· - k) ∪
              (rightRunWitness x p k ∪ leftRunWitness x p k)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨p, k, hp, hk, hcov⟩ :=
      inShortBadInterval_runCovered (Nat.lt_add_one_iff.mp hn.1) hn.2
    rw [Finset.mem_biUnion]
    refine ⟨p, hp, Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩⟩
    rcases hcov with ⟨m, hm, hnm⟩ | ⟨m, hm, hnm⟩ | hnmem
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨m, hm, hnm.symm⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨m, hm, hnm.symm⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hnmem)
  calc shortBadCount x
      ≤ ((Nat.primesLE (Nat.sqrt (2 * x))).biUnion fun p =>
          (Finset.Icc 1 (2 * p)).biUnion fun k =>
            (rightRunWitness x p k).image (· + k) ∪
              ((leftRunWitness x p k).image (· - k) ∪
                (rightRunWitness x p k ∪ leftRunWitness x p k))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ((Finset.Icc 1 (2 * p)).biUnion fun k =>
            (rightRunWitness x p k).image (· + k) ∪
              ((leftRunWitness x p k).image (· - k) ∪
                (rightRunWitness x p k ∪ leftRunWitness x p k))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ∑ k ∈ Finset.Icc 1 (2 * p),
            ((rightRunWitness x p k).image (· + k) ∪
              ((leftRunWitness x p k).image (· - k) ∪
                (rightRunWitness x p k ∪ leftRunWitness x p k))).card :=
        Finset.sum_le_sum fun p _ => Finset.card_biUnion_le
    _ ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ∑ k ∈ Finset.Icc 1 (2 * p),
            2 * (rightRunCount x p k + leftRunCount x p k) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro k _
        have h1 := Finset.card_union_le
          ((rightRunWitness x p k).image (· + k))
          ((leftRunWitness x p k).image (· - k) ∪
            (rightRunWitness x p k ∪ leftRunWitness x p k))
        have h2 := Finset.card_union_le
          ((leftRunWitness x p k).image (· - k))
          (rightRunWitness x p k ∪ leftRunWitness x p k)
        have h3 := Finset.card_union_le (rightRunWitness x p k)
          (leftRunWitness x p k)
        have h4 := Finset.card_image_le (s := rightRunWitness x p k)
          (f := (· + k))
        have h5 := Finset.card_image_le (s := leftRunWitness x p k)
          (f := (· - k))
        have h6 : rightRunCount x p k = (rightRunWitness x p k).card := rfl
        have h7 : leftRunCount x p k = (leftRunWitness x p k).card := rfl
        omega
    _ = 2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          ∑ k ∈ Finset.Icc 1 (2 * p),
            (rightRunCount x p k + leftRunCount x p k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]

end JSP314
