import JSP314.BandSum

/-!
# JSP-000314 — multiplicity collapse of the inner `k`-sum in `runCountSum`

The inner sum `∑ k ∈ Finset.Icc 1 (2*p), (rightRunCount x p k +
leftRunCount x p k)` of `BandSum.runCountSum` counts each *multiplicity*
`k` of the smooth run through a `P²`-witness `m`.  But longer runs are
rarer than shorter ones: for `k ≤ k'`, the `k'`-arc contains the `k`-arc,
so

* `rightRunWitness x p k' ⊆ rightRunWitness x p k` (`rightRunWitness_mono`),
  and similarly on the left (`leftRunWitness_mono`).

In particular every witness with `k ≥ 1` is a `k = 1` witness: a bad
singleton `m` carrying *one* smooth neighbour `m + 1` (resp. `m − 1`).
The whole inner sum therefore collapses to `2·p` times the pair count:

* `sum_Icc_rightRunCount_le`, `sum_Icc_leftRunCount_le` —
  `∑ k ∈ Icc 1 (2p), rightRunCount x p k ≤ 2 * p * rightRunCount x p 1`;
* `sum_Icc_runCount_le` — the combined version;
* `runCountSum_le_two_mul_prime_weighted_pair_sum` — the headline bound

  ```
  runCountSum x ≤
    2 * ∑ p ∈ primesLE √(2x), p * (rightRunCount x p 1 + leftRunCount x p 1)
  ```

  (the factor is `2`, not `4`: `∑ k ≤ 2p` contributes `2p` copies, and the
  outer `2` in `shortBadCount_le_run_sum` is *not* part of `runCountSum`).

* Pair interpretation: `rightRunWitness x p 1` consists of `p²`-multiples
  `m ≤ 2x` with `largestPrimeFactor m = p` and `largestPrimeFactor (m+1)
  ≤ p` (`rightRunWitness_one_subset_pair`).  Quotienting `m = p²·r` gives
  the injection bound

  ```
  rightRunCount x p 1 ≤ rightPairQuotCount x p
    := #{r ≤ 2x / p² : largestPrimeFactor (p²·r + 1) ≤ p}
  ```

  (`rightRunCount_one_le_rightPairQuotCount`, and the left analogue with
  `p²·r − 1`).

* `runCountSum_le_two_mul_pairQuot_sum` — the headline bound transported
  to the quotient counts.

* Bonus collapse at the `badNonSingletonCount` level
  (`badNonSingletonCount_le_pair_sum_add_const`):

  ```
  badNonSingletonCount x ≤
    4 * ∑ p ∈ primesLE √(2x), p * (rightRunCount x p 1 + leftRunCount x p 1)
      + (2 * 10^16 + 1).
  ```

Everything is at the level of `ℕ`-cardinality; no analysis is used.
-/

namespace JSP314

open Classical

section Monotonicity

/-- **Monotonicity in the run length (right).**  A `k'`-long right run is
also a `k`-long right run whenever `k ≤ k'`: the arc `Icc (m+1) (m+k)` is
contained in `Icc (m+1) (m+k')`. -/
theorem rightRunWitness_mono {x p k k' : ℕ} (h : k ≤ k') :
    rightRunWitness x p k' ⊆ rightRunWitness x p k := by
  intro m hm
  rw [mem_rightRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsm⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, ?_⟩
  intro j hj
  apply hsm
  rw [Finset.mem_Icc] at hj ⊢
  omega

/-- **Monotonicity in the run length (left).**  Same for the left arc:
`Icc (m - k) (m - 1) ⊆ Icc (m - k') (m - 1)` since truncated subtraction
gives `m - k' ≤ m - k`. -/
theorem leftRunWitness_mono {x p k k' : ℕ} (h : k ≤ k') :
    leftRunWitness x p k' ⊆ leftRunWitness x p k := by
  intro m hm
  rw [mem_leftRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsm⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, ?_⟩
  intro j hj
  apply hsm
  rw [Finset.mem_Icc] at hj ⊢
  omega

/-- Every right run witness of length `k ≥ 1` is a length-`1` witness, so
`rightRunCount x p k ≤ rightRunCount x p 1`. -/
theorem rightRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    rightRunCount x p k ≤ rightRunCount x p 1 :=
  Finset.card_le_card (rightRunWitness_mono hk)

/-- Every left run witness of length `k ≥ 1` is a length-`1` witness, so
`leftRunCount x p k ≤ leftRunCount x p 1`. -/
theorem leftRunCount_le_one {x p k : ℕ} (hk : 1 ≤ k) :
    leftRunCount x p k ≤ leftRunCount x p 1 :=
  Finset.card_le_card (leftRunWitness_mono hk)

end Monotonicity

section Collapse

/-- **Inner-sum collapse (right).**  Each of the `2 * p` summands
`rightRunCount x p k`, `k ∈ Icc 1 (2p)`, is at most `rightRunCount x p 1`. -/
theorem sum_Icc_rightRunCount_le (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k ≤
      2 * p * rightRunCount x p 1 := by
  calc ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k
      ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), rightRunCount x p 1 :=
        Finset.sum_le_sum fun k hk =>
          rightRunCount_le_one (Finset.mem_Icc.mp hk).1
    _ = 2 * p * rightRunCount x p 1 := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc,
          Nat.add_sub_cancel]

/-- **Inner-sum collapse (left).** -/
theorem sum_Icc_leftRunCount_le (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k ≤
      2 * p * leftRunCount x p 1 := by
  calc ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k
      ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), leftRunCount x p 1 :=
        Finset.sum_le_sum fun k hk =>
          leftRunCount_le_one (Finset.mem_Icc.mp hk).1
    _ = 2 * p * leftRunCount x p 1 := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.card_Icc,
          Nat.add_sub_cancel]

/-- **Inner-sum collapse (both sides).** -/
theorem sum_Icc_runCount_le (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k) ≤
      2 * p * (rightRunCount x p 1 + leftRunCount x p 1) := by
  rw [Finset.sum_add_distrib, mul_add]
  exact Nat.add_le_add (sum_Icc_rightRunCount_le x p)
    (sum_Icc_leftRunCount_le x p)

/-- **Multiplicity collapse of `runCountSum`.**  Summing the inner collapse
over the primes `p ≤ √(2x)`:

`runCountSum x ≤ 2 * ∑ p, p * (rightRunCount x p 1 + leftRunCount x p 1)`.

Each `m` counted is a `P²`-bad singleton (`p² ∣ m`,
`largestPrimeFactor m = p`) carrying a `p`-smooth neighbour `m ± 1`. -/
theorem runCountSum_le_two_mul_prime_weighted_pair_sum (x : ℕ) :
    runCountSum x ≤
      2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        p * (rightRunCount x p 1 + leftRunCount x p 1) := by
  rw [runCountSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  calc ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)
      ≤ 2 * p * (rightRunCount x p 1 + leftRunCount x p 1) :=
        sum_Icc_runCount_le x p
    _ = 2 * (p * (rightRunCount x p 1 + leftRunCount x p 1)) :=
        mul_assoc 2 p _

end Collapse

section PairInterpretation

/-- **Pair reading (right).**  A `k = 1` right run witness is a `p²`-multiple
`m ≤ 2x` whose right neighbour `m + 1` is `p`-smooth. -/
theorem rightRunWitness_one_subset_pair (x p : ℕ) :
    rightRunWitness x p 1 ⊆
      (Finset.range (2 * x + 1)).filter
        (fun m => p ^ 2 ∣ m ∧ largestPrimeFactor (m + 1) ≤ p) := by
  intro m hm
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  exact ⟨hm2x, hdvd, hsm (m + 1) (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)⟩

/-- **Pair reading (left).**  A `k = 1` left run witness is a `p²`-multiple
`m ≤ 2x` whose left neighbour `m - 1` is `p`-smooth (the arc
`Icc (m - 1) (m - 1) = {m - 1}` is nonempty even for `m = 0`). -/
theorem leftRunWitness_one_subset_pair (x p : ℕ) :
    leftRunWitness x p 1 ⊆
      (Finset.range (2 * x + 1)).filter
        (fun m => p ^ 2 ∣ m ∧ largestPrimeFactor (m - 1) ≤ p) := by
  intro m hm
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
  exact ⟨hm2x, hdvd, hsm (m - 1) (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)⟩

/-- **Quotient witnesses (right):** `r ≤ 2x / p²` such that `p²·r + 1` is
`p`-smooth — the image of `rightRunWitness x p 1` under `m ↦ m / p²`. -/
noncomputable def rightPairQuotWitness (x p : ℕ) : Finset ℕ :=
  (Finset.range (2 * x / p ^ 2 + 1)).filter
    (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)

/-- **Quotient witnesses (left):** `r ≤ 2x / p²` such that `p²·r - 1` is
`p`-smooth. -/
noncomputable def leftPairQuotWitness (x p : ℕ) : Finset ℕ :=
  (Finset.range (2 * x / p ^ 2 + 1)).filter
    (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)

/-- The number of right quotient witnesses. -/
noncomputable def rightPairQuotCount (x p : ℕ) : ℕ :=
  (rightPairQuotWitness x p).card

/-- The number of left quotient witnesses. -/
noncomputable def leftPairQuotCount (x p : ℕ) : ℕ :=
  (leftPairQuotWitness x p).card

/-- **Quotient injection (right).**  For `p ≥ 2`, `m ↦ m / p²` injects
`rightRunWitness x p 1` into the `r ≤ 2x / p²` with `p²·r + 1` `p`-smooth
(injectivity uses `p² * (m / p²) = m` from `p² ∣ m`). -/
theorem rightRunCount_one_le_rightPairQuotCount {x p : ℕ} (_hp : 2 ≤ p) :
    rightRunCount x p 1 ≤ rightPairQuotCount x p := by
  refine Finset.card_le_card_of_injOn (fun m => m / p ^ 2) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
    show m / p ^ 2 ∈ (Finset.range (2 * x / p ^ 2 + 1)).filter
        (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
    refine ⟨Nat.div_le_div_right hm2x, ?_⟩
    have hEq : p ^ 2 * (m / p ^ 2) = m := Nat.mul_div_cancel' hdvd
    rw [hEq]
    exact hsm (m + 1) (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  · intro a ha b hb h
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    have h' : a / p ^ 2 = b / p ^ 2 := h
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [h']
      _ = b := Nat.mul_div_cancel' hb.2.1

/-- **Quotient injection (left).**  Same injection for the left neighbour:
`p²·(m / p²) - 1 = m - 1` is `p`-smooth. -/
theorem leftRunCount_one_le_leftPairQuotCount {x p : ℕ} (_hp : 2 ≤ p) :
    leftRunCount x p 1 ≤ leftPairQuotCount x p := by
  refine Finset.card_le_card_of_injOn (fun m => m / p ^ 2) ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
    show m / p ^ 2 ∈ (Finset.range (2 * x / p ^ 2 + 1)).filter
        (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_add_one_iff]
    refine ⟨Nat.div_le_div_right hm2x, ?_⟩
    have hEq : p ^ 2 * (m / p ^ 2) = m := Nat.mul_div_cancel' hdvd
    rw [hEq]
    exact hsm (m - 1) (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  · intro a ha b hb h
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    have h' : a / p ^ 2 = b / p ^ 2 := h
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [h']
      _ = b := Nat.mul_div_cancel' hb.2.1

/-- **Quotient form of the collapse.**  `runCountSum x` is at most `2` times
the prime-weighted count of quotient pairs `r ≤ 2x / p²` with `p²·r ± 1`
`p`-smooth:

`runCountSum x ≤ 2 * ∑ p ∈ primesLE √(2x), p * (rightPairQuotCount x p +
leftPairQuotCount x p)`. -/
theorem runCountSum_le_two_mul_pairQuot_sum (x : ℕ) :
    runCountSum x ≤
      2 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        p * (rightPairQuotCount x p + leftPairQuotCount x p) := by
  refine (runCountSum_le_two_mul_prime_weighted_pair_sum x).trans ?_
  apply Nat.mul_le_mul (le_refl 2)
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesLE hp).two_le
  exact Nat.mul_le_mul (le_refl p)
    (Nat.add_le_add (rightRunCount_one_le_rightPairQuotCount hp2)
      (leftRunCount_one_le_leftPairQuotCount hp2))

end PairInterpretation

section TotalCount

/-- **Bonus: collapse at the `badNonSingletonCount` level.**  Combining
`BandSum.badNonSingletonCount_le_two_mul_runCountSum_add_const` with the
multiplicity collapse:

`badNonSingletonCount x ≤
  4 * ∑ p ∈ primesLE √(2x), p * (rightRunCount x p 1 + leftRunCount x p 1)
    + (2 * 10^16 + 1)`. -/
theorem badNonSingletonCount_le_pair_sum_add_const (x : ℕ) :
    badNonSingletonCount x ≤
      4 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          p * (rightRunCount x p 1 + leftRunCount x p 1) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_two_mul_runCountSum_add_const x
  have h2 := runCountSum_le_two_mul_prime_weighted_pair_sum x
  omega

/-- Same collapse with the quotient pair counts:
`badNonSingletonCount x ≤
  4 * ∑ p, p * (rightPairQuotCount x p + leftPairQuotCount x p)
    + (2 * 10^16 + 1)`. -/
theorem badNonSingletonCount_le_pairQuot_sum_add_const (x : ℕ) :
    badNonSingletonCount x ≤
      4 * ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          p * (rightPairQuotCount x p + leftPairQuotCount x p) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_two_mul_runCountSum_add_const x
  have h2 := runCountSum_le_two_mul_pairQuot_sum x
  omega

end TotalCount

end JSP314
