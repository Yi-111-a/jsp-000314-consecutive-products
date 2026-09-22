import JSP314.Dominant

/-!
# JSP-000314 — refined union bounds for the short-interval count

This file sharpens the crude union bound
`shortBadCount x ≤ badSingletonCount (2x) · (2√(2x) + 1)` of
`JSP314.ShortLong` by exploiting the *dominant singleton* structure proved in
`JSP314.Dominant`: every point `n ≤ x` covered by a short bad interval has a
bad singleton `m ≤ 2x` with `P(m)² ∣ m` within distance `P(m) = lpf m`, and
(unless `n = m`) `lpf n < lpf m`.

## Contents

* `badSingletonsOfLpf B p`: the bad singletons `≤ B` with `lpf m = p`.
* `card_badSingletonsOfLpf_le`: such singletons are `p²`-multiples, so there
  are at most `B / p²` of them.
* `card_biUnion_Icc_badSingletonsOfLpf_le`: they cover at most
  `(B / p²) · (2p + 1)` points.
* `shortBadCount_le_sum_lpf`:
  `T_short(x) ≤ ∑_{m ≤ 2x, bad singleton} (2·lpf m + 1)` — a strict
  sharpening of `shortBadCount_le_sum_sqrt` since `lpf m ≤ √m`.
* `shortBadCount_le_prime_sum` (**per-prime partition bound**):
  `T_short(x) ≤ ∑_{p ≤ √(2x), p prime} (2x / p²) · (2p + 1)`.
  Since `∑_{p} 1/p` over primes diverges like `log log`, this is the natural
  `O(x · log log x)`-shaped union bound for the short branch.
* `shortBadCount_le_smooth_add_prime_sum` (**smooth/rough split**): splitting
  covered points at a smoothness parameter `y` gives
  `T_short(x) ≤ #{n ≤ x : n is (y+1)-smooth} + ∑_{p > y, p ≤ √(2x)} (2x/p²)·(2p+1)`.
* `shortBadCount_le_smooth_bound_add_prime_sum`: the same with the smooth
  part bounded by `2^{π'(y+1)} · √x` via `Nat.smoothNumbersUpTo_card_le`.

This file is fully proved; no placeholders or unsafe shortcuts are used.
-/

namespace JSP314

open Classical

/-- The bad singletons `m ≤ B` whose largest prime factor equals `p`:
`1 < m`, `P(m)² ∣ m` and `P(m) = p`. -/
def badSingletonsOfLpf (B p : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter
    (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ largestPrimeFactor m = p)

theorem mem_badSingletonsOfLpf {B p m : ℕ} :
    m ∈ badSingletonsOfLpf B p ↔
      m ≤ B ∧ 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ largestPrimeFactor m = p := by
  simp only [badSingletonsOfLpf, Finset.mem_filter, Finset.mem_range,
    Nat.lt_add_one_iff]

/-- The interval `[m − p, m + p]` has at most `2p + 1` elements. -/
theorem card_Icc_sub_add_le (m p : ℕ) :
    (Finset.Icc (m - p) (m + p)).card ≤ 2 * p + 1 := by
  rw [Nat.card_Icc]
  omega

/-- **Count of bad singletons with a fixed largest prime factor**: every such
`m ≤ B` is a multiple of `p²`, and `m ↦ m / p²` injects them into
`[1, B / p²]`, so there are at most `B / p²` of them. -/
theorem card_badSingletonsOfLpf_le (B p : ℕ) :
    (badSingletonsOfLpf B p).card ≤ B / p ^ 2 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · -- `p = 0`: no `m` has `largestPrimeFactor m = 0` (it is always `≥ 1`).
    have hempty : badSingletonsOfLpf B 0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      rw [mem_badSingletonsOfLpf] at hm
      have hpos := largestPrimeFactor_pos m
      omega
    rw [hempty]
    simp
  · have hp2 : 0 < p ^ 2 := by
      rw [pow_two]
      exact Nat.mul_pos hp0 hp0
    refine (Finset.card_le_card_of_injOn (fun m => m / p ^ 2) ?_ ?_).trans ?_
    · -- MapsTo: `1 ≤ m / p² ≤ B / p²`.
      intro m hm
      rw [Finset.mem_coe, mem_badSingletonsOfLpf] at hm
      obtain ⟨hmB, hm1, hmsq, hmeq⟩ := hm
      have hdvd : p ^ 2 ∣ m := hmeq ▸ hmsq
      refine Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp2
      · exact Nat.div_le_div_right hmB
    · -- InjOn: `m` is determined by `m / p²` since `p² ∣ m`.
      intro a ha b hb hab
      rw [Finset.mem_coe, mem_badSingletonsOfLpf] at ha hb
      have hdvd_a : p ^ 2 ∣ a := ha.2.2.2 ▸ ha.2.2.1
      have hdvd_b : p ^ 2 ∣ b := hb.2.2.2 ▸ hb.2.2.1
      have hab' : a / p ^ 2 = b / p ^ 2 := hab
      calc a = a / p ^ 2 * p ^ 2 := (Nat.div_mul_cancel hdvd_a).symm
        _ = b / p ^ 2 * p ^ 2 := by rw [hab']
        _ = b := Nat.div_mul_cancel hdvd_b
    · rw [Nat.card_Icc]
      omega

/-- **Per-prime covering bound**: the bad singletons `m ≤ B` with
`lpf m = p` cover at most `(B / p²) · (2p + 1)` points. -/
theorem card_biUnion_Icc_badSingletonsOfLpf_le (B p : ℕ) :
    ((badSingletonsOfLpf B p).biUnion
        (fun m => Finset.Icc (m - p) (m + p))).card ≤
      (B / p ^ 2) * (2 * p + 1) := by
  refine (Finset.card_biUnion_le_card_mul _ _ _ ?_).trans ?_
  · intro m _
    exact card_Icc_sub_add_le m p
  · exact Nat.mul_le_mul (card_badSingletonsOfLpf_le B p) le_rfl

/-- Every point `n ≤ x` covered by a short bad interval lies in
`[m − lpf m, m + lpf m]` for a bad singleton `m ≤ 2x`, hence in the biUnion
indexed by `p = lpf m` ranging over primes `≤ √(2x)` whose witness `m` has
largest prime factor exactly `p`. -/
theorem shortBadCovered_subset_biUnion (x : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hPbound : ∀ m : ℕ, 1 < m → (largestPrimeFactor m) ^ 2 ∣ m →
      m ≤ 2 * x → largestPrimeFactor m ∈ P) :
    (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      P.biUnion (fun p =>
        (badSingletonsOfLpf (2 * x) p).biUnion
          (fun m => Finset.Icc (m - p) (m + p))) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hnx, hsh⟩ := hn
  obtain ⟨m, hm1, hmsq, hm2x, _hlt, _hbetween, hnhi, hmlo⟩ :=
    shortBadCovered_dominant hsh (Nat.lt_add_one_iff.mp hnx)
  rw [Finset.mem_biUnion]
  refine ⟨largestPrimeFactor m, hPbound m hm1 hmsq hm2x, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨m, ?_, ?_⟩
  · rw [mem_badSingletonsOfLpf]
    exact ⟨hm2x, hm1, hmsq, rfl⟩
  · rw [Finset.mem_Icc]
    omega

/-- **Deliverable 1 — per-singleton `lpf` bound**:
`T_short(x) ≤ ∑_{m ≤ 2x, m bad singleton} (2·lpf m + 1)`.

Strictly sharper than `shortBadCount_le_sum_sqrt` (which uses `√m`), since
`lpf m ≤ √m` whenever `lpf m² ∣ m`. -/
theorem shortBadCount_le_sum_lpf (x : ℕ) :
    shortBadCount x ≤
      ∑ m ∈ (Finset.range (2 * x + 1)).filter
          (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m),
        (2 * largestPrimeFactor m + 1) := by
  unfold shortBadCount
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      ((Finset.range (2 * x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)).biUnion
        (fun m => Finset.Icc
          (m - largestPrimeFactor m) (m + largestPrimeFactor m)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hsh⟩ := hn
    obtain ⟨m, hm1, hmsq, hm2x, _, _, hnhi, hmlo⟩ :=
      shortBadCovered_dominant hsh (Nat.lt_add_one_iff.mp hnx)
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hmsq⟩
    · rw [Finset.mem_Icc]
      omega
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro m _
  exact card_Icc_sub_add_le m (largestPrimeFactor m)

/-- **Deliverable 2 — per-prime partition bound** (the `O(x·log log x)`
union bound for the short branch):

`T_short(x) ≤ ∑_{p ≤ √(2x), p prime} (2x / p²) · (2p + 1)`.

Every short-covered point has a dominant bad singleton `m ≤ 2x` within
`p = lpf m`; grouping by `p`, at most `2x/p²` such `m` exist (each is a
`p²`-multiple), each covering `≤ 2p + 1` points. -/
theorem shortBadCount_le_prime_sum (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * x / p ^ 2) * (2 * p + 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      (Nat.primesLE (Nat.sqrt (2 * x))).biUnion (fun p =>
        (badSingletonsOfLpf (2 * x) p).biUnion
          (fun m => Finset.Icc (m - p) (m + p))) := by
    refine shortBadCovered_subset_biUnion x _ (fun p hp =>
      Nat.prime_of_mem_primesLE hp) ?_
    intro m hm1 hmsq hm2x
    rw [Nat.mem_primesLE]
    exact ⟨(lpf_le_sqrt_of_sq_dvd hm1 hmsq).trans (Nat.sqrt_le_sqrt hm2x),
      largestPrimeFactor_prime (by omega)⟩
  unfold shortBadCount
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro p _
  exact card_biUnion_Icc_badSingletonsOfLpf_le (2 * x) p

/-- **Deliverable 3 — smooth/rough split**: for any cutoff `y`, the covered
points with `lpf n ≤ y` are `(y+1)`-smooth (and covered points satisfy
`n ≥ 1`, so they land in `Nat.smoothNumbersUpTo x (y+1)`), while points with
`y < lpf n` have a dominant singleton whose `lpf = p` satisfies `p > y`
(whether `n = m`, when `lpf n = p`, or `n ≠ m`, when `lpf n < p`).

`T_short(x) ≤ #{n ≤ x : (y+1)-smooth} +
  ∑_{p prime, y < p ≤ √(2x)} (2x / p²)·(2p + 1)`. -/
theorem shortBadCount_le_smooth_add_prime_sum (x y : ℕ) :
    shortBadCount x ≤
      (Nat.smoothNumbersUpTo x (y + 1)).card +
      ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => y < p),
        (2 * x / p ^ 2) * (2 * p + 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      Nat.smoothNumbersUpTo x (y + 1) ∪
        ((Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => y < p)).biUnion
          (fun p => (badSingletonsOfLpf (2 * x) p).biUnion
            (fun m => Finset.Icc (m - p) (m + p))) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hsh⟩ := hn
    have hx : n ≤ x := Nat.lt_add_one_iff.mp hnx
    rcases Nat.lt_or_ge y (largestPrimeFactor n) with hy | hy
    · -- Rough branch: `y < lpf n`, and the witness `m` has `lpf m > y`.
      obtain ⟨m, hm1, hmsq, hm2x, hlt, _, hnhi, hmlo⟩ :=
        shortBadCovered_dominant hsh hx
      have hym : y < largestPrimeFactor m := by
        rcases eq_or_ne n m with rfl | hne
        · exact hy
        · exact hy.trans (hlt hne)
      rw [Finset.mem_union]
      refine Or.inr ?_
      rw [Finset.mem_biUnion]
      refine ⟨largestPrimeFactor m, ?_, ?_⟩
      · rw [Finset.mem_filter, Nat.mem_primesLE]
        exact ⟨⟨(lpf_le_sqrt_of_sq_dvd hm1 hmsq).trans
            (Nat.sqrt_le_sqrt hm2x),
          largestPrimeFactor_prime (by omega)⟩, hym⟩
      · rw [Finset.mem_biUnion]
        refine ⟨m, ?_, ?_⟩
        · rw [mem_badSingletonsOfLpf]
          exact ⟨hm2x, hm1, hmsq, rfl⟩
        · rw [Finset.mem_Icc]
          omega
    · -- Smooth branch: `lpf n ≤ y`; covered points satisfy `1 ≤ n`.
      have hn1 : 1 ≤ n := by
        obtain ⟨u, v, _, hbad, hun, _, _⟩ := hsh
        exact le_trans (bad_interval_one_le_left hbad) hun
      rw [Finset.mem_union]
      refine Or.inl ?_
      rw [Nat.mem_smoothNumbersUpTo]
      exact ⟨hx, mem_smoothNumbers_of_lpf_le hn1 hy⟩
  unfold shortBadCount
  refine (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans ?_)
  refine Nat.add_le_add_left ?_ _
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro p _
  exact card_biUnion_Icc_badSingletonsOfLpf_le (2 * x) p

/-- **Quantitative smooth/rough split**: the smooth part is bounded by
Mathlib's squareful-kernel estimate
`#{n ≤ x : (y+1)-smooth} ≤ 2^{π'(y+1)} · √x`, giving

`T_short(x) ≤ 2^{π'(y+1)}·√x +
  ∑_{p prime, y < p ≤ √(2x)} (2x / p²)·(2p + 1)`. -/
theorem shortBadCount_le_smooth_bound_add_prime_sum (x y : ℕ) :
    shortBadCount x ≤
      2 ^ Nat.primeCounting' (y + 1) * Nat.sqrt x +
      ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => y < p),
        (2 * x / p ^ 2) * (2 * p + 1) := by
  refine (shortBadCount_le_smooth_add_prime_sum x y).trans
    (Nat.add_le_add_right ?_ _)
  have h := Nat.smoothNumbersUpTo_card_le x (y + 1)
  rwa [Nat.primesBelow_card_eq_primeCounting'] at h

end JSP314
