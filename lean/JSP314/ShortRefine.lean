import JSP314.Dominant

/-!
# JSP-000314 — dominant-singleton refinement of the short-interval count

The union bound in `JSP314.ShortCount` charges each bad singleton `m ≤ 2x`
with `largestPrimeFactor m = p` for *all* `2p + 1` integers of the covering
window `[m − p, m + p]`.  The dominant-singleton theorem
`shortBadCovered_dominant` says more: a covered point `n` in that window is
either `m` itself or strictly smoother than `m`, i.e.
`largestPrimeFactor n < p`, so `n` is `p`-smooth in Mathlib's strict sense
(all prime factors `< p`).  This file replaces the `2p + 1` factor by the
count of `p`-smooth points of the window, plus the singleton `m` itself.

**Note.**  This file imports `JSP314.Dominant` only and reproduces the
`badSingletonsOfLpf` API of `JSP314.ShortCount` (same names and statements,
proofs adjusted for this toolchain), because `JSP314.ShortCount` currently
does not elaborate against Mathlib v4.34.0 (implicit-argument synthesis
failures in `card_badSingletonsOfLpf_le` and
`card_biUnion_Icc_badSingletonsOfLpf_le`).

## Contents

* `badSingletonsOfLpf B p`, `mem_badSingletonsOfLpf`,
  `card_badSingletonsOfLpf_le`: the bad singletons `≤ B` with `lpf m = p`
  and the `B / p²` cardinality bound (as in `JSP314.ShortCount`).
* `shortBadCovered_subset_biUnion_smooth`: the refined covering — every
  short-covered `n ≤ x` lies in the "smooth-or-self" filtered window of a
  bad singleton `m ≤ 2x` with `lpf m = p ≤ √(2x)` prime.
* `shortBadCount_le_sum_smooth_card` (**Target 1**):
  `T_short(x) ≤ ∑_{p ≤ √(2x), p prime} ∑_{m ∈ badSingletonsOfLpf (2x) p}
    #((Icc (m − p) (m + p)).filter (lpf · < p ∨ · = m))`.
* `card_Icc_filter_smooth_or_self_le` (**Target 2**): for `p < m` the
  filtered window is contained in
  `Nat.smoothNumbersUpTo (m + p) p ∪ {m}`, hence has cardinality
  `≤ #(smoothNumbersUpTo (m + p) p) + 1`.
* `window_card_le`: the same with the uniform bound `2x + p`.
* `shortBadCount_le_sum_card_mul_smooth_card` and
  `shortBadCount_le_prime_smooth_card` (**Target 3**): the assembled bounds
  `T_short(x) ≤ ∑_p #(badSingletonsOfLpf (2x) p) · (Ψ(2x+p, p) + 1)
             ≤ ∑_p (2x/p²) · (Ψ(2x+p, p) + 1)`,
  where `Ψ(N, p) := #(Nat.smoothNumbersUpTo N p)`.
* `shortBadCount_le_prime_smooth_bound`: the closed form obtained from
  `Nat.smoothNumbersUpTo_card_le`,
  `T_short(x) ≤ ∑_p (2x/p²) · (2^{π'(p)}·√(2x+p) + 1)`.

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
    have hcard : (badSingletonsOfLpf B p).card ≤
        (Finset.Icc 1 (B / p ^ 2)).card := by
      refine Finset.card_le_card_of_injOn (fun m => m / p ^ 2) ?_ ?_
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
    rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
    exact hcard

/-- **Refined covering**: every point `n ≤ x` covered by a short bad interval
lies in the window `[m − p, m + p]` of a bad singleton `m ≤ 2x` with
`lpf m = p`, and is either equal to `m` or strictly smoother
(`lpf n < p`).  Hence the covered set is contained in the biUnion over
primes `p ≤ √(2x)` and singletons `m` of the "smooth-or-self" filtered
windows. -/
theorem shortBadCovered_subset_biUnion_smooth (x : ℕ) :
    (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      (Nat.primesLE (Nat.sqrt (2 * x))).biUnion (fun p =>
        (badSingletonsOfLpf (2 * x) p).biUnion (fun m =>
          (Finset.Icc (m - p) (m + p)).filter
            (fun n => largestPrimeFactor n < p ∨ n = m))) := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨hnx, hsh⟩ := hn
  obtain ⟨m, hm1, hmsq, hm2x, hnlt, _hbetween, hnhi, hmlo⟩ :=
    shortBadCovered_dominant hsh (Nat.lt_add_one_iff.mp hnx)
  rw [Finset.mem_biUnion]
  refine ⟨largestPrimeFactor m, ?_, ?_⟩
  · rw [Nat.mem_primesLE]
    exact ⟨(lpf_le_sqrt_of_sq_dvd hm1 hmsq).trans (Nat.sqrt_le_sqrt hm2x),
      largestPrimeFactor_prime (by omega)⟩
  · rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [mem_badSingletonsOfLpf]
      exact ⟨hm2x, hm1, hmsq, rfl⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rcases eq_or_ne n m with rfl | hne
      · exact Or.inr rfl
      · exact Or.inl (hnlt hne)

/-- **Target 1** — the union bound with the `(2p + 1)` factor replaced by the
actual "smooth-or-self" count of each covering window:

`T_short(x) ≤ ∑_{p ≤ √(2x), p prime} ∑_{m ∈ badSingletonsOfLpf (2x) p}
  #((Icc (m − p) (m + p)).filter (fun n => lpf n < p ∨ n = m))`. -/
theorem shortBadCount_le_sum_smooth_card (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ m ∈ badSingletonsOfLpf (2 * x) p,
          ((Finset.Icc (m - p) (m + p)).filter
            (fun n => largestPrimeFactor n < p ∨ n = m)).card := by
  unfold shortBadCount
  refine (Finset.card_le_card
    (shortBadCovered_subset_biUnion_smooth x)).trans
      (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro p _
  exact Finset.card_biUnion_le

/-- Monotonicity of `Nat.smoothNumbersUpTo` in the cutoff. -/
theorem smoothNumbersUpTo_subset_of_le {N N' k : ℕ} (h : N ≤ N') :
    Nat.smoothNumbersUpTo N k ⊆ Nat.smoothNumbersUpTo N' k := by
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans h, hn.2⟩

/-- **Target 2** — when `p < m` (so the window `[m − p, m + p]` stays
positive), every element of the "smooth-or-self" filtered window is either
`p`-smooth and `≤ m + p`, or equal to `m` itself; hence its cardinality is
at most `#(smoothNumbersUpTo (m + p) p) + 1`. -/
theorem card_Icc_filter_smooth_or_self_le {m p : ℕ} (hpm : p < m) :
    ((Finset.Icc (m - p) (m + p)).filter
        (fun n => largestPrimeFactor n < p ∨ n = m)).card ≤
      (Nat.smoothNumbersUpTo (m + p) p).card + 1 := by
  have hsub : (Finset.Icc (m - p) (m + p)).filter
        (fun n => largestPrimeFactor n < p ∨ n = m) ⊆
      Nat.smoothNumbersUpTo (m + p) p ∪ {m} := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hmn, hnm⟩, hsm⟩ := hn
    rw [Finset.mem_union]
    rcases hsm with hlt | rfl
    · -- `lpf n < p`: `n` is `p`-smooth (all prime factors `< p`).
      refine Or.inl ?_
      rw [Nat.mem_smoothNumbersUpTo]
      have hn1 : 1 ≤ n := by omega
      have hle : largestPrimeFactor n ≤ p - 1 := by omega
      have hsm' := mem_smoothNumbers_of_lpf_le hn1 hle
      have hp1 : p - 1 + 1 = p := by omega
      rw [hp1] at hsm'
      exact ⟨hnm, hsm'⟩
    · exact Or.inr (Finset.mem_singleton_self _)
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  exact Nat.add_le_add_left (Finset.card_singleton m).le _

/-- The filtered window of a bad singleton `m ≤ 2x` with `lpf m = p` has at
most `#(smoothNumbersUpTo (2x + p) p) + 1` elements: bad singletons satisfy
`p² ∣ m`, hence `p < m`, so `card_Icc_filter_smooth_or_self_le` applies,
and `m + p ≤ 2x + p`. -/
theorem window_card_le {x p m : ℕ}
    (hm : m ∈ badSingletonsOfLpf (2 * x) p) :
    ((Finset.Icc (m - p) (m + p)).filter
        (fun n => largestPrimeFactor n < p ∨ n = m)).card ≤
      (Nat.smoothNumbersUpTo (2 * x + p) p).card + 1 := by
  rw [mem_badSingletonsOfLpf] at hm
  obtain ⟨hmB, hm1, hmsq, hmeq⟩ := hm
  have hdvd : p ^ 2 ∣ m := hmeq ▸ hmsq
  have hpm2 : p ^ 2 ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hp2 : 2 ≤ p := by
    have h := largestPrimeFactor_prime (show 2 ≤ m by omega)
    rw [hmeq] at h
    exact h.two_le
  have hpm : p < m := by
    have hpp : p < p ^ 2 := by
      rw [pow_two]
      calc p < 2 * p := by omega
        _ ≤ p * p := Nat.mul_le_mul hp2 (le_refl p)
    exact hpp.trans_le hpm2
  refine (card_Icc_filter_smooth_or_self_le hpm).trans ?_
  exact Nat.add_le_add_right
    (Finset.card_le_card
      (smoothNumbersUpTo_subset_of_le (show m + p ≤ 2 * x + p by omega))) 1

/-- **Target 3 (exact-count form)** — grouping the refined window bound over
the singletons of each prime:

`T_short(x) ≤ ∑_{p ≤ √(2x), p prime}
  #(badSingletonsOfLpf (2x) p) · (#(smoothNumbersUpTo (2x + p) p) + 1)`. -/
theorem shortBadCount_le_sum_card_mul_smooth_card (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (badSingletonsOfLpf (2 * x) p).card *
          ((Nat.smoothNumbersUpTo (2 * x + p) p).card + 1) := by
  refine (shortBadCount_le_sum_smooth_card x).trans ?_
  apply Finset.sum_le_sum
  intro p _
  exact le_of_le_of_eq
    (Finset.sum_le_card_nsmul _ _ _ (fun m hm => window_card_le hm))
    (Nat.nsmul_eq_mul _ _)

/-- **Target 3 (closed form)** — bounding the singleton count by `2x / p²`:

`T_short(x) ≤ ∑_{p ≤ √(2x), p prime}
  (2x / p²) · (#(smoothNumbersUpTo (2x + p) p) + 1)`. -/
theorem shortBadCount_le_prime_smooth_card (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * x / p ^ 2) *
          ((Nat.smoothNumbersUpTo (2 * x + p) p).card + 1) := by
  refine (shortBadCount_le_sum_card_mul_smooth_card x).trans ?_
  apply Finset.sum_le_sum
  intro p _
  exact Nat.mul_le_mul (card_badSingletonsOfLpf_le (2 * x) p) le_rfl

/-- **Quantitative closed form**: via Mathlib's squareful-kernel estimate
`#(smoothNumbersUpTo N k) ≤ 2^{π'(k)}·√N`,

`T_short(x) ≤ ∑_{p ≤ √(2x), p prime}
  (2x / p²) · (2^{π'(p)}·√(2x + p) + 1)`. -/
theorem shortBadCount_le_prime_smooth_bound (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * x / p ^ 2) *
          (2 ^ Nat.primeCounting' p * Nat.sqrt (2 * x + p) + 1) := by
  refine (shortBadCount_le_prime_smooth_card x).trans ?_
  apply Finset.sum_le_sum
  intro p _
  refine Nat.mul_le_mul le_rfl (Nat.add_le_add_right ?_ 1)
  have h := Nat.smoothNumbersUpTo_card_le (2 * x + p) p
  rwa [Nat.primesBelow_card_eq_primeCounting'] at h

end JSP314
