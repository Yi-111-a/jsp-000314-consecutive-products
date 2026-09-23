import JSP314.ArcCount

/-!
# JSP-000314 — the small-prime / large-prime split of the smooth-arc count

This file splits `smoothArcCoveredCount x` (`JSP314.Reach`) into the two
`largestPrimeFactor` bands of the witnessing bad singleton `m`:

* `InSmoothArcSmall n Y` / `arcSmallCount x Y` — the witness `m` has
  `largestPrimeFactor m ≤ Y`;
* `InSmoothArcLarge n Y` / `arcLargeCount x Y` — the witness `m` has
  `Y < largestPrimeFactor m`.

## What is proved

* `inSmoothArcToSingleton_iff_small_or_large` — the pointwise dichotomy, hence
  `smoothArcCoveredCount_le_arcBands`:
  `smoothArcCoveredCount x ≤ arcSmallCount x Y + arcLargeCount x Y`.
* `arcSmallCount_le_prime_smooth_sum` — the `lpf`-fibers of the small band lie
  in `Nat.primesLE Y`, so adapting the resummation of `JSP314.ArcCount` gives
  `arcSmallCount x Y ≤ ∑_{p ≤ Y prime} (2p+1)·Ψ(2x/p², p+1)`.
* `arcSmallCount_le_explicit` — the **unconditional small-band bound**:
  `arcSmallCount x Y ≤ (Y+1)·(2Y+1)·2^{π'(Y+1)}·√(2x)`,
  using `Ψ(N, k) ≤ 2^{π'(k)}·√N` (`Nat.smoothNumbersUpTo_card_le`) and
  `π(Y) ≤ Y+1`; and the fully elementary corollary
  `arcSmallCount_le_pow` :
  `arcSmallCount x Y ≤ (Y+1)·(2Y+1)·2^{Y+1}·√(2x)`.
* `badNonSingletonCount_le_arcBands` — the assembled decomposition
  `badNonSingletonCount x ≤ arcSmallCount x Y + arcLargeCount x Y +
    smoothRunCoveredCount x`.

The mathematically hard residual is thereby isolated to the large-prime band
`arcLargeCount` (witnesses with `largestPrimeFactor m > Y`): for `Y` growing
slowly with `x` (e.g. `Y ≈ (log x)²`), the small band is `x^{1/2+o(1)}` by
`arcSmallCount_le_pow`, while `arcLargeCount` is where Tao's deep inputs are
needed.
-/

namespace JSP314

open Classical

section Bands

/-- `n` lies on a smooth arc to a bad singleton `m` whose largest prime factor
is at most `Y`: the *small-prime band* of `InSmoothArcToSingleton`. -/
def InSmoothArcSmall (n Y : ℕ) : Prop :=
  ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
    largestPrimeFactor m ≤ Y ∧ m ≤ 2 * n ∧
    (∀ j ∈ Finset.Icc (min n m) (max n m),
      largestPrimeFactor j ≤ largestPrimeFactor m) ∧
    n ≤ m + largestPrimeFactor m ∧ m ≤ n + largestPrimeFactor m

/-- `n` lies on a smooth arc to a bad singleton `m` whose largest prime factor
exceeds `Y`: the *large-prime band* of `InSmoothArcToSingleton`. -/
def InSmoothArcLarge (n Y : ℕ) : Prop :=
  ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
    Y < largestPrimeFactor m ∧ m ≤ 2 * n ∧
    (∀ j ∈ Finset.Icc (min n m) (max n m),
      largestPrimeFactor j ≤ largestPrimeFactor m) ∧
    n ≤ m + largestPrimeFactor m ∧ m ≤ n + largestPrimeFactor m

/-- Pointwise dichotomy on `largestPrimeFactor m ≤ Y`. -/
theorem inSmoothArcToSingleton_iff_small_or_large {n Y : ℕ} :
    InSmoothArcToSingleton n ↔
      InSmoothArcSmall n Y ∨ InSmoothArcLarge n Y := by
  constructor
  · rintro ⟨m, hm1, hmsq, hm2n, hsm, hnm, hmn⟩
    rcases Nat.lt_or_ge Y (largestPrimeFactor m) with h | h
    · exact Or.inr ⟨m, hm1, hmsq, h, hm2n, hsm, hnm, hmn⟩
    · exact Or.inl ⟨m, hm1, hmsq, h, hm2n, hsm, hnm, hmn⟩
  · rintro (⟨m, hm1, hmsq, -, hm2n, hsm, hnm, hmn⟩ |
      ⟨m, hm1, hmsq, -, hm2n, hsm, hnm, hmn⟩)
    · exact ⟨m, hm1, hmsq, hm2n, hsm, hnm, hmn⟩
    · exact ⟨m, hm1, hmsq, hm2n, hsm, hnm, hmn⟩

/-- `arcSmallCount x Y`: the number of `n ≤ x` on a smooth arc to a bad
singleton `m ≤ 2n` with `largestPrimeFactor m ≤ Y`. -/
noncomputable def arcSmallCount (x Y : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InSmoothArcSmall n Y).card

/-- `arcLargeCount x Y`: the number of `n ≤ x` on a smooth arc to a bad
singleton `m ≤ 2n` with `Y < largestPrimeFactor m`. -/
noncomputable def arcLargeCount (x Y : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun n => InSmoothArcLarge n Y).card

/-- The band split of the arc count:
`T_arc(x) ≤ T_arc^{≤Y}(x) + T_arc^{>Y}(x)`. -/
theorem smoothArcCoveredCount_le_arcBands (x Y : ℕ) :
    smoothArcCoveredCount x ≤ arcSmallCount x Y + arcLargeCount x Y := by
  unfold smoothArcCoveredCount arcSmallCount arcLargeCount
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  rcases inSmoothArcToSingleton_iff_small_or_large.mp hn.2 with h | h
  · exact Or.inl ⟨hn.1, h⟩
  · exact Or.inr ⟨hn.1, h⟩

end Bands

section SmallBand

/-- The bad singletons `≤ y` with largest prime factor `≤ Y`: the relevant
summation set for the small band. -/
noncomputable def badSingletonsBelowSmall (y Y : ℕ) : Finset ℕ :=
  (badSingletonsBelow y).filter (fun m => largestPrimeFactor m ≤ Y)

theorem mem_badSingletonsBelowSmall {y Y m : ℕ} :
    m ∈ badSingletonsBelowSmall y Y ↔
      m ≤ y ∧ 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
        largestPrimeFactor m ≤ Y := by
  simp only [badSingletonsBelowSmall, Finset.mem_filter,
    mem_badSingletonsBelow]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h3⟩, h4⟩

/-- Domination bound for the small band: each covered `n` lies in the window
`Icc (m - lpf m) (m + lpf m)` of a small-`lpf` bad singleton `m ≤ 2x`. -/
theorem arcSmallCount_le_sum (x Y : ℕ) :
    arcSmallCount x Y ≤
      ∑ m ∈ badSingletonsBelowSmall (2 * x) Y,
        (2 * largestPrimeFactor m + 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InSmoothArcSmall n Y) ⊆
      (badSingletonsBelowSmall (2 * x) Y).biUnion
        (fun m => Finset.Icc (m - largestPrimeFactor m)
          (m + largestPrimeFactor m)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, m, hm1, hmsq, hmY, hm2n, -, hnm, hmn⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [mem_badSingletonsBelowSmall]
      exact ⟨by omega, hm1, hmsq, hmY⟩
    · rw [Finset.mem_Icc]
      omega
  unfold arcSmallCount
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  exact Finset.sum_le_sum fun m _ => by rw [Nat.card_Icc]; omega

/-- `lpf` of a small-band bad singleton is a prime `≤ Y`. -/
theorem lpf_mem_primesLE_of_small {y Y m : ℕ}
    (hm : m ∈ badSingletonsBelowSmall y Y) :
    largestPrimeFactor m ∈ Nat.primesLE Y := by
  rw [mem_badSingletonsBelowSmall] at hm
  obtain ⟨-, hm1, -, hmY⟩ := hm
  exact Nat.mem_primesLE.mpr ⟨hmY, largestPrimeFactor_prime (by omega)⟩

/-- Re-summing an arbitrary function over `badSingletonsBelowSmall (2x) Y`
along the `largestPrimeFactor`-fibers, which land in `Nat.primesLE Y`. -/
theorem badSingletonsBelowSmall_sum_fiberwise {f : ℕ → ℕ} (x Y : ℕ) :
    ∑ m ∈ badSingletonsBelowSmall (2 * x) Y, f m =
      ∑ p ∈ Nat.primesLE Y,
        ∑ m ∈ (badSingletonsBelowSmall (2 * x) Y).filter
          (fun m => largestPrimeFactor m = p), f m :=
  (Finset.sum_fiberwise_of_maps_to
    (fun _ hm => lpf_mem_primesLE_of_small hm) f).symm

/-- Fiber bound for the small band: the `lpf = p` fiber of the small set is a
subset of the full `lpf = p` fiber, hence injects into the `(p+1)`-smooth
numbers `≤ 2x/p²` by `badSingletonsBelow_fiber_card_le`. -/
theorem badSingletonsBelowSmall_fiber_card_le {x Y p : ℕ} :
    ((badSingletonsBelowSmall (2 * x) Y).filter
        (fun m => largestPrimeFactor m = p)).card ≤
      (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  refine (Finset.card_le_card ?_).trans badSingletonsBelow_fiber_card_le
  intro m hm
  rw [Finset.mem_filter, mem_badSingletonsBelowSmall] at hm
  rw [Finset.mem_filter, mem_badSingletonsBelow]
  exact ⟨⟨hm.1.1, hm.1.2.1, hm.1.2.2.1⟩, hm.2⟩

/-- **Prime–smooth resummation for the small band**:
`arcSmallCount x Y ≤ ∑_{p ≤ Y prime} (2p+1)·Ψ(2x/p², p+1)`. -/
theorem arcSmallCount_le_prime_smooth_sum (x Y : ℕ) :
    arcSmallCount x Y ≤
      ∑ p ∈ Nat.primesLE Y,
        (2 * p + 1) *
          (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  refine (arcSmallCount_le_sum x Y).trans ?_
  rw [badSingletonsBelowSmall_sum_fiberwise]
  apply Finset.sum_le_sum
  intro p _
  calc ∑ m ∈ (badSingletonsBelowSmall (2 * x) Y).filter
        (fun m => largestPrimeFactor m = p), (2 * largestPrimeFactor m + 1)
      = ((badSingletonsBelowSmall (2 * x) Y).filter
          (fun m => largestPrimeFactor m = p)).card * (2 * p + 1) := by
        apply Finset.sum_const_nat
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
    _ ≤ (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card * (2 * p + 1) :=
        Nat.mul_le_mul badSingletonsBelowSmall_fiber_card_le (le_refl _)
    _ = (2 * p + 1) *
          (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
        Nat.mul_comm _ _

/-- `π'(n) ≤ n`: there are at most `n` primes below `n`. -/
theorem card_primesBelow_le (n : ℕ) : (Nat.primesBelow n).card ≤ n := by
  rw [Nat.primesBelow]
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- **Unconditional small-band bound**: inserting
`Ψ(N, p+1) ≤ 2^{π'(p+1)}·√N ≤ 2^{π'(Y+1)}·√(2x)`, `2p+1 ≤ 2Y+1`, and
`π(Y) ≤ Y+1` into `arcSmallCount_le_prime_smooth_sum` gives

`arcSmallCount x Y ≤ (Y+1)·(2Y+1)·2^{π'(Y+1)}·√(2x)`. -/
theorem arcSmallCount_le_explicit (x Y : ℕ) :
    arcSmallCount x Y ≤
      (Y + 1) *
        ((2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
          Nat.sqrt (2 * x)) := by
  refine (arcSmallCount_le_prime_smooth_sum x Y).trans ?_
  calc ∑ p ∈ Nat.primesLE Y,
        (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
      ≤ ∑ _p ∈ Nat.primesLE Y,
          ((2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
            Nat.sqrt (2 * x)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpY : p ≤ Y := Nat.le_of_mem_primesLE hp
        have h1 : (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card ≤
            2 ^ (Nat.primesBelow (Y + 1)).card * Nat.sqrt (2 * x) := by
          calc (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
              ≤ 2 ^ (Nat.primesBelow (p + 1)).card *
                  Nat.sqrt (2 * x / p ^ 2) :=
                Nat.smoothNumbersUpTo_card_le _ _
            _ ≤ 2 ^ (Nat.primesBelow (Y + 1)).card * Nat.sqrt (2 * x) := by
                apply Nat.mul_le_mul
                · exact Nat.pow_le_pow_right (by omega)
                    (Finset.card_le_card
                      (Nat.primesBelow_mono (by omega)))
                · exact Nat.sqrt_le_sqrt (Nat.div_le_self _ _)
        calc (2 * p + 1) *
              (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
            ≤ (2 * p + 1) * (2 ^ (Nat.primesBelow (Y + 1)).card *
                Nat.sqrt (2 * x)) :=
              Nat.mul_le_mul (le_refl _) h1
          _ ≤ (2 * Y + 1) * (2 ^ (Nat.primesBelow (Y + 1)).card *
                Nat.sqrt (2 * x)) :=
              Nat.mul_le_mul (by omega) (le_refl _)
          _ = (2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
                Nat.sqrt (2 * x) := by ring
    _ = (Nat.primesLE Y).card *
          ((2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
            Nat.sqrt (2 * x)) := by
        exact Finset.sum_const_nat (fun _ _ => rfl)
    _ ≤ (Y + 1) *
          ((2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
            Nat.sqrt (2 * x)) :=
        Nat.mul_le_mul (primesLE_card_le Y) (le_refl _)

/-- **Fully elementary corollary**: since `π'(Y+1) ≤ Y+1`,

`arcSmallCount x Y ≤ (Y+1)·(2Y+1)·2^{Y+1}·√(2x)`.

For `Y` growing slower than any positive power of `x` (e.g. `Y = (log x)²`)
this is `x^{1/2+o(1)}`, so the small-prime band is unconditionally negligible;
only the large-prime band `arcLargeCount` remains. -/
theorem arcSmallCount_le_pow (x Y : ℕ) :
    arcSmallCount x Y ≤
      (Y + 1) * (2 * Y + 1) * 2 ^ (Y + 1) * Nat.sqrt (2 * x) := by
  refine (arcSmallCount_le_explicit x Y).trans ?_
  have h : 2 ^ (Nat.primesBelow (Y + 1)).card ≤ 2 ^ (Y + 1) :=
    Nat.pow_le_pow_right (by omega) (card_primesBelow_le _)
  calc (Y + 1) * ((2 * Y + 1) * 2 ^ (Nat.primesBelow (Y + 1)).card *
        Nat.sqrt (2 * x))
      ≤ (Y + 1) * ((2 * Y + 1) * 2 ^ (Y + 1) * Nat.sqrt (2 * x)) :=
        Nat.mul_le_mul (le_refl _)
          (Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) h) (le_refl _))
    _ = (Y + 1) * (2 * Y + 1) * 2 ^ (Y + 1) * Nat.sqrt (2 * x) := by ring

end SmallBand

/-- **Assembled decomposition**: the non-singleton bad count splits into the
small-prime arc band, the large-prime arc band, and the smooth-run count:

`badNonSingletonCount x ≤ arcSmallCount x Y + arcLargeCount x Y +
  smoothRunCoveredCount x`.

The small band is unconditionally `≤ (Y+1)·(2Y+1)·2^{Y+1}·√(2x)`
(`arcSmallCount_le_pow`); the residual mathematical difficulty is exactly
`arcLargeCount x Y`, witnesses with `largestPrimeFactor m > Y`. -/
theorem badNonSingletonCount_le_arcBands (x Y : ℕ) :
    badNonSingletonCount x ≤
      arcSmallCount x Y + arcLargeCount x Y + smoothRunCoveredCount x := by
  have h1 := badNonSingletonCount_le_short_add_smooth x
  have h2 := shortBadCount_le_smoothArcCoveredCount x
  have h3 := smoothArcCoveredCount_le_arcBands x Y
  omega

end JSP314
