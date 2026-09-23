import JSP314.Reach
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# JSP-000314 — verified bounds on `smoothArcCoveredCount`

This file develops *unconditional* bounds on `smoothArcCoveredCount x`, the
number of `n ≤ x` lying on a `P(m)`-smooth arc to a bad singleton `m ≤ 2n`
(`JSP314.Reach`).  Recall that `shortBadCount x ≤ smoothArcCoveredCount x`
(`shortBadCount_le_smoothArcCoveredCount`), so every bound proved here applies
to the short component of the short/long decomposition
`badNonSingletonCount_le_short_add_smooth`.

## What is proved

* `smoothArcCoveredCount_le_sum` — **domination bound (a)**: every covered `n`
  lies in the window `Icc (m - lpf m) (m + lpf m)` around a bad singleton
  `m ≤ 2x`, so
  `smoothArcCoveredCount x ≤ ∑_{m ≤ 2x, (lpf m)² ∣ m} (2·lpf m + 1)`.
* `smoothArcCoveredCount_le_badSingleton_mul_sqrt` — the coarse corollary
  `smoothArcCoveredCount x ≤ S(2x)·(2√(2x) + 1)` (extending
  `shortBadCount_le` to the whole arc count).
* `badSingleton_decomp` — **kernel decomposition (c)**: a bad singleton
  `m = p²·t` with `p = lpf m` prime and `t = m/p²` a `(p+1)`-smooth
  ("`p`-smooth") kernel; `badSingletonsBelow_fiber_card_le` — the fiber
  `lpf m = p` injects via `m ↦ m/p²` into `smoothNumbersUpTo (2x/p²) (p+1)`.
* `sum_lpf_badSingletonsBelow_le`, `badSingletonCount_le_smooth_sum`,
  `smoothArcCoveredCount_le_prime_smooth_sum` — **resummation (b)**: re-summing
  over `lpf`-fibers gives
  `smoothArcCoveredCount x ≤ ∑_{p ≤ √(2x) prime} (2p+1)·Ψ(2x/p², p)`
  and `S(2x) ≤ ∑_{p ≤ √(2x)} Ψ(2x/p², p)`, where `Ψ(N, p)` counts
  `(p+1)`-smooth numbers `≤ N`.  This is exactly the analytic object that
  remains to be estimated for Ta26c.
* `smoothArcCoveredCount_le_explicit` — inserting Mathlib's squarefree-kernel
  bound `Nat.smoothNumbersUpTo_card_le` yields the fully explicit (weak) bound
  `≤ √(2x) · ∑_{p ≤ √(2x)} (2p+1)·2^{π'(p+1)}`.
* `sum_primesLE_div_le` — a dyadic estimate `∑_{p ≤ Y} N/p ≤ N·(log₂ Y + 1)`;
  combined with the trivial `Ψ(N, k) ≤ N + 1` this gives the headline
  quantitative corollary `smoothArcCoveredCount_le_log_bound`:

  `smoothArcCoveredCount x ≤ 6x·(log₂ √(2x) + 1) + (√(2x)+1)·(2√(2x)+1)`,

  i.e. `smoothArcCoveredCount x = O(x·log x)` — within a `log x / loglog x`
  factor of the true order `≈ x·loglog x` of `∑_{m ≤ 2x} lpf m`.

## Asymptotic strength

The residual lemma `badNonSingleton_interval_bound` asks for
`(log x)^{-1+ε}·S(x)`.  The bounds here are honest partial results: they
reduce the arc count to an explicit prime-by-prime smooth-number sum and give
an unconditional `O(x log x)` estimate, but they do not reach the
`(log x)^{-1+ε}·S(x)` target — that requires the much deeper inputs of Tao's
argument (e.g. fine control of `Ψ(2x/p², p)` weighted against the size of
`S(x)`).
-/

namespace JSP314

open Classical

/-- The bad singletons `≤ y`: `m` with `1 < m` and `(lpf m)² ∣ m`.  This is the
finset counted by `badSingletonCount y`. -/
noncomputable def badSingletonsBelow (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m)

theorem mem_badSingletonsBelow {y m : ℕ} :
    m ∈ badSingletonsBelow y ↔
      m ≤ y ∧ 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m := by
  simp [badSingletonsBelow]

theorem card_badSingletonsBelow (y : ℕ) :
    (badSingletonsBelow y).card = badSingletonCount y := rfl

section Domination

/-- **Domination bound (a)**: each `n` on a smooth arc to a bad singleton `m`
satisfies `m - lpf m ≤ n ≤ m + lpf m`, a window of `2·lpf m + 1` integers.
Counting the union of windows gives
`smoothArcCoveredCount x ≤ ∑_{m ≤ 2x, (lpf m)² ∣ m} (2·lpf m + 1)`. -/
theorem smoothArcCoveredCount_le_sum (x : ℕ) :
    smoothArcCoveredCount x ≤
      ∑ m ∈ badSingletonsBelow (2 * x), (2 * largestPrimeFactor m + 1) := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InSmoothArcToSingleton n) ⊆
      (badSingletonsBelow (2 * x)).biUnion
        (fun m => Finset.Icc (m - largestPrimeFactor m)
          (m + largestPrimeFactor m)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, m, hm1, hmsq, hm2n, -, hnm, hmn⟩ := hn
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · rw [mem_badSingletonsBelow]
      exact ⟨by omega, hm1, hmsq⟩
    · rw [Finset.mem_Icc]
      omega
  unfold smoothArcCoveredCount
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  exact Finset.sum_le_sum fun m _ => by rw [Nat.card_Icc]; omega

/-- **Coarse bound**: `lpf m ≤ √m ≤ √(2x)` on the summation range, hence
`smoothArcCoveredCount x ≤ S(2x)·(2√(2x) + 1)`. -/
theorem smoothArcCoveredCount_le_badSingleton_mul_sqrt (x : ℕ) :
    smoothArcCoveredCount x ≤
      badSingletonCount (2 * x) * (2 * Nat.sqrt (2 * x) + 1) := by
  refine (smoothArcCoveredCount_le_sum x).trans ?_
  rw [← card_badSingletonsBelow]
  calc ∑ m ∈ badSingletonsBelow (2 * x), (2 * largestPrimeFactor m + 1)
      ≤ ∑ _m ∈ badSingletonsBelow (2 * x), (2 * Nat.sqrt (2 * x) + 1) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [mem_badSingletonsBelow] at hm
        obtain ⟨hm2x, hm1, hmsq⟩ := hm
        have h1 := lpf_le_sqrt_of_sq_dvd hm1 hmsq
        have h2 := Nat.sqrt_le_sqrt hm2x
        omega
    _ = (badSingletonsBelow (2 * x)).card * (2 * Nat.sqrt (2 * x) + 1) := by
        rw [Finset.sum_const]
        simp

end Domination

section Decomposition

/-- **Kernel decomposition**: if `m > 1` and `(lpf m)² ∣ m`, then with
`p = lpf m` (prime) and `t = m / p²` we have `p² ≤ m`, `m = p²·t`, and `t` is
`(p + 1)`-smooth — every prime divisor of `t` is a prime divisor of `m`, hence
`≤ lpf m = p < p + 1`. -/
theorem badSingleton_decomp {m : ℕ} (hm : 1 < m)
    (hdvd : (largestPrimeFactor m) ^ 2 ∣ m) :
    Nat.Prime (largestPrimeFactor m) ∧
      (largestPrimeFactor m) ^ 2 ≤ m ∧
      m = (largestPrimeFactor m) ^ 2 * (m / (largestPrimeFactor m) ^ 2) ∧
      m / (largestPrimeFactor m) ^ 2 ∈
        Nat.smoothNumbers (largestPrimeFactor m + 1) := by
  have hm2 : 2 ≤ m := hm
  have hprime := largestPrimeFactor_prime hm2
  have hle : (largestPrimeFactor m) ^ 2 ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hm_eq : m =
      (largestPrimeFactor m) ^ 2 * (m / (largestPrimeFactor m) ^ 2) :=
    (Nat.mul_div_cancel' hdvd).symm
  have hsmooth : m / (largestPrimeFactor m) ^ 2 ∈
      Nat.smoothNumbers (largestPrimeFactor m + 1) := by
    rw [Nat.mem_smoothNumbers']
    intro q hq hqdt
    have htdvd : m / (largestPrimeFactor m) ^ 2 ∣ m :=
      ⟨(largestPrimeFactor m) ^ 2, (Nat.div_mul_cancel hdvd).symm⟩
    have hqm : q ∣ m := hqdt.trans htdvd
    have hqle : q ≤ largestPrimeFactor m :=
      prime_dvd_le_largestPrimeFactor hm2 hq hqm
    omega
  exact ⟨hprime, hle, hm_eq, hsmooth⟩

/-- `lpf` of a bad singleton `m ≤ y` is a prime `≤ √y`. -/
theorem lpf_mem_primesLE_sqrt {y m : ℕ} (hm : m ∈ badSingletonsBelow y) :
    largestPrimeFactor m ∈ Nat.primesLE (Nat.sqrt y) := by
  rw [mem_badSingletonsBelow] at hm
  obtain ⟨hmy, hm1, hmsq⟩ := hm
  rw [Nat.mem_primesLE]
  refine ⟨?_, largestPrimeFactor_prime (by omega)⟩
  rw [Nat.le_sqrt']
  exact (Nat.le_of_dvd (by omega) hmsq).trans hmy

/-- **Fiber bound**: for prime `p`, the bad singletons `m ≤ 2x` with
`lpf m = p` inject into the `(p+1)`-smooth numbers `t ≤ 2x / p²` via
`m ↦ m / p²` (injectivity because `m = p²·t` on this fiber). -/
theorem badSingletonsBelow_fiber_card_le {x p : ℕ} :
    ((badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p)).card ≤
      (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, Finset.mem_filter, mem_badSingletonsBelow] at hm
    obtain ⟨⟨hm2x, hm1, hmsq⟩, hlpf⟩ := hm
    obtain ⟨-, -, -, hsmooth⟩ := badSingleton_decomp hm1 hmsq
    rw [hlpf] at hsmooth
    rw [Finset.mem_coe, Nat.mem_smoothNumbersUpTo]
    exact ⟨Nat.div_le_div_right hm2x, hsmooth⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, mem_badSingletonsBelow] at ha hb
    obtain ⟨⟨-, ha1, hasq⟩, hpa⟩ := ha
    obtain ⟨⟨-, hb1, hbsq⟩, hpb⟩ := hb
    have ha' := (badSingleton_decomp ha1 hasq).2.2.1
    have hb' := (badSingleton_decomp hb1 hbsq).2.2.1
    rw [hpa] at ha'
    rw [hpb] at hb'
    have hab2 : a / p ^ 2 = b / p ^ 2 := hab
    calc a = p ^ 2 * (a / p ^ 2) := ha'
      _ = p ^ 2 * (b / p ^ 2) := by rw [hab2]
      _ = b := hb'.symm

/-- Re-summing an arbitrary function over `badSingletonsBelow (2x)` along the
fibers of `largestPrimeFactor` (which lands in `primesLE √(2x)`). -/
theorem badSingletonsBelow_sum_fiberwise {f : ℕ → ℕ} (x : ℕ) :
    ∑ m ∈ badSingletonsBelow (2 * x), f m =
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        ∑ m ∈ (badSingletonsBelow (2 * x)).filter
          (fun m => largestPrimeFactor m = p), f m :=
  (Finset.sum_fiberwise_of_maps_to
    (fun _ hm => lpf_mem_primesLE_sqrt hm) f).symm

end Decomposition

section Resummation

/-- The weighted `lpf`-sum over bad singletons is dominated by the
prime-by-prime smooth-kernel counts:
`∑_{m ≤ 2x, (lpf m)² ∣ m} lpf m ≤ ∑_{p ≤ √(2x)} p·Ψ(2x/p², p)`. -/
theorem sum_lpf_badSingletonsBelow_le (x : ℕ) :
    ∑ m ∈ badSingletonsBelow (2 * x), largestPrimeFactor m ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        p * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  rw [badSingletonsBelow_sum_fiberwise]
  apply Finset.sum_le_sum
  intro p hp
  calc ∑ m ∈ (badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p), largestPrimeFactor m
      = ((badSingletonsBelow (2 * x)).filter
          (fun m => largestPrimeFactor m = p)).card * p := by
        apply Finset.sum_const_nat
        intro k hk
        exact (Finset.mem_filter.mp hk).2
    _ ≤ (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card * p :=
        Nat.mul_le_mul badSingletonsBelow_fiber_card_le (le_refl _)
    _ = p * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
        Nat.mul_comm _ _

/-- The bad-singleton count itself is bounded by the smooth-kernel counts:
`S(2x) ≤ ∑_{p ≤ √(2x)} Ψ(2x/p², p)`. -/
theorem badSingletonCount_le_smooth_sum (x : ℕ) :
    badSingletonCount (2 * x) ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  rw [← card_badSingletonsBelow, Finset.card_eq_sum_ones,
    badSingletonsBelow_sum_fiberwise]
  apply Finset.sum_le_sum
  intro p hp
  calc ∑ _m ∈ (badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p), (1 : ℕ)
      = ((badSingletonsBelow (2 * x)).filter
          (fun m => largestPrimeFactor m = p)).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
    _ ≤ (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
        badSingletonsBelow_fiber_card_le

/-- **Prime–smooth resummation (b)**: the window bound of (a) summed over the
`lpf`-fibers gives
`smoothArcCoveredCount x ≤ ∑_{p ≤ √(2x)} (2p+1)·Ψ(2x/p², p)`
where `Ψ(N, p) = (smoothNumbersUpTo N (p+1)).card` counts `p`-smooth `t ≤ N`
(the kernels `t = m/p²` of bad singletons `m ≤ 2x` with `lpf m = p`). -/
theorem smoothArcCoveredCount_le_prime_smooth_sum (x : ℕ) :
    smoothArcCoveredCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card := by
  refine (smoothArcCoveredCount_le_sum x).trans ?_
  rw [badSingletonsBelow_sum_fiberwise]
  apply Finset.sum_le_sum
  intro p hp
  calc ∑ m ∈ (badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p), (2 * largestPrimeFactor m + 1)
      = ((badSingletonsBelow (2 * x)).filter
          (fun m => largestPrimeFactor m = p)).card * (2 * p + 1) := by
        apply Finset.sum_const_nat
        intro k hk
        rw [(Finset.mem_filter.mp hk).2]
    _ ≤ (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card * (2 * p + 1) :=
        Nat.mul_le_mul badSingletonsBelow_fiber_card_le (le_refl _)
    _ = (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
        Nat.mul_comm _ _

/-- **Fully explicit (weak) bound**: Mathlib's squarefree-kernel estimate
`Nat.smoothNumbersUpTo_card_le` gives `Ψ(N, k) ≤ 2^{π'(k)}·√N`, hence
`smoothArcCoveredCount x ≤ √(2x)·∑_{p ≤ √(2x)} (2p+1)·2^{π'(p+1)}`. -/
theorem smoothArcCoveredCount_le_explicit (x : ℕ) :
    smoothArcCoveredCount x ≤
      Nat.sqrt (2 * x) *
        ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (2 * p + 1) * 2 ^ (Nat.primesBelow (p + 1)).card := by
  refine (smoothArcCoveredCount_le_prime_smooth_sum x).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  calc (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
      ≤ (2 * p + 1) *
          (2 ^ (Nat.primesBelow (p + 1)).card * Nat.sqrt (2 * x / p ^ 2)) :=
        Nat.mul_le_mul (le_refl _) (Nat.smoothNumbersUpTo_card_le _ _)
    _ ≤ (2 * p + 1) *
          (2 ^ (Nat.primesBelow (p + 1)).card * Nat.sqrt (2 * x)) :=
        Nat.mul_le_mul (le_refl _)
          (Nat.mul_le_mul (le_refl _)
            (Nat.sqrt_le_sqrt (Nat.div_le_self _ _)))
    _ = Nat.sqrt (2 * x) *
          ((2 * p + 1) * 2 ^ (Nat.primesBelow (p + 1)).card) := by ring

end Resummation

section LogBound

/-- Trivial bound on smooth-number counts: `Ψ(N, k) ≤ N + 1`. -/
theorem smoothNumbersUpTo_card_le_add_one (N k : ℕ) :
    (Nat.smoothNumbersUpTo N k).card ≤ N + 1 := by
  calc (Nat.smoothNumbersUpTo N k).card
      ≤ (Finset.range (N + 1)).card := by
        apply Finset.card_le_card
        intro n hn
        rw [Nat.mem_smoothNumbersUpTo] at hn
        exact Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr hn.1)
    _ = N + 1 := Finset.card_range _

/-- `π(Y) ≤ Y + 1`. -/
theorem primesLE_card_le (Y : ℕ) : (Nat.primesLE Y).card ≤ Y + 1 := by
  rw [Nat.primesLE_eq_filter_range]
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- Re-summing over `primesLE Y` along the fibers of `Nat.log 2`. -/
theorem primesLE_sum_fiberwise_log {f : ℕ → ℕ} (Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, f p =
      ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
        ∑ p ∈ (Nat.primesLE Y).filter (fun p => Nat.log 2 p = j), f p := by
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro p hp
  rw [Finset.mem_range, Nat.lt_add_one_iff]
  exact Nat.log_mono_right (Nat.le_of_mem_primesLE hp)

/-- The fiber `{p ≤ Y prime : log₂ p = j}` lies in `Ico (2^j) (2^{j+1})`,
hence has at most `2^j` elements. -/
theorem primesLE_log_fiber_card_le {Y j : ℕ} :
    ((Nat.primesLE Y).filter (fun p => Nat.log 2 p = j)).card ≤ 2 ^ j := by
  have hsub : (Nat.primesLE Y).filter (fun p => Nat.log 2 p = j) ⊆
      Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ico]
    have hpp := Nat.prime_of_mem_primesLE hp.1
    have h1 : 2 ^ Nat.log 2 p ≤ p := Nat.pow_log_le_self 2 hpp.pos.ne'
    have h2 : p < 2 ^ (Nat.log 2 p + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) p
    rw [hp.2] at h1 h2
    exact ⟨h1, h2⟩
  refine (Finset.card_le_card hsub).trans_eq ?_
  rw [Nat.card_Ico]
  have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; ring
  rw [hpow]
  exact add_tsub_cancel_right _ _

/-- **Dyadic estimate**: `∑_{p ≤ Y prime} N / p ≤ N·(log₂ Y + 1)`.
This is the elementary input that upgrades the smooth-kernel bound to an
`O(N log Y)` estimate. -/
theorem sum_primesLE_div_le (N Y : ℕ) :
    ∑ p ∈ Nat.primesLE Y, N / p ≤ N * (Nat.log 2 Y + 1) := by
  calc ∑ p ∈ Nat.primesLE Y, N / p
      ≤ ∑ p ∈ Nat.primesLE Y, N / 2 ^ Nat.log 2 p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := Nat.prime_of_mem_primesLE hp
        exact Nat.div_le_div_left
          (Nat.pow_log_le_self 2 hpp.pos.ne') (Nat.pow_pos (by norm_num))
    _ = ∑ j ∈ Finset.range (Nat.log 2 Y + 1),
          ∑ p ∈ (Nat.primesLE Y).filter (fun p => Nat.log 2 p = j),
            N / 2 ^ Nat.log 2 p :=
        primesLE_sum_fiberwise_log Y
    _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 Y + 1), N := by
        apply Finset.sum_le_sum
        intro j _
        calc ∑ p ∈ (Nat.primesLE Y).filter (fun p => Nat.log 2 p = j),
              N / 2 ^ Nat.log 2 p
            = ((Nat.primesLE Y).filter
                (fun p => Nat.log 2 p = j)).card * (N / 2 ^ j) := by
              apply Finset.sum_const_nat
              intro k hk
              rw [(Finset.mem_filter.mp hk).2]
          _ ≤ 2 ^ j * (N / 2 ^ j) :=
              Nat.mul_le_mul primesLE_log_fiber_card_le (le_refl _)
          _ ≤ N := Nat.mul_div_le _ _
    _ = N * (Nat.log 2 Y + 1) := by
        rw [Finset.sum_const_nat (s := Finset.range (Nat.log 2 Y + 1))
              (f := fun _ => N) (fun _ _ => rfl),
          Finset.card_range]
        exact Nat.mul_comm _ _

/-- Per-prime term bound: `(2p+1)·Ψ(2x/p², p) ≤ 3·(2x/p) + (2p+1)` for prime
`p`, using `Ψ ≤ 2x/p² + 1`, `p·(2x/p²) ≤ 2x/p` and `2x/p² ≤ 2x/p`. -/
theorem prime_smooth_term_le {x p : ℕ} (hp : Nat.Prime p) :
    (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card ≤
      3 * (2 * x / p) + (2 * p + 1) := by
  have hpp : 0 < p := hp.pos
  have hA : (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card ≤
      2 * x / p ^ 2 + 1 := smoothNumbersUpTo_card_le_add_one _ _
  have hmul : p * (2 * x / p ^ 2) ≤ 2 * x / p := by
    have h : 2 * x / p ^ 2 = (2 * x / p) / p := by
      rw [Nat.div_div_eq_div_mul, pow_two]
    rw [h, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hA2 : 2 * x / p ^ 2 ≤ 2 * x / p :=
    Nat.div_le_div_left (Nat.le_self_pow two_ne_zero p) hpp
  calc (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
      ≤ (2 * p + 1) * (2 * x / p ^ 2 + 1) := Nat.mul_le_mul (le_refl _) hA
    _ = 2 * (p * (2 * x / p ^ 2)) + (2 * x / p ^ 2) + (2 * p + 1) := by ring
    _ ≤ 2 * (2 * x / p) + (2 * x / p) + (2 * p + 1) :=
        add_le_add (add_le_add (Nat.mul_le_mul (le_refl _) hmul) hA2)
          (le_refl _)
    _ = 3 * (2 * x / p) + (2 * p + 1) := by ring

/-- **Headline bound**: `smoothArcCoveredCount x = O(x·log x)`, explicitly

`smoothArcCoveredCount x ≤ 6x·(log₂ √(2x) + 1) + (√(2x)+1)·(2√(2x)+1)`.

Proof: `prime_smooth_term_le` bounds each summand of
`smoothArcCoveredCount_le_prime_smooth_sum` by `3·(2x/p) + (2p+1)`; the
`∑ (2x)/p` part is handled by the dyadic `sum_primesLE_div_le` and the
`∑ (2p+1)` part by `p ≤ √(2x)` and `π(√(2x)) ≤ √(2x) + 1`. -/
theorem smoothArcCoveredCount_le_log_bound (x : ℕ) :
    smoothArcCoveredCount x ≤
      3 * (2 * x) * (Nat.log 2 (Nat.sqrt (2 * x)) + 1) +
        (Nat.sqrt (2 * x) + 1) * (2 * Nat.sqrt (2 * x) + 1) := by
  refine (smoothArcCoveredCount_le_prime_smooth_sum x).trans ?_
  calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * p + 1) * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card
      ≤ ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
          (3 * (2 * x / p) + (2 * p + 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact prime_smooth_term_le (Nat.prime_of_mem_primesLE hp)
    _ = 3 * (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), 2 * x / p) +
          ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (2 * p + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 3 * (2 * x * (Nat.log 2 (Nat.sqrt (2 * x)) + 1)) +
          (Nat.sqrt (2 * x) + 1) * (2 * Nat.sqrt (2 * x) + 1) := by
        apply add_le_add
        · exact Nat.mul_le_mul (le_refl _)
            (sum_primesLE_div_le _ _)
        · calc ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)), (2 * p + 1)
              ≤ ∑ _p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
                  (2 * Nat.sqrt (2 * x) + 1) := by
                apply Finset.sum_le_sum
                intro p hp
                have := Nat.le_of_mem_primesLE hp
                omega
            _ = (Nat.primesLE (Nat.sqrt (2 * x))).card *
                  (2 * Nat.sqrt (2 * x) + 1) :=
                Finset.sum_const_nat (fun _ _ => rfl)
            _ ≤ (Nat.sqrt (2 * x) + 1) * (2 * Nat.sqrt (2 * x) + 1) :=
                Nat.mul_le_mul (primesLE_card_le _) (le_refl _)
    _ = 3 * (2 * x) * (Nat.log 2 (Nat.sqrt (2 * x)) + 1) +
          (Nat.sqrt (2 * x) + 1) * (2 * Nat.sqrt (2 * x) + 1) := by ring

end LogBound

end JSP314
