import JSP314.FreshEye
import Mathlib.Tactic

/-!
# JSP-000314 — fresh-eye audit, round 2: why the `ε > 1` shortcut fails and a
new "per-arc windowed" reduction

## Audit result (A): the `ε > 1` trivial-bound shortcut is *blocked*

For `ε > 1` the residual asks `N(x) ≤ (log x)^{ε−1}·S(x)`.  The proposed
chain `N ≤ x + 1 ≤ (log x)^{ε−1}·S` via `S ≥ x·exp(−10·√(L·L₂))`
(`SingletonLBz.badSingletonCount_eventually_ge_zscale`) **cannot work**: it
would require `e^{10·s}·(1 + 1/x) ≤ L^{ε−1}` with `s = √(L·L₂)`, but

  `e^{−10·s}·L^{ε−1} → 0`    (`SqueezeZ.tendsto_exp_neg_sqrt_ll_mul_log_pow`)

since `10·s = 10·√L·√L₂` dominates `(ε−1)·L₂ = (ε−1)·log L`.  Formally,
`zscale_lower_envelope_eventually_lt_trivial` shows the *provable lower
envelope* of the RHS is eventually `< x + 1` — the trivial bound overshoots
the target for **every** `ε`, including `ε > 1`.  Moreover, for the same
reason no bound `N ≤ x·(log x)^{−A}` (any fixed `A`) suffices: the target
`x·e^{−10·s}·L^{ε−1}` decays *faster* than `x·L^{−A}`.  Only a genuine
sub-polynomial saving `N ≤ x·e^{−c·s}·(log x)^{O(1)}` (with `c > 10`, i.e.
stronger than the true growth `N ≈ x·e^{−√2·s}` would allow — so the
`SqueezeZ`/`BandSum` `hN`-shaped hypotheses are in fact **stronger than the
theorem**), or a direct ratio bound `N ≤ S·(log x)^{−1+o(1)}`
(`FreshEye`/`Assembly`/`RatioGlue` transporters), can close the residual.

## Audit result (B): a new pointwise reduction — the windowed-`k=1` bound

The run decomposition `RunDecomp.inShortBadInterval_runCovered` assigns to
every covered `n` a `p²`-witness `m` at distance `k ∈ [1, 2p]` on a `p`-smooth
run.  Since `rightRunWitness`/`leftRunWitness` are **antitone in `k`**
(`rightRunWitness_anti`, `leftRunWitness_anti` — new), every level-`k` witness
is already a level-`1` witness: a `p²`-multiple `m ≤ 2x` with
`largestPrimeFactor m = p` and a `p`-smooth *neighbour* `m ± 1`.  Hence each
covered `n` lies in the window `Icc (m − 2p) (m + 2p)` of `4p + 1` points
around a level-`1` witness:

  `shortBadCount x ≤ Σ_{p ≤ √(2x)} (4p+1)·(rightRunCount x p 1 + leftRunCount x p 1)`

(`shortBadCount_le_windowed_runCount`), whence

  `N(x) ≤ Σ_p (4p+1)·(R₁ + L₁) + (2·10^16+1)`
        `≤ Σ_p (4p+1)·(R' + L') + (2·10^16+1)`

with `R'`, `L'` the elementary counts `#{r ≤ 2x/p² : p²r + 1 p-smooth}` and
`#{r ≤ 2x/p² : p²r − 1 p-smooth}` (`rightNeighbourSmoothCount`,
`leftNeighbourSmoothCount`, `badNonSingletonCount_le_neighbourSmooth_sum`) —
the `(4p+2)`-per-`p²`-multiple shape suggested for this round, and further
`≤ Σ_p (4p+1)·2·Ψ(2x/p², p+1) + C₀`
(`badNonSingletonCount_le_smooth_windowed_sum`) via the fiber bound
`ArcCount.badSingletonsBelow_fiber_card_le`.

The same antitonicity collapses the whole run-sum `Σ_k T_k` to `2p·T₁`
(`runCountSum_le_diagonal`).  These bounds are *sharp in shape*: `FreshEye`
showed the `k = 1` witnesses themselves are genuinely covered points
(`sum_rightRunCount_one_le_shortBadCount`), so no purely structural
improvement of this form can beat the truth — the missing input remains a
quantitative count of consecutive `p`-smooth pairs (a Pell-type /
Størmer-type estimate), which is the analytic core of Ta26c.
-/

namespace JSP314

open Filter Classical

section TrivialBoundBlocked

/-- The trivial bound: `N(x) ≤ x + 1` (subset of `range (x+1)`). -/
theorem badNonSingletonCount_le_add_one (x : ℕ) :
    badNonSingletonCount x ≤ x + 1 := by
  unfold badNonSingletonCount
  exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))

/-- **The `ε > 1` trivial-bound route is impossible.**  The best proved lower
bound for the RHS `(log x)^{-(1-ε)}·S(x)` is
`(log x)^{ε−1}·x·exp(−10·√(L·L₂))`, and this envelope is `o(x)` — eventually
strictly *below* `x + 1`, for **every** `ε : ℝ`.  Hence the chain
`N ≤ x + 1 ≤ (log x)^{ε−1}·S(x)` has no working link even for `ε > 1`:
`exp(−10·s)·L^{ε−1} → 0` because `10·√(L·L₂)` dominates `(ε−1)·log L`. -/
theorem zscale_lower_envelope_eventually_lt_trivial (ε : ℝ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-10 * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε - 1) <
        (x : ℝ) + 1 := by
  have ht := (tendsto_exp_neg_sqrt_ll_mul_log_pow 10 (ε - 1)
      (by norm_num)).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [ht, eventually_gt_atTop 0] with x hx hx0
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  have hlt : Real.exp (-10 * Real.sqrt (Real.log (x : ℝ) *
      Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε - 1) < 1 / 2 :=
    Set.mem_Iio.mp hx
  calc (x : ℝ) * Real.exp (-10 * Real.sqrt (Real.log (x : ℝ) *
          Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε - 1)
      = (x : ℝ) * (Real.exp (-10 * Real.sqrt (Real.log (x : ℝ) *
            Real.log (Real.log (x : ℝ)))) * (Real.log x) ^ (ε - 1)) := by ring
    _ < (x : ℝ) * (1 / 2) := mul_lt_mul_of_pos_left hlt hxr
    _ < (x : ℝ) + 1 := by linarith

end TrivialBoundBlocked

section RunMonotonicity

/-- **Run witnesses are antitone in the run length**: if `m + 1, …, m + l`
are all `p`-smooth then so are `m + 1, …, m + k` for `k ≤ l`. -/
theorem rightRunWitness_anti {x p k l : ℕ} (hkl : k ≤ l) :
    rightRunWitness x p l ⊆ rightRunWitness x p k := by
  intro m hm
  rw [mem_rightRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsm⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, fun j hj => hsm j ?_⟩
  rw [Finset.mem_Icc] at hj ⊢
  omega

/-- The left analogue of `rightRunWitness_anti`. -/
theorem leftRunWitness_anti {x p k l : ℕ} (hkl : k ≤ l) :
    leftRunWitness x p l ⊆ leftRunWitness x p k := by
  intro m hm
  rw [mem_leftRunWitness] at hm ⊢
  obtain ⟨hm2x, hdvd, hlpf, hsm⟩ := hm
  refine ⟨hm2x, hdvd, hlpf, fun j hj => hsm j ?_⟩
  rw [Finset.mem_Icc] at hj ⊢
  omega

theorem rightRunCount_anti {x p k l : ℕ} (hkl : k ≤ l) :
    rightRunCount x p l ≤ rightRunCount x p k :=
  Finset.card_le_card (rightRunWitness_anti hkl)

theorem leftRunCount_anti {x p k l : ℕ} (hkl : k ≤ l) :
    leftRunCount x p l ≤ leftRunCount x p k :=
  Finset.card_le_card (leftRunWitness_anti hkl)

/-- **The `k`-sum collapses to the diagonal**: `Σ_{k=1}^{2p} T_k ≤ 2p·T₁`,
since `T_k ≤ T_1` by antitonicity. -/
theorem sum_Icc_rightRunCount_le (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k ≤
      (2 * p) * rightRunCount x p 1 := by
  calc ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k
      ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), rightRunCount x p 1 :=
        Finset.sum_le_sum fun k hk =>
          rightRunCount_anti (Finset.mem_Icc.mp hk).1
    _ = (Finset.Icc 1 (2 * p)).card * rightRunCount x p 1 :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = (2 * p) * rightRunCount x p 1 := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]

theorem sum_Icc_leftRunCount_le (x p : ℕ) :
    ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k ≤
      (2 * p) * leftRunCount x p 1 := by
  calc ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k
      ≤ ∑ _k ∈ Finset.Icc 1 (2 * p), leftRunCount x p 1 :=
        Finset.sum_le_sum fun k hk =>
          leftRunCount_anti (Finset.mem_Icc.mp hk).1
    _ = (Finset.Icc 1 (2 * p)).card * leftRunCount x p 1 :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = (2 * p) * leftRunCount x p 1 := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- **Diagonal collapse of the run sum**: all run-length information is
discarded by
`runCountSum x ≤ Σ_{p ≤ √(2x)} 2p·(rightRunCount x p 1 + leftRunCount x p 1)`. -/
theorem runCountSum_le_diagonal (x : ℕ) :
    runCountSum x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (2 * p) * (rightRunCount x p 1 + leftRunCount x p 1) := by
  unfold runCountSum
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.sum_add_distrib]
  calc ∑ k ∈ Finset.Icc 1 (2 * p), rightRunCount x p k +
        ∑ k ∈ Finset.Icc 1 (2 * p), leftRunCount x p k
      ≤ 2 * p * rightRunCount x p 1 + 2 * p * leftRunCount x p 1 :=
        add_le_add (sum_Icc_rightRunCount_le x p)
          (sum_Icc_leftRunCount_le x p)
    _ = 2 * p * (rightRunCount x p 1 + leftRunCount x p 1) := by ring

end RunMonotonicity

section WindowedWitness

/-- **Windowed cover**: every `n ≤ x` covered by a short bad interval lies in
`Icc (m − 2p) (m + 2p)` around a *level-`1`* run witness `m` (a `p²`-multiple
`≤ 2x` with `largestPrimeFactor m = p` and a `p`-smooth neighbour `m ± 1`),
for some prime `p ≤ √(2x)`.  The level-`k` witness supplied by
`inShortBadInterval_runCovered` is a level-`1` witness by antitonicity. -/
theorem inShortBadInterval_mem_window {x n : ℕ} (hx : n ≤ x)
    (h : InShortBadInterval n) :
    ∃ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
      ∃ m ∈ rightRunWitness x p 1 ∪ leftRunWitness x p 1,
        n ∈ Finset.Icc (m - 2 * p) (m + 2 * p) := by
  obtain ⟨p, k, hp, hk, hcov⟩ := inShortBadInterval_runCovered hx h
  rw [Finset.mem_Icc] at hk
  refine ⟨p, hp, ?_⟩
  rcases hcov with ⟨m, hm, hnm⟩ | ⟨m, hm, hnm⟩ | hnmem
  · exact ⟨m, Finset.mem_union_left _ (rightRunWitness_anti hk.1 hm), by
      rw [Finset.mem_Icc]; omega⟩
  · exact ⟨m, Finset.mem_union_right _ (leftRunWitness_anti hk.1 hm), by
      rw [Finset.mem_Icc]; omega⟩
  · rw [Finset.mem_union] at hnmem
    rcases hnmem with h | h
    · exact ⟨n, Finset.mem_union_left _ (rightRunWitness_anti hk.1 h), by
        rw [Finset.mem_Icc]; omega⟩
    · exact ⟨n, Finset.mem_union_right _ (leftRunWitness_anti hk.1 h), by
        rw [Finset.mem_Icc]; omega⟩

/-- **Per-arc windowed bound**: the short bad-interval count is at most the
sum over primes `p ≤ √(2x)` of `4p + 1` (the window size
`|Icc (m−2p) (m+2p)|`) times the number of level-`1` run witnesses:
`T_short(x) ≤ Σ_p (4p+1)·|R₁ ∪ L₁|`. -/
theorem shortBadCount_le_windowed_witness_sum (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) *
          (rightRunWitness x p 1 ∪ leftRunWitness x p 1).card := by
  have hsub : (Finset.range (x + 1)).filter (fun n => InShortBadInterval n) ⊆
      (Nat.primesLE (Nat.sqrt (2 * x))).biUnion fun p =>
        (rightRunWitness x p 1 ∪ leftRunWitness x p 1).biUnion
          fun m => Finset.Icc (m - 2 * p) (m + 2 * p) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨p, hp, m, hm, hnI⟩ := inShortBadInterval_mem_window
      (Nat.lt_add_one_iff.mp hn.1) hn.2
    rw [Finset.mem_biUnion]
    exact ⟨p, hp, Finset.mem_biUnion.mpr ⟨m, hm, hnI⟩⟩
  unfold shortBadCount
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  apply Finset.sum_le_sum
  intro p _
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ m ∈ rightRunWitness x p 1 ∪ leftRunWitness x p 1,
        (Finset.Icc (m - 2 * p) (m + 2 * p)).card
      ≤ ∑ _m ∈ rightRunWitness x p 1 ∪ leftRunWitness x p 1, (4 * p + 1) := by
        apply Finset.sum_le_sum
        intro m _
        rw [Nat.card_Icc]
        omega
    _ = (rightRunWitness x p 1 ∪ leftRunWitness x p 1).card * (4 * p + 1) :=
        Finset.sum_const_nat fun _ _ => rfl
    _ = (4 * p + 1) *
          (rightRunWitness x p 1 ∪ leftRunWitness x p 1).card :=
        Nat.mul_comm _ _

/-- The same bound with the union count split:
`T_short(x) ≤ Σ_p (4p+1)·(rightRunCount x p 1 + leftRunCount x p 1)`. -/
theorem shortBadCount_le_windowed_runCount (x : ℕ) :
    shortBadCount x ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) * (rightRunCount x p 1 + leftRunCount x p 1) := by
  refine (shortBadCount_le_windowed_witness_sum x).trans ?_
  apply Finset.sum_le_sum
  intro p _
  exact Nat.mul_le_mul le_rfl (Finset.card_union_le _ _)

/-- **The new pointwise reduction of the residual**: the non-singleton bad
count is bounded by `4p + 1` points per level-`1` run witness, plus the
Sylvester–Schur constant:
`N(x) ≤ Σ_{p ≤ √(2x)} (4p+1)·(R₁ + L₁) + (2·10^16+1)`. -/
theorem badNonSingletonCount_le_windowed_runCount (x : ℕ) :
    badNonSingletonCount x ≤
      (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) * (rightRunCount x p 1 + leftRunCount x p 1)) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_short_add_const x
  have h2 := shortBadCount_le_windowed_runCount x
  omega

end WindowedWitness

section ElementaryForm

/-- **Right-neighbour-smooth `p²`-multiples**: `#{r ≤ 2x/p² : p²·r + 1 is
`p`-smooth}` — a purely elementary smooth-counting object. -/
noncomputable def rightNeighbourSmoothCount (x p : ℕ) : ℕ :=
  ((Finset.range (2 * x / p ^ 2 + 1)).filter
    (fun r => largestPrimeFactor (p ^ 2 * r + 1) ≤ p)).card

/-- Left analogue: `#{r ≤ 2x/p² : p²·r − 1 is `p`-smooth}`. -/
noncomputable def leftNeighbourSmoothCount (x p : ℕ) : ℕ :=
  ((Finset.range (2 * x / p ^ 2 + 1)).filter
    (fun r => largestPrimeFactor (p ^ 2 * r - 1) ≤ p)).card

/-- Every level-`1` right run witness `m` maps injectively to `r = m / p²`
with `p²·r + 1 = m + 1` `p`-smooth. -/
theorem rightRunCount_one_le_rightNeighbourSmoothCount (x p : ℕ) :
    rightRunCount x p 1 ≤ rightNeighbourSmoothCount x p := by
  unfold rightNeighbourSmoothCount
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Nat.lt_add_one_iff]
    refine ⟨Nat.div_le_div_right hm2x, ?_⟩
    rw [Nat.mul_div_cancel' hdvd]
    exact hsm (m + 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hb.2.1

/-- The left analogue via `r = m / p²`, `p²·r − 1 = m − 1`. -/
theorem leftRunCount_one_le_leftNeighbourSmoothCount (x p : ℕ) :
    leftRunCount x p 1 ≤ leftNeighbourSmoothCount x p := by
  unfold leftNeighbourSmoothCount
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hdvd, -, hsm⟩ := hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range,
      Nat.lt_add_one_iff]
    refine ⟨Nat.div_le_div_right hm2x, ?_⟩
    rw [Nat.mul_div_cancel' hdvd]
    exact hsm (m - 1) (Finset.mem_Icc.mpr ⟨le_refl _, le_refl _⟩)
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha.2.1).symm
      _ = p ^ 2 * (b / p ^ 2) := by rw [hab]
      _ = b := Nat.mul_div_cancel' hb.2.1

/-- **Elementary per-arc form of the reduction** (the suggested
`#{r ≤ 2x/p² : p²r+1 p-smooth}·(4p+2)`-type bound, with the sharper `4p+1`):
`N(x) ≤ Σ_{p ≤ √(2x)} (4p+1)·(R' + L') + (2·10^16+1)`, where `R'`, `L'` count
`p²`-multiples `≤ 2x` with a `p`-smooth neighbour. -/
theorem badNonSingletonCount_le_neighbourSmooth_sum (x : ℕ) :
    badNonSingletonCount x ≤
      (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) *
          (rightNeighbourSmoothCount x p + leftNeighbourSmoothCount x p)) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_windowed_runCount x
  have h2 : (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) * (rightRunCount x p 1 + leftRunCount x p 1)) ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) *
          (rightNeighbourSmoothCount x p + leftNeighbourSmoothCount x p) := by
    apply Finset.sum_le_sum
    intro p _
    exact Nat.mul_le_mul le_rfl
      (add_le_add (rightRunCount_one_le_rightNeighbourSmoothCount x p)
        (leftRunCount_one_le_leftNeighbourSmoothCount x p))
  omega

end ElementaryForm

section SmoothKernelForm

/-- A level-`1` right run witness is a bad singleton in the `lpf = p` fiber of
`badSingletonsBelow (2x)` (primality of `p` gives `m ≥ 2`). -/
theorem rightRunWitness_one_subset_fiber {x p : ℕ} (hp : Nat.Prime p) :
    rightRunWitness x p 1 ⊆
      (badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p) := by
  intro m hm
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, -⟩ := hm
  rw [Finset.mem_filter, mem_badSingletonsBelow]
  have hm1 : 1 < m := by
    by_contra hc
    push Not at hc
    rw [largestPrimeFactor_eq_one_iff.mpr (by omega : m ≤ 1)] at hlpf
    exact hp.ne_one hlpf.symm
  refine ⟨⟨hm2x, hm1, ?_⟩, hlpf⟩
  rw [hlpf]
  exact hdvd

/-- The left analogue of `rightRunWitness_one_subset_fiber`. -/
theorem leftRunWitness_one_subset_fiber {x p : ℕ} (hp : Nat.Prime p) :
    leftRunWitness x p 1 ⊆
      (badSingletonsBelow (2 * x)).filter
        (fun m => largestPrimeFactor m = p) := by
  intro m hm
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, -⟩ := hm
  rw [Finset.mem_filter, mem_badSingletonsBelow]
  have hm1 : 1 < m := by
    by_contra hc
    push Not at hc
    rw [largestPrimeFactor_eq_one_iff.mpr (by omega : m ≤ 1)] at hlpf
    exact hp.ne_one hlpf.symm
  refine ⟨⟨hm2x, hm1, ?_⟩, hlpf⟩
  rw [hlpf]
  exact hdvd

theorem rightRunCount_one_le_smoothNumbersUpTo (x p : ℕ) (hp : Nat.Prime p) :
    rightRunCount x p 1 ≤
      (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
  (Finset.card_le_card (rightRunWitness_one_subset_fiber hp)).trans
    badSingletonsBelow_fiber_card_le

theorem leftRunCount_one_le_smoothNumbersUpTo (x p : ℕ) (hp : Nat.Prime p) :
    leftRunCount x p 1 ≤
      (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card :=
  (Finset.card_le_card (leftRunWitness_one_subset_fiber hp)).trans
    badSingletonsBelow_fiber_card_le

/-- **Pure smooth-kernel form**: the residual count is bounded by a weighted
sum of Mathlib smooth-number counts:
`N(x) ≤ Σ_{p ≤ √(2x)} (4p+1)·2·Ψ(2x/p², p+1) + (2·10^16+1)`.
This is unconditional and fully explicit; inserting any upper bound on
`Nat.smoothNumbersUpTo` yields a bound on `N`. -/
theorem badNonSingletonCount_le_smooth_windowed_sum (x : ℕ) :
    badNonSingletonCount x ≤
      (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) *
          (2 * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card)) +
        (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_windowed_runCount x
  have h2 : (∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) * (rightRunCount x p 1 + leftRunCount x p 1)) ≤
      ∑ p ∈ Nat.primesLE (Nat.sqrt (2 * x)),
        (4 * p + 1) *
          (2 * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card) := by
    apply Finset.sum_le_sum
    intro p hp
    have hpp := Nat.prime_of_mem_primesLE hp
    calc (4 * p + 1) * (rightRunCount x p 1 + leftRunCount x p 1)
        ≤ (4 * p + 1) *
            ((Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card +
              (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card) :=
          Nat.mul_le_mul le_rfl
            (add_le_add (rightRunCount_one_le_smoothNumbersUpTo x p hpp)
              (leftRunCount_one_le_smoothNumbersUpTo x p hpp))
      _ = (4 * p + 1) *
            (2 * (Nat.smoothNumbersUpTo (2 * x / p ^ 2) (p + 1)).card) := by
          rw [two_mul]
  omega

end SmoothKernelForm

end JSP314
