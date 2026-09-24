import JSP314.ShortLong
import Mathlib.Tactic

/-!
# PsiWindow — elementary window/doubling bounds for smooth-number counts

These lemmas support the singleton-stability and band-sum estimates of the
Ta26c formalization.  Everything is elementary; no sorries.

## Import note

`JSP314.AntiSieve` (which defines `smoothFinset`/`smoothCount` and proves
`largestPrimeFactor_le_of_dvd` and `smoothCount_mono`) is currently **broken
upstream** — it fails to compile at lines 869+ (`Icc_eq_empty`, several
`omega`/`rw` failures, `Unknown identifier q₁`).  Since this file must compile
standalone, the handful of needed declarations are reproduced here *verbatim*
(same names, same statements, same proofs) from `AntiSieve.lean`:

* `smoothFinset`, `smoothCount`, `smoothCount_mono` (AntiSieve.lean:91–195)
* `largestPrimeFactor_le_of_dvd` (AntiSieve.lean:145–154)

Once `AntiSieve.lean` is repaired, this file can switch to
`import JSP314.AntiSieve` and the copies below can be deleted.

## Main results

* `exists_smooth_dvd_in_window` — the **peeling lemma**: every `y`-smooth
  `m ∈ (N, 2N]` has a `y`-smooth divisor `d` in the window `N/y < d ≤ N`
  whose cofactor `r = m/d` satisfies `r ≤ 2y`.
* `smoothCount_two_mul_le` — the **doubling bound**
  `Ψ(2N, y) ≤ (2y + 1)·Ψ(N, y)` for `y ≥ 1`.
* `smoothCount_two_mul_le'` — the corollary `Ψ(2N, y) ≤ 3y·Ψ(N, y)`.
* `smoothCount_mono_right` — monotonicity in the smoothness parameter.
-/

namespace JSP314

open Finset

/-! ### Local copies from `AntiSieve.lean` (see import note above) -/

/-- **Ψ-type finset**: `s ∈ [1, N]` with `largestPrimeFactor s ≤ y`.
(Identical to `AntiSieve.smoothFinset`.) -/
def smoothFinset (N y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun s => largestPrimeFactor s ≤ y

/-- `smoothCount N y = Ψ(N, y)`: the number of `y`-smooth integers in `[1, N]`.
(Identical to `AntiSieve.smoothCount`.) -/
noncomputable def smoothCount (N y : ℕ) : ℕ := (smoothFinset N y).card

/-- Monotonicity of `largestPrimeFactor` under divisibility.
(Identical to `AntiSieve.largestPrimeFactor_le_of_dvd`.) -/
theorem largestPrimeFactor_le_of_dvd {m s : ℕ} (h : m ∣ s) (hs : 2 ≤ s) :
    largestPrimeFactor m ≤ largestPrimeFactor s := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · rw [largestPrimeFactor_eq_one_iff.mpr (by omega : m ≤ 1)]
    exact (one_lt_largestPrimeFactor hs).le
  · rw [largestPrimeFactor_eq_maxPrimeFac hm,
        largestPrimeFactor_eq_maxPrimeFac hs,
        Nat.maxPrimeFac_le_iff (by omega : 1 < m)]
    intro r hrp hrd
    exact Nat.le_maxPrimeFac (by omega : s ≠ 0) hrp (hrd.trans h)

/-- Monotonicity of `smoothCount` in the ambient bound.
(Identical to `AntiSieve.smoothCount_mono`.) -/
theorem smoothCount_mono {N₁ N₂ y : ℕ} (h : N₁ ≤ N₂) :
    smoothCount N₁ y ≤ smoothCount N₂ y := by
  apply Finset.card_le_card
  intro s hs
  simp only [smoothFinset, Finset.mem_filter] at hs ⊢
  obtain ⟨hsI, hlp⟩ := hs
  obtain ⟨hs1, hsN⟩ := Finset.mem_Icc.mp hsI
  exact ⟨Finset.mem_Icc.mpr ⟨hs1, hsN.trans h⟩, hlp⟩

/-! ### The peeling lemma -/

/-- **Peeling lemma.**  Every `y`-smooth `m` in `(N, 2N]` has a `y`-smooth
divisor `d` in the window `N / y < d ≤ N`, with cofactor `r = m / d ≤ 2y`.

Proof: let `d` be the *largest* divisor of `m` not exceeding `N` (the set is
nonempty since `1 ∣ m` and `1 ≤ N`).  Then `m / d ≥ 2`, so
`p = largestPrimeFactor (m/d)` is a prime `≤ y` dividing `m`.  If `d * p ≤ N`
then `d * p` would be a divisor of `m` in `[1, N]` strictly larger than `d`,
contradicting maximality.  Hence `N < d * p ≤ d * y`, which gives
`N / y < d`, and `m = d * r ≤ 2N < 2 * (d * y)` gives `r < 2y`. -/
theorem exists_smooth_dvd_in_window {N y m : ℕ} (hm : N < m) (hm2 : m ≤ 2 * N)
    (hy : 1 ≤ y) (hsm : largestPrimeFactor m ≤ y) :
    ∃ d r : ℕ, d ∣ m ∧ m = d * r ∧ N / y < d ∧ d ≤ N ∧
      largestPrimeFactor d ≤ y ∧ r ≤ 2 * y := by
  have hN : 1 ≤ N := by omega
  have hm2' : 2 ≤ m := by omega
  have hmpos : 0 < m := by omega
  classical
  -- `S` = divisors of `m` in `[1, N]`; nonempty since `1 ∈ S`.
  set S := (Finset.Icc 1 N).filter (· ∣ m) with hS
  have hSne : S.Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩, one_dvd m⟩⟩
  -- `d` = largest element of `S`.
  set d := S.max' hSne with hd_def
  have hdS : d ∈ S := S.max'_mem hSne
  rw [hS, Finset.mem_filter] at hdS
  obtain ⟨hdI, hddvd⟩ := hdS
  obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hdI
  -- `r` = cofactor `m / d`, which is `≥ 2` since `d ≤ N < m`.
  set r := m / d with hr_def
  have hm_eq : m = d * r := (Nat.mul_div_cancel' hddvd).symm
  have hr2 : 2 ≤ r := by
    have hr1 : 1 ≤ r := Nat.div_pos (Nat.le_of_dvd hmpos hddvd) hd1
    rcases eq_or_lt_of_le hr1 with h1 | h1
    · exfalso
      rw [← h1, mul_one] at hm_eq
      omega
    · exact h1
  -- `p` = largest prime factor of `r`; it is a prime `≤ y` dividing `m`.
  set p := largestPrimeFactor r with hp_def
  have hpprime : p.Prime := largestPrimeFactor_prime hr2
  have hpdvd_r : p ∣ r := largestPrimeFactor_dvd hr2
  have hp_le : p ≤ y :=
    (largestPrimeFactor_le_of_dvd (Nat.div_dvd_of_dvd hddvd) hm2').trans hsm
  -- Maximality of `d`: `d * p` cannot be `≤ N`, else it would be a larger
  -- element of `S`.
  have hdpN : N < d * p := by
    by_contra h
    rw [not_lt] at h
    obtain ⟨k, hk⟩ := hpdvd_r
    have hdvd : d * p ∣ m := ⟨k, by rw [hm_eq, hk]; ring⟩
    have hpos : 1 ≤ d * p := by
      have := Nat.mul_le_mul hd1 hpprime.pos
      simpa using this
    have hmem : d * p ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨hpos, h⟩, hdvd⟩
    have hle : d * p ≤ d := Finset.le_max' S _ hmem
    have hgt : d < d * p := by
      have h2 := Nat.mul_le_mul_left d hpprime.two_le
      have hdd : d * 2 = d + d := by ring
      omega
    exact absurd hle (not_le.mpr hgt)
  -- Hence `N < d * p ≤ d * y`, so `N / y < d`.
  have hNdy : N < d * y :=
    hdpN.trans_le (Nat.mul_le_mul (le_refl d) hp_le)
  have hdNy : N / y < d := by
    by_contra hlt
    rw [not_lt] at hlt
    have hle : d * y ≤ N :=
      (Nat.mul_le_mul hlt (le_refl y)).trans (Nat.div_mul_le_self N y)
    omega
  -- And `m = d * r ≤ 2N < 2 * (d * y) = d * (2y)` forces `r < 2y`.
  have hr_le : r ≤ 2 * y := by
    by_contra h
    rw [not_le] at h
    have hge : d * (2 * y) ≤ d * r := Nat.mul_le_mul_left d h.le
    have hlt : 2 * N < d * (2 * y) := by
      have h3 : d * (2 * y) = 2 * (d * y) := by ring
      omega
    have hcontra : d * r < d * r :=
      calc d * r = m := hm_eq.symm
        _ ≤ 2 * N := hm2
        _ < d * (2 * y) := hlt
        _ ≤ d * r := hge
    exact absurd hcontra (lt_irrefl _)
  exact ⟨d, r, hddvd, hm_eq, hdNy, hdN,
    (largestPrimeFactor_le_of_dvd hddvd hm2').trans hsm, hr_le⟩

/-! ### The doubling bound -/

/-- **Window bound.**  `Ψ(2N, y) ≤ (2y + 1) * Ψ(N, y)` for `y ≥ 1`.

Every `y`-smooth `m ≤ 2N` either already lies in `[1, N]` or, by the peeling
lemma, factors as `m = d * r` with `d ∈ smoothFinset N y` and
`r ∈ [1, 2y]`.  Since the pair `(d, r)` determines `m`, the new elements in
`(N, 2N]` are dominated by the image of the product set under multiplication,
whose cardinality is at most `Ψ(N, y) * 2y`. -/
theorem smoothCount_two_mul_le (N y : ℕ) (hy : 1 ≤ y) :
    smoothCount (2 * N) y ≤ (2 * y + 1) * smoothCount N y := by
  classical
  set T := (smoothFinset (2 * N) y).filter (fun m => N < m) with hT
  have hexists : ∀ m ∈ T, ∃ d r : ℕ, d ∣ m ∧ m = d * r ∧ N / y < d ∧
      d ≤ N ∧ largestPrimeFactor d ≤ y ∧ r ≤ 2 * y := by
    intro m hm
    have hm' := hm
    simp only [hT, Finset.mem_filter, smoothFinset, Finset.mem_Icc] at hm'
    obtain ⟨⟨⟨hm1, hm2N⟩, hlpf⟩, hNm⟩ := hm'
    exact exists_smooth_dvd_in_window hNm hm2N hy hlpf
  -- The multiplication map covers `T`: every `m ∈ T` is `d * r` for some
  -- `(d, r)` in the product `smoothFinset N y ×ˢ Icc 1 (2y)`.
  have hsub : T ⊆ ((smoothFinset N y) ×ˢ (Finset.Icc 1 (2 * y))).image
      (fun p : ℕ × ℕ => p.1 * p.2) := by
    intro m hm
    obtain ⟨d, r, hdvd, hm_eq, hdNy, hdN, hlpfd, hr⟩ := hexists m hm
    have hmT := hm
    simp only [hT, Finset.mem_filter, smoothFinset, Finset.mem_Icc] at hmT
    have hmpos : 0 < m := by omega
    have hdpos : 1 ≤ d := (Nat.zero_le _).trans_lt hdNy
    have hrpos : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · exfalso
        rw [h0, mul_zero] at hm_eq
        omega
      · exact h0
    rw [Finset.mem_image]
    refine ⟨(d, r), Finset.mem_product.mpr ⟨?_, ?_⟩, hm_eq.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, hdN⟩, hlpfd⟩
    · exact Finset.mem_Icc.mpr ⟨hrpos, hr⟩
  have hTcard : T.card ≤ (smoothFinset N y).card * (2 * y) :=
    calc T.card
        ≤ (((smoothFinset N y) ×ˢ (Finset.Icc 1 (2 * y))).image
            (fun p : ℕ × ℕ => p.1 * p.2)).card := Finset.card_le_card hsub
      _ ≤ ((smoothFinset N y) ×ˢ (Finset.Icc 1 (2 * y))).card :=
          Finset.card_image_le
      _ = (smoothFinset N y).card * (2 * y) := by
          rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  -- `smoothFinset (2N) y` splits as `smoothFinset N y ∪ T`, disjointly.
  have hdecomp : smoothFinset (2 * N) y = smoothFinset N y ∪ T := by
    ext m
    simp only [hT, smoothFinset, Finset.mem_filter, Finset.mem_union,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hl⟩
      rcases Nat.lt_or_ge N m with h | h
      · exact Or.inr ⟨⟨⟨h1, h2⟩, hl⟩, h⟩
      · exact Or.inl ⟨⟨h1, h⟩, hl⟩
    · rintro (⟨⟨h1, h2⟩, hl⟩ | ⟨⟨⟨h1, h2⟩, hl⟩, h3⟩)
      · exact ⟨⟨h1, h2.trans (by omega)⟩, hl⟩
      · exact ⟨⟨h1, h2⟩, hl⟩
  have hdisj : Disjoint (smoothFinset N y) T := by
    rw [Finset.disjoint_left]
    intro m hm hmT
    simp only [smoothFinset, Finset.mem_filter, Finset.mem_Icc] at hm
    simp only [hT, Finset.mem_filter, smoothFinset, Finset.mem_Icc] at hmT
    omega
  have hcard : (smoothFinset (2 * N) y).card =
      (smoothFinset N y).card + T.card := by
    rw [hdecomp]
    exact Finset.card_union_of_disjoint hdisj
  calc smoothCount (2 * N) y = (smoothFinset (2 * N) y).card := rfl
    _ = (smoothFinset N y).card + T.card := hcard
    _ ≤ (smoothFinset N y).card + (smoothFinset N y).card * (2 * y) := by
        omega
    _ = (2 * y + 1) * (smoothFinset N y).card := by ring

/-- **Doubling bound, cleaner constant:** for `y ≥ 1`,
`Ψ(2N, y) ≤ 3y · Ψ(N, y)` (since `2y + 1 ≤ 3y`). -/
theorem smoothCount_two_mul_le' (N y : ℕ) (hy : 1 ≤ y) :
    smoothCount (2 * N) y ≤ 3 * y * smoothCount N y :=
  (smoothCount_two_mul_le N y hy).trans
    (Nat.mul_le_mul (by omega : 2 * y + 1 ≤ 3 * y) (le_refl _))

/-- `smoothCount` is monotone in the smoothness parameter `y`. -/
theorem smoothCount_mono_right {N : ℕ} {y₁ y₂ : ℕ} (h : y₁ ≤ y₂) :
    smoothCount N y₁ ≤ smoothCount N y₂ := by
  apply Finset.card_le_card
  intro s hs
  simp only [smoothFinset, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, hs.2.trans h⟩

end JSP314
