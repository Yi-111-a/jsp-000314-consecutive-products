import JSP314.SmoothLB
import JSP314.SingletonLBz
import Mathlib.Tactic

/-!
# JSP-000314 — elementary lower bounds for smooth-number counts

`smoothCount Y y` counts the `y`-smooth integers in `[1, Y]` (those `m` all of
whose prime factors are `≤ y`).  This file is the lower-bound counterpart of
the Rankin-trick upper bound in `SieveBase`.

## Main results

* `smoothCount_ge_choose`: if `y^u ≤ Y` then
  `smoothCount Y y ≥ C(π(y), u)`, by counting products `∏ T` of `u` distinct
  primes `≤ y`.  Injectivity: `Nat.primeFactors (∏ T) = T`
  (`SingletonLBz.primeFactors_prod_of_prime`).

* `smoothCount_ge_min_mul_choose`: the sharper two-band estimate
  `min (Y / y^u) (y / 2) · C(Δ(y/2), u) ≤ smoothCount Y y`, counting
  `r · ∏ T` with `r ≤ min (Y / y^u) (y / 2)` (every `r ≤ y/2` is automatically
  `y`-smooth and all its prime factors lie below every element of
  `T ⊆ (y/2, y]`).  Injectivity: `T` is recovered as the set of prime factors
  of `r·∏T` that exceed `y/2`.  The cofactor `r` absorbs the loss
  `Y / y^u ∈ [1, y)` coming from `u = ⌊log Y / log y⌋`, so the `u·log u` term
  is *not* doubled.

* `smoothCount_ge_min_mul_div_pow`: real-valued corollary via
  `SingletonLBz.choose_ge_quarter`:
  `min (Y / y^u) (y / 2) · (Δ(y/2) / (2u))^u ≤ smoothCount Y y`.

* `smoothCount_eventually_ge_exp`: for `y` large and all `Y`, with
  `u = ⌊log Y / log y⌋₊`,
  `Y · exp(-u·(log u + log log y) - 7u) ≤ smoothCount Y y`.
  Since `log u ≤ log log y + O(1)` in the regime `u ≍ log Y / log y`, this is
  `Y·exp(-(1+o(1))·u·log u)`, the correct order for `Ψ(Y, y)`.

* `eventually_smoothCount_ge_exp`: the same bound packaged as
  `∀ᶠ p : ℕ × ℕ in Filter.atTop`.
-/

namespace JSP314

namespace PsiLB

open Finset Filter

open scoped Topology

/-- The number of `y`-smooth integers in `[1, Y]`, i.e. those `m ∈ [1, Y]`
all of whose prime factors are `≤ y`. -/
def smoothCount (Y y : ℕ) : ℕ :=
  ((Finset.Icc 1 Y).filter fun m => ∀ p ∈ Nat.primeFactors m, p ≤ y).card

/-- `1` is `y`-smooth, so the count is positive for `Y ≥ 1`. -/
theorem one_le_smoothCount {Y y : ℕ} (hY : 1 ≤ Y) : 1 ≤ smoothCount Y y := by
  apply Finset.card_pos.mpr
  exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hY⟩,
    fun p hp => by simp only [Nat.primeFactors_one, Finset.not_mem_empty] at hp⟩⟩

/-- If `Y ≤ y`, every `m ∈ [1, Y]` is `y`-smooth. -/
theorem smoothCount_eq_self {Y y : ℕ} (h : Y ≤ y) : smoothCount Y y = Y := by
  unfold smoothCount
  rw [show (Finset.Icc 1 Y).filter (fun m => ∀ p ∈ Nat.primeFactors m, p ≤ y)
      = Finset.Icc 1 Y from ?_]
  · rw [Nat.card_Icc]; omega
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun h' => h'.1, fun hm => ⟨hm, fun p hp => ?_⟩⟩
  rw [Nat.mem_primeFactors] at hp
  exact (Nat.le_of_dvd hm.1 hp.2.1).trans (hm.2.trans h)

/-- **Distinct-primes count.** If `y^u ≤ Y` then `smoothCount Y y ≥ C(π(y), u)`:
map a `u`-element set `T` of primes `≤ y` to `∏ T`; the product is `≤ y^u ≤ Y`,
is `y`-smooth, and `T` is recovered as `Nat.primeFactors (∏ T)`. -/
theorem smoothCount_ge_choose {Y y u : ℕ} (hY : 1 ≤ Y) (hu : y ^ u ≤ Y) :
    (Nat.primesLE y).card.choose u ≤ smoothCount Y y := by
  classical
  have hsub : ((Nat.primesLE y).powersetCard u).image (fun T => T.prod id) ⊆
      (Finset.Icc 1 Y).filter (fun m => ∀ p ∈ Nat.primeFactors m, p ≤ y) := by
    rw [Finset.image_subset_iff]
    intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    have hprime : ∀ q ∈ T, q.Prime :=
      fun q hq => Nat.prime_of_mem_primesLE (hTsub hq)
    have hpos : 1 ≤ T.prod id :=
      Finset.one_le_prod fun q hq => (hprime q hq).one_lt.le
    have hle : T.prod id ≤ Y := by
      calc T.prod id ≤ y ^ T.card :=
            Finset.prod_le_pow_card T id y fun q hq =>
              Nat.le_of_mem_primesLE (hTsub hq)
        _ = y ^ u := by rw [hTcard]
        _ ≤ Y := hu
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hpos, hle⟩, fun p hp => ?_⟩
    rw [SingletonLBz.primeFactors_prod_of_prime hprime] at hp
    exact Nat.le_of_mem_primesLE (hTsub hp)
  have hinj : Set.InjOn (fun T : Finset ℕ => T.prod id)
      ((Nat.primesLE y).powersetCard u) := by
    intro T hT U hU h
    have h' : T.prod id = U.prod id := h
    obtain ⟨hTsub, -⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨hUsub, -⟩ := Finset.mem_powersetCard.mp hU
    have eT := SingletonLBz.primeFactors_prod_of_prime
      (fun q hq => Nat.prime_of_mem_primesLE (hTsub hq))
    have eU := SingletonLBz.primeFactors_prod_of_prime
      (fun q hq => Nat.prime_of_mem_primesLE (hUsub hq))
    rw [← eT, ← eU, h']
  calc (Nat.primesLE y).card.choose u
        = (((Nat.primesLE y).powersetCard u).image fun T => T.prod id).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard]
    _ ≤ smoothCount Y y := Finset.card_le_card hsub

/-- **Two-band count.**  Count `r · ∏ T` where `r ∈ [1, w]` with
`w = min (Y / y^u) (y / 2)` and `T` is a `u`-subset of the dyadic primes in
`(y/2, y]`.  Every prime factor of `r` is `≤ w ≤ y/2`, hence below every
element of `T`; the map is injective since `T` is recovered as the prime
factors of the product that exceed `y/2`. -/
theorem smoothCount_ge_min_mul_choose {Y y u : ℕ} (hY : 1 ≤ Y) (hu : y ^ u ≤ Y) :
    min (Y / y ^ u) (y / 2) * ((SmoothLB.dyadicPrimes (y / 2)).card.choose u)
      ≤ smoothCount Y y := by
  classical
  set w := min (Y / y ^ u) (y / 2) with hwdef
  set D := SmoothLB.dyadicPrimes (y / 2) with hDdef
  set S : Finset (ℕ × Finset ℕ) := (Finset.Icc 1 w) ×ˢ D.powersetCard u with hSdef
  set f : ℕ × Finset ℕ → ℕ := fun s => s.1 * s.2.prod id with hfdef
  have hwy : w ≤ y / 2 := min_le_right _ _
  have hwy' : w ≤ y := hwy.trans (Nat.div_le_self _ _)
  have hwY : w * y ^ u ≤ Y :=
    (Nat.mul_le_mul (min_le_left _ _) le_rfl).trans (Nat.div_mul_le_self _ _)
  have hfacts : ∀ r : ℕ, ∀ T : Finset ℕ, (r, T) ∈ S →
      1 ≤ r ∧ r ≤ w ∧ (∀ q ∈ T, q.Prime ∧ y / 2 < q ∧ q ≤ y) ∧ T.card = u := by
    intro r T hm
    rw [hSdef, Finset.mem_product] at hm
    obtain ⟨hr, hT⟩ := hm
    obtain ⟨hr1, hrw⟩ := Finset.mem_Icc.mp hr
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    refine ⟨hr1, hrw, fun q hq => ?_, hTcard⟩
    obtain ⟨hp, hgt, hle⟩ := SmoothLB.mem_dyadicPrimes.mp (hTsub hq)
    exact ⟨hp, hgt, hle.trans (by omega : 2 * (y / 2) ≤ y)⟩
  have hsub : S.image f ⊆ (Finset.Icc 1 Y).filter
      (fun m => ∀ p ∈ Nat.primeFactors m, p ≤ y) := by
    rw [Finset.image_subset_iff]
    rintro ⟨r, T⟩ hm
    obtain ⟨hr1, hrw, hqT, hTcard⟩ := hfacts r T hm
    have hTpos : 1 ≤ T.prod id :=
      Finset.one_le_prod fun q hq => (hqT q hq).1.one_lt.le
    have hTle : T.prod id ≤ y ^ u := by
      calc T.prod id ≤ y ^ T.card :=
            Finset.prod_le_pow_card T id y fun q hq => (hqT q hq).2.2
        _ = y ^ u := by rw [hTcard]
    have hpos : 1 ≤ r * T.prod id := Nat.mul_pos hr1 hTpos
    have hle' : r * T.prod id ≤ Y := (Nat.mul_le_mul hrw hTle).trans hwY
    simp only [hfdef, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨hpos, hle'⟩, fun p hp => ?_⟩
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpprime, hpdvd, -⟩ := hp
    rcases hpprime.dvd_mul.mp hpdvd with hpr | hpT
    · exact (Nat.le_of_dvd hr1 hpr).trans (hrw.trans hwy')
    · obtain ⟨q, hq, hpq⟩ := ((Nat.prime_iff.mp hpprime).dvd_finsetProd_iff id).mp hpT
      rcases (hqT q hq).1.eq_one_or_self_of_dvd p hpq with h1 | h1
      · exact absurd h1 hpprime.ne_one
      · rw [h1]; exact (hqT q hq).2.2
  have hinj : Set.InjOn f S := by
    rintro ⟨r, T⟩ hmT ⟨r', T'⟩ hmT' h
    have h' : r * T.prod id = r' * T'.prod id := h
    obtain ⟨hr1, hrw, hqT, hTcard⟩ := hfacts r T hmT
    obtain ⟨hr1', hrw', hqT', hTcard'⟩ := hfacts r' T' hmT'
    have hTpos : 0 < T.prod id := Finset.prod_pos fun q hq => (hqT q hq).1.pos
    have hT'pos : 0 < T'.prod id := Finset.prod_pos fun q hq => (hqT' q hq).1.pos
    have hpf : Nat.primeFactors (r * T.prod id) = Nat.primeFactors r ∪ T := by
      rw [Nat.primeFactors_mul (by omega : r ≠ 0) hTpos.ne',
        SingletonLBz.primeFactors_prod_of_prime (fun q hq => (hqT q hq).1)]
    have hpf' : Nat.primeFactors (r' * T'.prod id) = Nat.primeFactors r' ∪ T' := by
      rw [Nat.primeFactors_mul (by omega : r' ≠ 0) hT'pos.ne',
        SingletonLBz.primeFactors_prod_of_prime (fun q hq => (hqT' q hq).1)]
    have key : T = (Nat.primeFactors (r * T.prod id)).filter (fun p => y / 2 < p) := by
      rw [hpf]
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, (hqT p hp).2.1⟩
      · rintro ⟨h | h, hlt⟩
        · rw [Nat.mem_primeFactors] at h
          have hpr : p ≤ r := Nat.le_of_dvd hr1 h.2.1
          omega
        · exact h
    have key' : T' = (Nat.primeFactors (r' * T'.prod id)).filter
        (fun p => y / 2 < p) := by
      rw [hpf']
      ext p
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨Or.inr hp, (hqT' p hp).2.1⟩
      · rintro ⟨h | h, hlt⟩
        · rw [Nat.mem_primeFactors] at h
          have hpr : p ≤ r' := Nat.le_of_dvd hr1' h.2.1
          omega
        · exact h
    have hTT : T = T' := by rw [key, key', h']
    subst hTT
    have hrr : r = r' := Nat.mul_right_cancel hTpos h'
    exact Prod.ext_iff.mpr ⟨hrr, rfl⟩
  have hcard : S.card = w * (D.card.choose u) := by
    rw [hSdef, Finset.card_product, Finset.card_powersetCard, Nat.card_Icc,
      show w + 1 - 1 = w from by omega]
  calc w * (D.card.choose u) = S.card := hcard.symm
    _ = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ smoothCount Y y := Finset.card_le_card hsub

/-- **Real-valued corollary.**  With `w = min (Y / y^u) (y / 2)` and
`D' = #(dyadicPrimes (y/2))`, if `2u ≤ D'` then
`w · (D' / (2u))^u ≤ smoothCount Y y`. -/
theorem smoothCount_ge_min_mul_div_pow {Y y u : ℕ} (hY : 1 ≤ Y) (hu : y ^ u ≤ Y)
    (h2u : 2 * u ≤ (SmoothLB.dyadicPrimes (y / 2)).card) :
    (min (Y / y ^ u) (y / 2) : ℝ) *
      (((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) / (2 * u)) ^ u
        ≤ (smoothCount Y y : ℝ) := by
  have h := smoothCount_ge_min_mul_choose hY hu
  have hc := SingletonLBz.choose_ge_quarter
    (D := (SmoothLB.dyadicPrimes (y / 2)).card) (u := u) h2u
  have heq : (((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) / (2 * u)) ^ u
      = (((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) / 2) ^ u / (u : ℝ) ^ u := by
    rw [div_pow, mul_pow, div_pow, div_div]
  calc (min (Y / y ^ u) (y / 2) : ℝ) *
          (((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) / (2 * u)) ^ u
      = (min (Y / y ^ u) (y / 2) : ℝ) *
          ((((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) / 2) ^ u / (u : ℝ) ^ u) := by
        rw [heq]
    _ ≤ (min (Y / y ^ u) (y / 2) : ℝ) *
          (((SmoothLB.dyadicPrimes (y / 2)).card.choose u : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
    _ = ((min (Y / y ^ u) (y / 2) *
          (SmoothLB.dyadicPrimes (y / 2)).card.choose u : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (smoothCount Y y : ℝ) := by exact_mod_cast h

/-- `y ↦ y / 2` tends to `∞`. -/
theorem tendsto_nat_div_two_atTop :
    Filter.Tendsto (fun n : ℕ => n / 2) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun a ha =>
    (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr (by omega)⟩

/-- The dyadic prime count on `(y/2, y]` is `≥ y / (32 log y)` eventually. -/
theorem eventually_dyadicPrimes_half_card_ge : ∀ᶠ y : ℕ in Filter.atTop,
    (y : ℝ) / (32 * Real.log y) ≤ ((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) := by
  have h := tendsto_nat_div_two_atTop.eventually
    SmoothLB.eventually_dyadicPrimes_card_ge
  filter_upwards [h, eventually_ge_atTop 4] with y hy hy4
  set n := y / 2 with hn
  have hn2 : 2 ≤ n := by omega
  have h4n : y ≤ 4 * n := by omega
  have hnry : (y : ℝ) / 4 ≤ (n : ℝ) := by
    have h4 : (y : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast h4n
    linarith
  have hlogn : Real.log (n : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
      (by exact_mod_cast (Nat.div_le_self y 2))
  have hlognpos : (0 : ℝ) < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  calc (y : ℝ) / (32 * Real.log y) = ((y : ℝ) / 4) / (8 * Real.log y) := by
        rw [div_div]; congr 1; ring
    _ ≤ (n : ℝ) / (8 * Real.log n) :=
        div_le_div₀ (by positivity) hnry
          (by positivity : (0 : ℝ) < 8 * Real.log (n : ℝ))
          (by linarith [hlogn])
    _ ≤ _ := hy

/-- `(log y)² ≤ y / 64` eventually (from `log = o(·^{1/2})`). -/
theorem eventually_log_sq_le : ∀ᶠ y : ℕ in Filter.atTop,
    (Real.log (y : ℝ)) ^ 2 ≤ (y : ℝ) / 64 := by
  have h := (Real.isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
    tendsto_natCast_atTop_atTop
  rw [Asymptotics.isLittleO_iff] at h
  have h1 := h (show (0 : ℝ) < (1 / 8 : ℝ) by norm_num)
  filter_upwards [h1, eventually_ge_atTop 3] with y hy hy3
  simp only [Function.comp_apply] at hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega)
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))
  have hsqrt : 0 ≤ (y : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs, abs_of_nonneg hsqrt,
    one_mul] at hy
  have hsq : ((y : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (y : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hy0.le]
  calc (Real.log (y : ℝ)) ^ 2 ≤ ((y : ℝ) ^ (1 / 2 : ℝ) / 8) ^ 2 :=
        pow_le_pow_left₀ hlog (by linarith [hy]) _
    _ = (y : ℝ) / 64 := by rw [div_pow, hsq]; ring

/-- **Asymptotic lower bound.**  For `y` large and every `Y`, with
`u = ⌊log Y / log y⌋₊`,
`Y · exp(-u·(log u + log log y) - 7u) ≤ smoothCount Y y`. -/
set_option maxHeartbeats 800000 in
theorem smoothCount_eventually_ge_exp :
    ∃ B : ℕ, ∀ Y y : ℕ, B ≤ y →
      (Y : ℝ) * Real.exp
          (-(⌊Real.log (Y : ℝ) / Real.log (y : ℝ)⌋₊ : ℝ) *
            (Real.log (⌊Real.log (Y : ℝ) / Real.log (y : ℝ)⌋₊ : ℝ) +
              Real.log (Real.log (y : ℝ))) -
            7 * (⌊Real.log (Y : ℝ) / Real.log (y : ℝ)⌋₊ : ℝ))
        ≤ (smoothCount Y y : ℝ) := by
  obtain ⟨B1, hB1⟩ := eventually_atTop.mp eventually_dyadicPrimes_half_card_ge
  obtain ⟨B2, hB2⟩ := eventually_atTop.mp eventually_log_sq_le
  refine ⟨max (max B1 B2) 4, fun Y y hBy => ?_⟩
  have hB1y := hB1 y ((le_max_left B1 B2).trans ((le_max_left _ 4).trans hBy))
  have hB2y := hB2 y ((le_max_right B1 B2).trans ((le_max_left _ 4).trans hBy))
  have hy4 : 4 ≤ y := (le_max_right _ 4).trans hBy
  set u : ℕ := ⌊Real.log (Y : ℝ) / Real.log (y : ℝ)⌋₊ with hudef
  have hy0 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega)
  have hly : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlog4gt1 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9]
  have hly1 : (1 : ℝ) < Real.log (y : ℝ) := by
    have h := Real.log_le_log (show (0 : ℝ) < 4 by norm_num)
      (show (4 : ℝ) ≤ (y : ℝ) by exact_mod_cast hy4)
    linarith [hlog4gt1, h]
  have hlly : 0 < Real.log (Real.log (y : ℝ)) := Real.log_pos hly1
  have hlog64 : Real.log 64 < (4.2 : ℝ) := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hlog4 : Real.log 4 < (1.4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hlog2 : Real.log 2 < (0.7 : ℝ) := by linarith [Real.log_two_lt_d9]
  rcases le_or_lt Y y with hYy | hYy
  · -- `Y ≤ y`: every `m ≤ Y` is `y`-smooth, and the bound is `≤ Y`.
    rw [smoothCount_eq_self hYy]
    have hlogu : 0 ≤ Real.log (u : ℝ) := by
      rcases Nat.eq_zero_or_pos u with h0 | hpos
      · rw [h0]; simp
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    have hE : -(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
        - 7 * (u : ℝ) ≤ 0 := by
      have h1 : (0 : ℝ) ≤ (u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ))) :=
        mul_nonneg (Nat.cast_nonneg _) (add_nonneg hlogu hlly.le)
      have h2 : (0 : ℝ) ≤ 7 * (u : ℝ) := by positivity
      linarith
    have hexp : Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
        - 7 * (u : ℝ)) ≤ 1 :=
      Real.exp_zero ▸ Real.exp_le_exp.mpr hE
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) hexp
  · -- `y < Y`: `u ≥ 1`, `y^u ≤ Y < y^(u+1)`.
    have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast (by omega)
    have hY1 : 1 ≤ Y := by omega
    have hL : Real.log (y : ℝ) < Real.log (Y : ℝ) :=
      Real.log_lt_log hy0 (by exact_mod_cast hYy)
    have hLnn : 0 ≤ Real.log (Y : ℝ) := hly.le.trans hL.le
    have hLy1 : 1 < Real.log (Y : ℝ) / Real.log (y : ℝ) := (one_lt_div hly).mpr hL
    have huflt : Real.log (Y : ℝ) / Real.log (y : ℝ) < (u : ℝ) + 1 := by
      have h := Nat.lt_floor_add_one (Real.log (Y : ℝ) / Real.log (y : ℝ))
      rwa [← hudef] at h
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | hpos
      · exfalso
        rw [h0] at huflt
        push_cast at huflt
        linarith [hLy1, huflt]
      · exact hpos
    have hurpos : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu1
    have hlogu : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    have huL : (u : ℝ) * Real.log (y : ℝ) ≤ Real.log (Y : ℝ) := by
      have h := Nat.floor_le (div_nonneg hLnn hly.le)
      rw [← hudef] at h
      exact (le_div_iff₀ hly).mp h
    have hLu : Real.log (Y : ℝ) < ((u : ℝ) + 1) * Real.log (y : ℝ) :=
      (div_lt_iff₀ hly).mp huflt
    have hYu : y ^ u ≤ Y := by
      have e : ((y : ℝ) ^ u : ℝ) ≤ (Y : ℝ) := by
        calc (y : ℝ) ^ u = (Real.exp (Real.log (y : ℝ))) ^ u := by
              rw [Real.exp_log hy0]
          _ = Real.exp ((u : ℝ) * Real.log (y : ℝ)) := (Real.exp_nat_mul _ _).symm
          _ ≤ Real.exp (Real.log (Y : ℝ)) := Real.exp_le_exp.mpr huL
          _ = (Y : ℝ) := Real.exp_log hY0
      exact_mod_cast e
    rcases le_or_lt (2 * u) (SmoothLB.dyadicPrimes (y / 2)).card with h2u | h2u
    · -- Case A: `2u ≤ Δ(y/2)`, use the choose bound.
      set D' := ((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) with hD'def
      have hD'pos : (0 : ℝ) < D' := by
        have h1 : (0 : ℝ) < (y : ℝ) / (32 * Real.log (y : ℝ)) :=
          div_pos hy0 (mul_pos (by norm_num) hly)
        rw [hD'def]
        exact h1.trans_le hB1y
      have h2upos : (0 : ℝ) < 2 * (u : ℝ) := mul_pos two_pos hurpos
      have h3 := smoothCount_ge_min_mul_div_pow hY1 hYu h2u
      have hbase : (y : ℝ) / (64 * (u : ℝ) * Real.log (y : ℝ)) ≤ D' / (2 * (u : ℝ)) := by
        have e : (y : ℝ) / (64 * (u : ℝ) * Real.log (y : ℝ))
            = ((y : ℝ) / (32 * Real.log (y : ℝ))) / (2 * (u : ℝ)) := by
          rw [div_div]; congr 1; ring
        rw [e]
        exact (div_le_div_iff_of_pos_right h2upos).mpr hB1y
      have hlogbase : Real.log (y : ℝ) - Real.log 64 - Real.log (u : ℝ)
            - Real.log (Real.log (y : ℝ)) ≤ Real.log (D' / (2 * (u : ℝ))) := by
        have hpos : (0 : ℝ) < (y : ℝ) / (64 * (u : ℝ) * Real.log (y : ℝ)) :=
          div_pos hy0 (mul_pos (mul_pos (by norm_num) hurpos) hly)
        have h1 := Real.log_le_log hpos hbase
        have e : Real.log ((y : ℝ) / (64 * (u : ℝ) * Real.log (y : ℝ)))
            = Real.log (y : ℝ) - Real.log 64 - Real.log (u : ℝ)
              - Real.log (Real.log (y : ℝ)) := by
          rw [Real.log_div hy0.ne' (mul_pos (mul_pos (by norm_num) hurpos) hly).ne',
            Real.log_mul (mul_pos (by norm_num) hurpos).ne' hly.ne',
            Real.log_mul (by norm_num) hurpos.ne']
          ring
        linarith [h1, e]
      have hbpos : (0 : ℝ) < D' / (2 * (u : ℝ)) := div_pos hD'pos h2upos
      have hwpos0 : 1 ≤ min (Y / y ^ u) (y / 2) :=
        le_min (Nat.div_pos hYu (pow_pos (show 0 < y by omega) u)) (by omega)
      have hwpos : (0 : ℝ) < (min (Y / y ^ u) (y / 2) : ℝ) := by exact_mod_cast hwpos0
      have hlogprod : Real.log ((min (Y / y ^ u) (y / 2) : ℝ) * (D' / (2 * (u : ℝ))) ^ u)
          = Real.log (min (Y / y ^ u) (y / 2) : ℝ)
            + (u : ℝ) * Real.log (D' / (2 * (u : ℝ))) := by
        rw [Real.log_mul hwpos.ne' (pow_pos hbpos u).ne', Real.log_pow]
      have hcountpos : (0 : ℝ) < (smoothCount Y y : ℝ) := by
        have h1 := one_le_smoothCount hY1
        exact_mod_cast h1
      have hlogcount : Real.log (min (Y / y ^ u) (y / 2) : ℝ)
          + (u : ℝ) * Real.log (D' / (2 * (u : ℝ))) ≤ Real.log (smoothCount Y y : ℝ) := by
        have e := Real.log_le_log (mul_pos hwpos (pow_pos hbpos u)) h3
        rwa [hlogprod] at e
      have h2 := mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
      have h1' := mul_le_mul_of_nonneg_left hlog64.le (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
      have hur1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
      rcases le_total (Y / y ^ u) (y / 2) with hmin | hmin
      · -- `w = Y / y^u`: `log w ≥ log Y - u·log y - log 2`.
        have hweq : min (Y / y ^ u) (y / 2) = Y / y ^ u := min_eq_left hmin
        have hapos : 0 < y ^ u := pow_pos (show 0 < y by omega) u
        have hmod : Y < (Y / y ^ u + 1) * y ^ u := by
          calc Y = y ^ u * (Y / y ^ u) + Y % y ^ u := (Nat.div_add_mod Y _).symm
            _ < y ^ u * (Y / y ^ u) + y ^ u := add_lt_add_right (Nat.mod_lt _ hapos) _
            _ = (Y / y ^ u + 1) * y ^ u := by ring
        have hdiv : (Y : ℝ) / (y : ℝ) ^ u < ((Y / y ^ u : ℕ) : ℝ) + 1 := by
          rw [div_lt_iff₀ (pow_pos hy0 u : (0 : ℝ) < (y : ℝ) ^ u)]
          have h := hmod
          rw [← Nat.cast_lt] at h
          push_cast at h
          exact h
        have hwge : (Y : ℝ) / (2 * (y : ℝ) ^ u) ≤ ((Y / y ^ u : ℕ) : ℝ) := by
          have ha1 : (1 : ℝ) ≤ ((Y / y ^ u : ℕ) : ℝ) := by
            have h := Nat.div_pos hYu hapos
            exact_mod_cast h
          rcases le_or_lt ((Y : ℝ) / (y : ℝ) ^ u) 2 with ht | ht
          · linarith [hdiv, ha1]
          · linarith [hdiv]
        have hlogw : Real.log (Y : ℝ) - (u : ℝ) * Real.log (y : ℝ) - Real.log 2
            ≤ Real.log ((Y / y ^ u : ℕ) : ℝ) := by
          have e := Real.log_le_log
            (div_pos hY0 (mul_pos two_pos (pow_pos hy0 u)) :
              (0 : ℝ) < (Y : ℝ) / (2 * (y : ℝ) ^ u)) hwge
          have ee : Real.log ((Y : ℝ) / (2 * (y : ℝ) ^ u))
              = Real.log (Y : ℝ) - Real.log 2 - (u : ℝ) * Real.log (y : ℝ) := by
            rw [Real.log_div hY0.ne' (mul_pos two_pos (pow_pos hy0 u)).ne',
              Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hy0 u).ne',
              Real.log_pow]
            ring
          linarith [e, ee]
        have hlogcount2 : Real.log (Y : ℝ)
            - (u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)) + 7)
            ≤ Real.log (smoothCount Y y : ℝ) := by
          rw [hweq] at hlogcount
          linarith [hlogcount, hlogw, h2, h1', hlog2, hur1]
        have hgoal : Real.log (Y : ℝ)
            + (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ))) - 7 * (u : ℝ))
            ≤ Real.log (smoothCount Y y : ℝ) := by linarith [hlogcount2]
        calc (Y : ℝ) * Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
              - 7 * (u : ℝ))
            = Real.exp (Real.log (Y : ℝ)) *
                Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
                  - 7 * (u : ℝ)) := by rw [Real.exp_log hY0]
          _ = Real.exp (Real.log (Y : ℝ)
              + (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
                - 7 * (u : ℝ))) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (Real.log (smoothCount Y y : ℝ)) := Real.exp_le_exp.mpr hgoal
          _ = (smoothCount Y y : ℝ) := Real.exp_log hcountpos
      · -- `w = y / 2`: `log w ≥ log y - log 4`.
        have hweq : min (Y / y ^ u) (y / 2) = y / 2 := min_eq_right hmin
        have hwge : (y : ℝ) / 4 ≤ ((y / 2 : ℕ) : ℝ) := by
          have h4w : y ≤ 4 * (y / 2) := by omega
          have h4w' : (y : ℝ) ≤ 4 * ((y / 2 : ℕ) : ℝ) := by exact_mod_cast h4w
          linarith
        have hlogw : Real.log (y : ℝ) - Real.log 4 ≤ Real.log ((y / 2 : ℕ) : ℝ) := by
          have e := Real.log_le_log (by positivity : (0 : ℝ) < (y : ℝ) / 4) hwge
          have ee : Real.log ((y : ℝ) / 4) = Real.log (y : ℝ) - Real.log 4 :=
            Real.log_div hy0.ne' (by norm_num)
          linarith [e, ee]
        have hlogcount2 : Real.log (Y : ℝ)
            - (u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)) + 7)
            ≤ Real.log (smoothCount Y y : ℝ) := by
          rw [hweq] at hlogcount
          linarith [hlogcount, hlogw, h2, h1', hlog4, hLu, hur1]
        have hgoal : Real.log (Y : ℝ)
            + (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ))) - 7 * (u : ℝ))
            ≤ Real.log (smoothCount Y y : ℝ) := by linarith [hlogcount2]
        calc (Y : ℝ) * Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
              - 7 * (u : ℝ))
            = Real.exp (Real.log (Y : ℝ)) *
                Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
                  - 7 * (u : ℝ)) := by rw [Real.exp_log hY0]
          _ = Real.exp (Real.log (Y : ℝ)
              + (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
                - 7 * (u : ℝ))) := (Real.exp_add _ _).symm
          _ ≤ Real.exp (Real.log (smoothCount Y y : ℝ)) := Real.exp_le_exp.mpr hgoal
          _ = (smoothCount Y y : ℝ) := Real.exp_log hcountpos
    · -- Case B: `Δ(y/2) < 2u`; then `u ≥ y/(64 log y)` and the bound is `≤ 1`.
      have hDlt : ((SmoothLB.dyadicPrimes (y / 2)).card : ℝ) < 2 * (u : ℝ) := by
        exact_mod_cast h2u
      have hug : (y : ℝ) / (64 * Real.log (y : ℝ)) ≤ (u : ℝ) := by
        have h : (y : ℝ) / (32 * Real.log (y : ℝ)) < 2 * (u : ℝ) :=
          lt_of_le_of_lt hB1y hDlt
        rw [div_lt_iff₀ (mul_pos (by norm_num) hly : (0 : ℝ) < 64 * Real.log (y : ℝ))]
        rw [div_lt_iff₀ (mul_pos (by norm_num) hly : (0 : ℝ) < 32 * Real.log (y : ℝ))] at h
        linarith [h]
      have hlogu_ge : Real.log (y : ℝ) - Real.log 64 - Real.log (Real.log (y : ℝ))
          ≤ Real.log (u : ℝ) := by
        have e := Real.log_le_log
          (div_pos hy0 (mul_pos (by norm_num) hly) :
            (0 : ℝ) < (y : ℝ) / (64 * Real.log (y : ℝ))) hug
        have ee : Real.log ((y : ℝ) / (64 * Real.log (y : ℝ)))
            = Real.log (y : ℝ) - Real.log 64 - Real.log (Real.log (y : ℝ)) := by
          rw [Real.log_div hy0.ne' (mul_pos (by norm_num) hly).ne',
            Real.log_mul (by norm_num) hly.ne']
          ring
        linarith [e, ee]
      have hule : Real.log (y : ℝ) ≤ (u : ℝ) * (7 - Real.log 64) := by
        have h2 : Real.log (y : ℝ) ≤ (y : ℝ) / (64 * Real.log (y : ℝ)) := by
          rw [le_div_iff₀ (mul_pos (by norm_num) hly)]
          nlinarith [hB2y]
        calc Real.log (y : ℝ) ≤ (y : ℝ) / (64 * Real.log (y : ℝ)) := h2
          _ ≤ (u : ℝ) := hug
          _ ≤ (u : ℝ) * (7 - Real.log 64) :=
              le_mul_of_one_le_right hurpos.le (by linarith [hlog64])
      have hS : Real.log (Y : ℝ)
          ≤ (u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)) + 7) := by
        have h1 := mul_le_mul_of_nonneg_left hlogu_ge (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
        nlinarith [h1, hule, hLu]
      have hcnt : (1 : ℝ) ≤ (smoothCount Y y : ℝ) := by
        have h1 := one_le_smoothCount hY1
        exact_mod_cast h1
      calc (Y : ℝ) * Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
            - 7 * (u : ℝ))
          = Real.exp (Real.log (Y : ℝ)) *
              Real.exp (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
                - 7 * (u : ℝ)) := by rw [Real.exp_log hY0]
        _ = Real.exp (Real.log (Y : ℝ)
            + (-(u : ℝ) * (Real.log (u : ℝ) + Real.log (Real.log (y : ℝ)))
              - 7 * (u : ℝ))) := (Real.exp_add _ _).symm
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [hS])
        _ = 1 := Real.exp_zero
        _ ≤ (smoothCount Y y : ℝ) := hcnt

/-- The same bound, packaged as an `eventually` statement on `ℕ × ℕ`. -/
theorem eventually_smoothCount_ge_exp :
    ∀ᶠ p : ℕ × ℕ in Filter.atTop,
      (p.1 : ℝ) * Real.exp
          (-(⌊Real.log (p.1 : ℝ) / Real.log (p.2 : ℝ)⌋₊ : ℝ) *
            (Real.log (⌊Real.log (p.1 : ℝ) / Real.log (p.2 : ℝ)⌋₊ : ℝ) +
              Real.log (Real.log (p.2 : ℝ))) -
            7 * (⌊Real.log (p.1 : ℝ) / Real.log (p.2 : ℝ)⌋₊ : ℝ))
        ≤ (smoothCount p.1 p.2 : ℝ) := by
  obtain ⟨B, hB⟩ := smoothCount_eventually_ge_exp
  rw [eventually_atTop]
  refine ⟨(0, B), fun ⟨Y, y⟩ hge => ?_⟩
  exact hB Y y (Prod.le_def.mp hge).2

end PsiLB

end JSP314
