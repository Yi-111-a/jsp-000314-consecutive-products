import JSP314.SmoothLB
import JSP314.SmoothLB2
import Mathlib.Tactic

/-!
# A near-truth lower bound for `badSingletonCount`

We prove that `S(x) = badSingletonCount x` (the number of `n ≤ x` with `1 < n`
and `P(n)² ∣ n`) satisfies the eventual lower bound

  `S(x) ≥ x · exp(-C·√(log x · log log x))`

with `C = 10`, which is of the true order of magnitude: the count of bad
singletons is `x·exp(-(√2+o(1))·√(log x·log log x))`.

## Proof outline

We count `n = p² · q₁ · … · q_u` where

* `p` is a prime in `(2Z, 4Z]` with `Z = ⌈exp(√(log x·loglog x)/2)⌉`,
* `q₁, …, q_u` are *distinct* primes in `(Z, 2Z]`, i.e. `{q₁,…,q_u}` ranges
  over `(dyadicPrimes Z).powersetCard u`,
* `u ≈ log x / log Z ≈ 2·√(log x/loglog x)`.

Since every `q ≤ 2Z < p`, `P(n) = p` and `n` is a bad singleton.  The map is
injective: `p` is recovered as `P(n)` and the set of `qᵢ` as
`Nat.primeFactors (n / p²)` — a product of distinct primes has its prime factor
set equal to the finset itself (`primeFactors_prod_of_prime`).

The count is `(#dyadicPrimes (2Z)) · choose(#dyadicPrimes Z, u)`, which is
bounded below by `e^t/(4(t+2)) · (e^t/(16(t+1)))^u / u^u` with `t = √…/2`,
using `choose(D,u)·u! = descFactorial D u ≥ (D+1-u)^u` and the dyadic
Chebyshev bound `SmoothLB.eventually_dyadicPrimes_card_ge`.  An elementary
estimate gives `log(count) ≥ log x − 10·√(log x·loglog x)` eventually.
-/

namespace JSP314

namespace SingletonLBz

open Finset Filter SmoothLB

open scoped Topology

/-- The prime factors of a product of distinct primes form exactly that set. -/
theorem primeFactors_prod_of_prime {T : Finset ℕ} (hT : ∀ q ∈ T, Nat.Prime q) :
    Nat.primeFactors (T.prod id) = T := by
  ext r
  rw [Nat.mem_primeFactors]
  have hne : T.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q hq => (hT q hq).pos.ne'
  constructor
  · rintro ⟨hr, hd, -⟩
    obtain ⟨q, hq, hrd⟩ := ((Nat.prime_iff.mp hr).dvd_finsetProd_iff id).mp hd
    rcases (hT q hq).eq_one_or_self_of_dvd r hrd with h | h
    · exact absurd h hr.ne_one
    · rw [h]; exact hq
  · intro hr
    exact ⟨hT r hr, Finset.dvd_prod_of_mem id hr, hne⟩

/-- `(n + 1 - k)^k ≤ n.descFactorial k`. -/
theorem descFactorial_ge (n k : ℕ) : (n + 1 - k) ^ k ≤ n.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : n + 1 - (k + 1) = n - k := by omega
    rw [Nat.descFactorial_succ, e]
    calc (n - k) ^ (k + 1)
        = (n - k) * (n - k) ^ k := pow_succ' _ _
      _ ≤ (n - k) * (n + 1 - k) ^ k :=
          Nat.mul_le_mul_left _
            (Nat.pow_le_pow_left (by omega) k)
      _ ≤ (n - k) * n.descFactorial k := Nat.mul_le_mul_left _ ih

/-- `u ! ≤ u ^ u`. -/
theorem factorial_le_pow_self : ∀ u : ℕ, u.factorial ≤ u ^ u := by
  intro u
  induction u with
  | zero => simp
  | succ u ih =>
    rw [Nat.factorial_succ]
    calc (u + 1) * u.factorial
        ≤ (u + 1) * u ^ u := Nat.mul_le_mul_left _ ih
      _ ≤ (u + 1) * (u + 1) ^ u :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ u) u)
      _ = (u + 1) ^ (u + 1) := (pow_succ' _ _).symm

/-- Lower bound for binomial coefficients, real-valued:
`(D/2)^u / u^u ≤ D.choose u` when `2u ≤ D`. -/
theorem choose_ge_quarter {D u : ℕ} (h : 2 * u ≤ D) :
    ((D : ℝ) / 2) ^ u / (u : ℝ) ^ u ≤ (D.choose u : ℝ) := by
  have huD : u ≤ D := by omega
  have hdesc : (D + 1 - u) ^ u ≤ D.descFactorial u := descFactorial_ge D u
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hcast : ((D + 1 - u : ℕ) : ℝ) = (D : ℝ) + 1 - u := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hhalf : (D : ℝ) / 2 ≤ ((D + 1 - u : ℕ) : ℝ) := by
    rw [hcast]
    have h2 : (2 : ℝ) * u ≤ D := by exact_mod_cast h
    linarith
  have hfact : (u.factorial : ℝ) ≤ (u : ℝ) ^ u := by
    exact_mod_cast factorial_le_pow_self u
  have hpow : ((D : ℝ) / 2) ^ u ≤ (u.factorial : ℝ) * (D.choose u : ℝ) := by
    calc ((D : ℝ) / 2) ^ u ≤ ((D + 1 - u : ℕ) : ℝ) ^ u :=
          pow_le_pow_left₀ (by positivity) hhalf _
      _ ≤ (u.factorial : ℝ) * (D.choose u : ℝ) := by exact_mod_cast hdesc
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · subst hu0; simp
  · have hup : (0 : ℝ) < (u : ℝ) ^ u :=
      pow_pos (by exact_mod_cast hupos) _
    rw [div_le_iff₀ hup]
    calc ((D : ℝ) / 2) ^ u ≤ (u.factorial : ℝ) * (D.choose u : ℝ) := hpow
      _ ≤ (u : ℝ) ^ u * (D.choose u : ℝ) :=
          mul_le_mul_of_nonneg_right hfact (Nat.cast_nonneg _)
      _ = (D.choose u : ℝ) * (u : ℝ) ^ u := by ring

/-!
### The injection `(p, T) ↦ p² · ∏ T`
-/

/-- If `(4Z)²·(2Z)^u ≤ x`, then `badSingletonCount x` is at least
`#(dyadicPrimes (2Z)) · C(#(dyadicPrimes Z), u)`: map `p` prime in `(2Z, 4Z]`
and `T` a `u`-element subset of the primes in `(Z, 2Z]` to `p²·∏T`. -/
theorem badSingletonCount_ge_card (x Z u : ℕ)
    (hx : (4 * Z) ^ 2 * (2 * Z) ^ u ≤ x) :
    (dyadicPrimes (2 * Z)).card * ((dyadicPrimes Z).card.choose u)
      ≤ badSingletonCount x := by
  classical
  set P := dyadicPrimes (2 * Z) with hPdef
  set Q := dyadicPrimes Z with hQdef
  set S : Finset (ℕ × Finset ℕ) := P ×ˢ Q.powersetCard u with hSdef
  set f : ℕ × Finset ℕ → ℕ := fun s => s.1 ^ 2 * s.2.prod id with hfdef
  have hfacts : ∀ p : ℕ, ∀ T : Finset ℕ, (p, T) ∈ S →
      p.Prime ∧ 2 * Z < p ∧ p ≤ 4 * Z ∧
        (∀ q ∈ T, q.Prime ∧ Z < q ∧ q ≤ 2 * Z) ∧ T.card = u := by
    intro p T hm
    rw [hSdef, Finset.mem_product] at hm
    obtain ⟨hpP, hTQ⟩ := hm
    obtain ⟨hp, h2Zp, hp4Z⟩ := mem_dyadicPrimes.mp hpP
    rw [Finset.mem_powersetCard] at hTQ
    obtain ⟨hTQsub, hTcard⟩ := hTQ
    exact ⟨hp, h2Zp, by omega,
      fun q hq => mem_dyadicPrimes.mp (hTQsub hq), hTcard⟩
  have hsub : S.image f ⊆ (Finset.range (x + 1)).filter
      (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m) := by
    rw [Finset.image_subset_iff]
    rintro ⟨p, T⟩ hm
    obtain ⟨hp, h2Zp, hp4Z, hqT, hTcard⟩ := hfacts p T hm
    have hTpos : 1 ≤ T.prod id :=
      Finset.one_le_prod fun q hq => (hqT q hq).1.one_lt.le
    have hTle : T.prod id ≤ (2 * Z) ^ u := by
      calc T.prod id ≤ (2 * Z) ^ T.card :=
            Finset.prod_le_pow_card T id (2 * Z) fun q hq => (hqT q hq).2.2
        _ = (2 * Z) ^ u := by rw [hTcard]
    have hsmooth : ∀ r : ℕ, r.Prime → r ∣ T.prod id → r ≤ p := by
      intro r hr hrd
      obtain ⟨q, hq, hrq⟩ := ((Nat.prime_iff.mp hr).dvd_finsetProd_iff id).mp hrd
      rcases (hqT q hq).1.eq_one_or_self_of_dvd r hrq with h | h
      · exact absurd h hr.ne_one
      · rw [h]
        exact ((hqT q hq).2.2).trans h2Zp.le
    have hlpf : largestPrimeFactor (p ^ 2 * T.prod id) = p :=
      largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hTpos hsmooth
    have hle : p ^ 2 * T.prod id ≤ x := by
      calc p ^ 2 * T.prod id ≤ (4 * Z) ^ 2 * (2 * Z) ^ u :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hp4Z 2) hTle
        _ ≤ x := hx
    have h2 : 2 ≤ p ^ 2 * T.prod id := by
      calc 2 ≤ 2 ^ 2 * 1 := by norm_num
        _ ≤ p ^ 2 * T.prod id :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hTpos
    simp only [hfdef, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
    rw [hlpf]
    exact dvd_mul_right _ _
  have hinj : Set.InjOn f S := by
    rintro ⟨p, T⟩ hmT ⟨r, U⟩ hmU h
    obtain ⟨hp, h2Zp, hp4Z, hqT, hTcard⟩ := hfacts p T hmT
    obtain ⟨hr, h2Zr, hr4Z, hsU, hUcard⟩ := hfacts r U hmU
    have h' : p ^ 2 * T.prod id = r ^ 2 * U.prod id := h
    have hsmoothT : ∀ s : ℕ, s.Prime → s ∣ T.prod id → s ≤ p := by
      intro s hs hsd
      obtain ⟨q, hq, hsq⟩ := ((Nat.prime_iff.mp hs).dvd_finsetProd_iff id).mp hsd
      rcases (hqT q hq).1.eq_one_or_self_of_dvd s hsq with hh | hh
      · exact absurd hh hs.ne_one
      · rw [hh]
        exact ((hqT q hq).2.2).trans h2Zp.le
    have hsmoothU : ∀ s : ℕ, s.Prime → s ∣ U.prod id → s ≤ r := by
      intro s hs hsd
      obtain ⟨q, hq, hsq⟩ := ((Nat.prime_iff.mp hs).dvd_finsetProd_iff id).mp hsd
      rcases (hsU q hq).1.eq_one_or_self_of_dvd s hsq with hh | hh
      · exact absurd hh hs.ne_one
      · rw [hh]
        exact ((hsU q hq).2.2).trans h2Zr.le
    have hTpos : 1 ≤ T.prod id :=
      Finset.one_le_prod fun q hq => (hqT q hq).1.one_lt.le
    have hUpos : 1 ≤ U.prod id :=
      Finset.one_le_prod fun q hq => (hsU q hq).1.one_lt.le
    have hpr : p = r := by
      have e1 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hTpos hsmoothT
      have e2 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hr hUpos hsmoothU
      rw [← e1, h', e2]
    subst hpr
    have hTU : T.prod id = U.prod id := Nat.mul_left_cancel (pow_pos hp.pos 2) h'
    have hTU' : T = U := by
      rw [← primeFactors_prod_of_prime (fun q hq => (hqT q hq).1),
        ← primeFactors_prod_of_prime (fun q hq => (hsU q hq).1), hTU]
    rw [hTU']
  have hcard : S.card = P.card * Q.card.choose u := by
    rw [hSdef, Finset.card_product, Finset.card_powersetCard]
  calc P.card * Q.card.choose u = S.card := hcard.symm
    _ = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ badSingletonCount x := Finset.card_le_card hsub

/-!
### Assembly of the final bound
-/

set_option maxHeartbeats 1600000 in
theorem badSingletonCount_eventually_ge_zscale :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) * Real.exp (-C * Real.sqrt (Real.log x * Real.log (Real.log x)))
        ≤ (badSingletonCount x : ℝ) := by
  -- `L = log x → ∞`, `L2 = log log x → ∞`, `L2/L → 0`
  have hLt : Filter.Tendsto (fun x : ℕ => Real.log (x : ℝ)) Filter.atTop
      Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL2t : Filter.Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hLt
  have hratio : Filter.Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))
      Filter.atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hLt).tendsto_div_nhds_zero
  have h64 : ∀ᶠ x : ℕ in Filter.atTop,
      64 * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have h := hratio.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 64 by norm_num))
    filter_upwards [h, hLt.eventually_ge_atTop 1] with x hx hL1
    have hLpos : (0 : ℝ) < Real.log x := by linarith
    rw [div_lt_iff₀ hLpos] at hx
    linarith
  -- `t = √(L·L2)/2 ≥ 4·L2` eventually
  have htge : ∀ᶠ x : ℕ in Filter.atTop,
      4 * Real.log (Real.log (x : ℝ)) ≤
        Real.sqrt (Real.log x * Real.log (Real.log x)) / 2 := by
    filter_upwards [h64, hL2t.eventually_ge_atTop 0] with x hx hx2
    set L := Real.log (x : ℝ) with hLdef
    set L2 := Real.log L with hL2def
    have hA : 8 * L2 ≤ Real.sqrt (L * L2) := by
      have h64sq : (8 * L2) ^ 2 ≤ L * L2 := by
        have h := mul_le_mul_of_nonneg_right hx hx2
        nlinarith [h, hx2]
      calc 8 * L2 = Real.sqrt ((8 * L2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ Real.sqrt (L * L2) := Real.sqrt_le_sqrt h64sq
    linarith
  -- `Z = ⌈e^t⌉ → ∞`
  have hexp_t : Filter.Tendsto
      (fun x : ℕ => Real.exp (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2))
      Filter.atTop Filter.atTop := by
    apply Real.tendsto_exp_atTop.comp
    refine tendsto_atTop_mono' Filter.atTop ?_ hL2t
    filter_upwards [htge, hL2t.eventually_ge_atTop 0] with x hx hx0
    linarith
  have hZt : Filter.Tendsto
      (fun x : ℕ => ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono' Filter.atTop
        (Filter.Eventually.of_forall fun x => Nat.le_ceil _) hexp_t)
  have h2Zt : Filter.Tendsto
      (fun x : ℕ => 2 * ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun n => le_mul_of_one_le_left (Nat.zero_le _) one_le_two) hZt
  -- dyadic Chebyshev lower bounds along `Z` and `2Z`
  have hDZ : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈Real.exp (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊ : ℝ) /
          (8 * Real.log ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊)
        ≤ ((dyadicPrimes ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊).card : ℝ) :=
    hZt.eventually eventually_dyadicPrimes_card_ge
  have hD2Z : ∀ᶠ x : ℕ in Filter.atTop,
      ((2 * ⌈Real.exp
        (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (2 * ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊))
        ≤ ((dyadicPrimes (2 * ⌈Real.exp
            (Real.sqrt (Real.log x * Real.log (Real.log x)) / 2)⌉₊)).card : ℝ) := by
    filter_upwards [h2Zt.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  refine ⟨10, by norm_num, ?_⟩
  filter_upwards [h64, htge, hDZ, hD2Z, hLt.eventually_ge_atTop 32,
    hL2t.eventually_ge_atTop 9, eventually_ge_atTop 4]
    with x h64' htge' hDZ' hD2Z' hL hL2 hx4
  -- abbreviations
  set L : ℝ := Real.log (x : ℝ) with hLdef
  set L2 : ℝ := Real.log L with hL2def
  set A : ℝ := Real.sqrt (L * L2) with hAdef
  set t : ℝ := A / 2 with htdef
  set Z : ℕ := ⌈Real.exp t⌉₊ with hZdef
  set v : ℝ := (L - 6) / (t + 2) with hvdef
  set u : ℕ := ⌊v⌋₊ - 4 with hudef
  -- basic facts
  have hxp : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hLpos : 0 < L := by linarith
  have hL2pos : 0 < L2 := by linarith
  have hLL2 : 0 ≤ L * L2 := mul_nonneg hLpos.le hL2pos.le
  have hAsq : A ^ 2 = L * L2 := Real.sq_sqrt hLL2
  have hA8 : 8 * L2 ≤ A := by
    have h64sq : (8 * L2) ^ 2 ≤ L * L2 := by
      have h := mul_le_mul_of_nonneg_right h64' hL2pos.le
      nlinarith [h, hL2pos.le]
    calc 8 * L2 = Real.sqrt ((8 * L2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ A := Real.sqrt_le_sqrt h64sq
  have hApos : 0 < A := by linarith [hA8, hL2pos]
  have hAle : A ≤ L / 8 := by
    have hsq : L * L2 ≤ (L / 8) ^ 2 := by nlinarith [h64', hLpos]
    calc A = Real.sqrt (L * L2) := rfl
      _ ≤ Real.sqrt ((L / 8) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = L / 8 := Real.sqrt_sq (by linarith)
  have ht_lo : 4 * L2 ≤ t := by linarith [htge']
  have ht_hi : t ≤ L / 16 := by linarith [hAle]
  have ht_pos : 0 < t := by linarith [hL2pos]
  -- `Z` bounds
  have hexpt1 : Real.exp t ≤ (Z : ℝ) := Nat.le_ceil _
  have hexpt2 : (Z : ℝ) ≤ Real.exp (t + 1) := by
    have h1 : (Z : ℝ) ≤ Real.exp t + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg t)).le
    have he2 : (2 : ℝ) ≤ Real.exp 1 :=
      (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans Real.exp_one_gt_d9.le
    have h2 : Real.exp t + 1 ≤ Real.exp (t + 1) := by
      rw [Real.exp_add]
      have hge : 1 ≤ Real.exp t :=
        Real.exp_zero ▸ Real.exp_le_exp.mpr ht_pos.le
      nlinarith [hge, he2, Real.exp_nonneg t]
    exact h1.trans h2
  have hZ2hi : (2 * (Z : ℝ)) ≤ Real.exp (t + 2) := by
    have he2 : (2 : ℝ) ≤ Real.exp 1 :=
      (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans Real.exp_one_gt_d9.le
    calc 2 * (Z : ℝ) ≤ 2 * Real.exp (t + 1) := by linarith [hexpt2]
      _ ≤ Real.exp 1 * Real.exp (t + 1) :=
          mul_le_mul_of_nonneg_right he2 (Real.exp_nonneg _)
      _ = Real.exp (t + 2) := by
          rw [← Real.exp_add]; congr 1; ring
  have hZpos : 0 < Z := by
    have : (0 : ℝ) < Z := lt_of_lt_of_le (Real.exp_pos t) hexpt1
    exact_mod_cast this
  have hlogZ : Real.log Z ≤ t + 1 := by
    have h : Real.log (Z : ℝ) ≤ Real.log (Real.exp (t + 1)) :=
      Real.log_le_log (by exact_mod_cast hZpos) hexpt2
    rwa [Real.log_exp] at h
  have hlogZ_ge : t ≤ Real.log Z := by
    have h : Real.log (Real.exp t) ≤ Real.log (Z : ℝ) :=
      Real.log_le_log (Real.exp_pos t) hexpt1
    rwa [Real.log_exp] at h
  have hlog2Z : Real.log (2 * (Z : ℝ)) ≤ t + 2 := by
    have h2Zpos : (0 : ℝ) < 2 * (Z : ℝ) := by
      have hZpos' : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZpos
      linarith
    have h : Real.log (2 * (Z : ℝ)) ≤ Real.log (Real.exp (t + 2)) :=
      Real.log_le_log h2Zpos hZ2hi
    rwa [Real.log_exp] at h
  -- `u` bounds
  have hv0 : 0 ≤ v := div_nonneg (by linarith) (by linarith)
  have hu_le_v : (u : ℝ) ≤ v :=
    (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le hv0)
  have hfloor4 : 4 ≤ ⌊v⌋₊ := by
    apply Nat.le_floor
    -- v ≥ 4 since t + 2 ≤ L/8 and L ≥ 32
    have ht2 : t + 2 ≤ L / 8 := by linarith [ht_hi, hL]
    calc (4 : ℝ) ≤ 6 := by norm_num
      _ ≤ (L - 6) / (L / 8) := by
          rw [le_div_iff₀ (by linarith : (0:ℝ) < L / 8)]
          nlinarith [hL]
      _ ≤ v := by
          apply div_le_div₀ (by linarith) le_rfl (by linarith) ht2
  have hu4 : u + 4 = ⌊v⌋₊ := Nat.sub_add_cancel hfloor4
  have hu_eq : (u : ℝ) = ⌊v⌋₊ - 4 := by
    have := congrArg (Nat.cast : ℕ → ℝ) hu4
    push_cast at this
    linarith
  have hu2 : (u : ℝ) + 2 ≤ v - 2 := by
    have hfl : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv0
    linarith [hu_eq]
  have hu_ge : (u : ℝ) ≥ v - 5 := by
    have hfl : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
    linarith [hu_eq]
  have hu_le_L : (u : ℝ) ≤ L := by
    calc (u : ℝ) ≤ v := hu_le_v
      _ = (L - 6) / (t + 2) := rfl
      _ ≤ L := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < t + 2)]
          nlinarith [hLpos, ht_pos]
  -- `(u+2)(t+2) ≤ L - 10`
  have hu2t2 : ((u : ℝ) + 2) * (t + 2) ≤ L - 10 := by
    calc ((u : ℝ) + 2) * (t + 2) ≤ (v - 2) * (t + 2) :=
          mul_le_mul_of_nonneg_right hu2 (by linarith)
      _ = (L - 6) - 2 * (t + 2) := by
          have hvt2 : v * (t + 2) = L - 6 := by
            rw [hvdef]
            exact div_mul_cancel₀ _ (ne_of_gt (by linarith [ht_pos]))
          rw [sub_mul, hvt2]
      _ ≤ L - 10 := by linarith [ht_pos]
  -- the admissibility bound `(4Z)²·(2Z)^u ≤ x`
  have hxbound : (4 * Z) ^ 2 * (2 * Z) ^ u ≤ x := by
    have hre : ((4 * Z) ^ 2 * (2 * Z) ^ u : ℝ) ≤ (x : ℝ) := by
      have e16 : (16 : ℝ) ≤ Real.exp 12 := by
        have e12 : Real.exp 12 = Real.exp 1 ^ 12 := by
          have := Real.exp_nat_mul (1 : ℝ) 12
          rw [Nat.cast_ofNat, mul_one] at this
          exact this
        have e2 : (2 : ℝ) ≤ Real.exp 1 :=
          (by norm_num : (2 : ℝ) ≤ (2.7182818283 : ℝ)).trans Real.exp_one_gt_d9.le
        calc (16 : ℝ) ≤ (2 : ℝ) ^ 12 := by norm_num
          _ ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) e2 _
          _ = Real.exp 12 := e12.symm
      have step1 : (4 * (Z : ℝ)) ^ 2 * (2 * (Z : ℝ)) ^ u
          ≤ 16 * Real.exp (2 * (t + 1)) * Real.exp ((u : ℝ) * (t + 2)) := by
        have pa : (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (t + 1) ^ 2 := by
          calc (4 * (Z : ℝ)) ^ 2 = 16 * (Z : ℝ) ^ 2 := by ring
            _ ≤ 16 * Real.exp (t + 1) ^ 2 :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (by positivity) hexpt2 _) (by norm_num)
        have pb : (2 * (Z : ℝ)) ^ u ≤ Real.exp ((u : ℝ) * (t + 2)) := by
          calc (2 * (Z : ℝ)) ^ u ≤ Real.exp (t + 2) ^ u :=
                pow_le_pow_left₀ (by positivity) hZ2hi _
            _ = Real.exp ((u : ℝ) * (t + 2)) := (Real.exp_nat_mul _ _).symm
        have pa' : (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (2 * (t + 1)) := by
          calc (4 * (Z : ℝ)) ^ 2 ≤ 16 * Real.exp (t + 1) ^ 2 := pa
            _ = 16 * Real.exp (2 * (t + 1)) := by
                rw [show (2:ℝ) * (t+1) = ((2:ℕ) : ℝ) * (t+1) from by push_cast; ring,
                  Real.exp_nat_mul]
        exact mul_le_mul pa' pb (by positivity) (by positivity)
      calc ((4 * Z) ^ 2 * (2 * Z) ^ u : ℝ)
          = (4 * (Z : ℝ)) ^ 2 * (2 * (Z : ℝ)) ^ u := by ring
        _ ≤ 16 * Real.exp (2 * (t + 1)) * Real.exp ((u : ℝ) * (t + 2)) := step1
        _ = 16 * Real.exp (2 * (t + 1) + (u : ℝ) * (t + 2)) := by
            rw [Real.exp_add]; ring
        _ ≤ 16 * Real.exp (L - 12) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 16)
            apply Real.exp_le_exp.mpr
            linarith [hu2t2]
        _ ≤ Real.exp L := by
            calc 16 * Real.exp (L - 12)
                ≤ Real.exp 12 * Real.exp (L - 12) :=
                  mul_le_mul_of_nonneg_right e16 (Real.exp_nonneg _)
              _ = Real.exp L := by rw [← Real.exp_add]; congr 1; ring
        _ = (x : ℝ) := Real.exp_log hxp
    exact_mod_cast hre
  -- dyadic bounds at this `x`
  have hcardP : Real.exp t / (4 * (t + 2)) ≤
      ((dyadicPrimes (2 * Z)).card : ℝ) := by
    have hZ2 : ((2 * Z : ℕ) : ℝ) = 2 * (Z : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have hlogpos : 0 < Real.log (2 * (Z : ℝ)) := by
      apply Real.log_pos
      have h1 : (1 : ℝ) < Real.exp t := Real.exp_zero ▸ Real.exp_lt_exp.mpr ht_pos
      linarith [hexpt1]
    have h2 : (2 * Real.exp t) / (8 * (t + 2)) ≤
        ((2 * Z : ℕ) : ℝ) / (8 * Real.log (2 * (Z : ℝ))) := by
      apply div_le_div₀ (by positivity : (0 : ℝ) ≤ ((2 * Z : ℕ) : ℝ))
      · rw [hZ2]; linarith [hexpt1]
      · exact mul_pos (by norm_num) hlogpos
      · linarith [hlog2Z]
    have heq : Real.exp t / (4 * (t + 2)) = (2 * Real.exp t) / (8 * (t + 2)) := by
      have hne : (t + 2 : ℝ) ≠ 0 := by linarith [ht_pos]
      field_simp [hne]; ring
    rw [heq]
    exact h2.trans hD2Z'
  have hcardQ : Real.exp t / (8 * (t + 1)) ≤
      ((dyadicPrimes Z).card : ℝ) := by
    have hlogpos : 0 < Real.log (Z : ℝ) := by
      apply Real.log_pos
      have h1 : (1 : ℝ) < Real.exp t := Real.exp_zero ▸ Real.exp_lt_exp.mpr ht_pos
      linarith [hexpt1]
    have h2 : Real.exp t / (8 * (t + 1)) ≤ (Z : ℝ) / (8 * Real.log Z) :=
      div_le_div₀ (Nat.cast_nonneg _) hexpt1 (mul_pos (by norm_num) hlogpos)
        (by linarith [hlogZ])
    exact h2.trans hDZ'
  -- `e^t ≥ L^4`
  have hexp_L4 : (L : ℝ) ^ 4 ≤ Real.exp t := by
    have h1 : Real.exp (4 * L2) = (L : ℝ) ^ 4 := by
      have e : Real.exp (((4 : ℕ) : ℝ) * L2) = (Real.exp L2) ^ 4 :=
        Real.exp_nat_mul L2 4
      rw [hL2def, Real.exp_log hLpos, Nat.cast_ofNat] at e
      exact e
    calc (L : ℝ) ^ 4 = Real.exp (4 * L2) := h1.symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht_lo
  -- `t + 1 ≤ L` and `t + 2 ≤ L`
  have ht1_L : t + 1 ≤ L := by linarith [ht_hi, hL]
  have ht2_L : t + 2 ≤ L := by linarith [ht_hi, hL]
  -- `2u ≤ #dyadicPrimes Z`:  `cardQ ≥ e^t/(8(t+1)) ≥ L⁴/(8L) = L³/8 ≥ 2L ≥ 2u`
  have hcardQ_L : (L : ℝ) ^ 3 / 8 ≤ ((dyadicPrimes Z).card : ℝ) := by
    calc (L : ℝ) ^ 3 / 8 = (L : ℝ) ^ 4 / (8 * L) := by
          rw [div_eq_div_iff (by norm_num : (8:ℝ) ≠ 0)
            (mul_ne_zero (by norm_num) hLpos.ne')]
          ring
      _ ≤ Real.exp t / (8 * (t + 1)) :=
          div_le_div₀ (Real.exp_nonneg _) hexp_L4
            (mul_pos (by norm_num) (by linarith [ht_pos])) (by linarith [ht1_L])
      _ ≤ ((dyadicPrimes Z).card : ℝ) := hcardQ
  have h2u : 2 * u ≤ (dyadicPrimes Z).card := by
    have hLsq : (1024 : ℝ) ≤ L ^ 2 :=
      calc (1024 : ℝ) = 32 ^ 2 := by norm_num
        _ ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL _
    have h3 : (1024 : ℝ) * L ≤ L ^ 3 := by
      have e : (L : ℝ) ^ 3 = L ^ 2 * L := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hLsq hLpos.le
    have h1 : (2 : ℝ) * u ≤ L ^ 3 / 8 := by linarith [hu_le_L, h3, hLpos]
    have h2 : (2 : ℝ) * u ≤ ((dyadicPrimes Z).card : ℝ) := h1.trans hcardQ_L
    exact_mod_cast h2
  -- the choose bound: `e^{u·t}/((16(t+1))^u·L^u) ≤ cardQ.choose u`
  have hchoose : Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)
      ≤ (((dyadicPrimes Z).card.choose u : ℕ) : ℝ) := by
    have h0 := choose_ge_quarter (D := (dyadicPrimes Z).card) (u := u) h2u
    have hQ2 : Real.exp t / (16 * (t + 1)) ≤ ((dyadicPrimes Z).card : ℝ) / 2 := by
      rw [show (16 : ℝ) * (t + 1) = (8 * (t + 1)) * 2 by ring, ← div_div]
      linarith [hcardQ]
    have hrew : (Real.exp t / (16 * (t + 1))) ^ u =
        Real.exp ((u : ℝ) * t) / (16 * (t + 1)) ^ u := by
      rw [div_pow, Real.exp_nat_mul]
    have huu : (u : ℝ) ^ u ≤ (L : ℝ) ^ u :=
      pow_le_pow_left₀ (by positivity) hu_le_L u
    calc Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)
        = (Real.exp t / (16 * (t + 1))) ^ u / (L : ℝ) ^ u := by
          rw [hrew, div_div]
      _ ≤ (((dyadicPrimes Z).card : ℝ) / 2) ^ u / (u : ℝ) ^ u := by
          apply div_le_div₀ (pow_nonneg (by positivity) _)
          · exact pow_le_pow_left₀
              (div_nonneg (Real.exp_nonneg _) (by linarith [ht_pos])) hQ2 u
          · rcases Nat.eq_zero_or_pos u with hu0 | hupos
            · simp [hu0]
            · exact pow_pos (by exact_mod_cast hupos) _
          · exact huu
      _ ≤ _ := h0
  -- product of the two bounds
  have hprod : Real.exp t / (4 * (t + 2)) *
      (Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (L : ℝ) ^ u))
      ≤ (badSingletonCount x : ℝ) := by
    calc Real.exp t / (4 * (t + 2)) *
          (Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (L : ℝ) ^ u))
        ≤ ((dyadicPrimes (2 * Z)).card : ℝ) *
          (((dyadicPrimes Z).card.choose u : ℕ) : ℝ) :=
          mul_le_mul hcardP hchoose
            (div_nonneg (Real.exp_nonneg _)
              (mul_nonneg (pow_nonneg (by linarith [ht_pos]) _)
                (pow_nonneg hLpos.le _)))
            (Nat.cast_nonneg _)
      _ ≤ (badSingletonCount x : ℝ) := by
          exact_mod_cast badSingletonCount_ge_card x Z u hxbound
  -- numerator bound: `e^{t + u·t} ≥ e^{L − 3A}`
  have hnum : Real.exp (L - 3 * A) ≤ Real.exp (t + (u : ℝ) * t) := by
    apply Real.exp_le_exp.mpr
    have hvt : v * t = (L - 6) - 2 * (L - 6) / (t + 2) := by
      have hne : (t + 2 : ℝ) ≠ 0 := ne_of_gt (by linarith [ht_pos])
      have hvt2 : v * (t + 2) = L - 6 := by
        rw [hvdef]; exact div_mul_cancel₀ _ hne
      have h2v : 2 * v = 2 * (L - 6) / (t + 2) := by
        rw [hvdef, mul_div_assoc']
      rw [show v * t = v * (t + 2) - 2 * v by ring, hvt2, h2v]
    have hfrac : 2 * (L - 6) / (t + 2) ≤ A / 2 := by
      have h1 : 2 * (L - 6) / (t + 2) ≤ 2 * L / (t + 2) :=
        div_le_div₀ (by linarith) (by linarith) (by linarith) le_rfl
      have h2 : 2 * L / (t + 2) ≤ 2 * L / t :=
        div_le_div₀ (by linarith) le_rfl ht_pos (by linarith)
      have h3 : 2 * L / t = 4 * A / L2 := by
        have hA2 : (A / 2 : ℝ) ≠ 0 := by linarith [hApos]
        rw [htdef, div_eq_div_iff hA2 hL2pos.ne']
        linarith [hAsq]
      have h4 : 4 * A / L2 ≤ A / 2 := by
        rw [div_le_iff₀ hL2pos]
        nlinarith [hApos, hL2]
      linarith [h1, h2, h3, h4]
    have hut : (v - 5) * t ≤ (u : ℝ) * t :=
      mul_le_mul_of_nonneg_right hu_ge ht_pos.le
    linarith [hvt, hfrac, hut, htdef, hA8, hL2]
  -- denominator bound: `4(t+2)·(16(t+1))^u·L^u ≤ e^{7A}`
  have eL : Real.exp L2 = L := by rw [hL2def]; exact Real.exp_log hLpos
  have huL2 : (u : ℝ) * L2 ≤ 2 * A := by
    have huv : (u : ℝ) ≤ L / (t + 2) := by
      calc (u : ℝ) ≤ v := hu_le_v
        _ = (L - 6) / (t + 2) := rfl
        _ ≤ L / (t + 2) := div_le_div₀ (by linarith) (by linarith) (by linarith) le_rfl
    have hLt : L / (t + 2) ≤ L / t :=
      div_le_div₀ hLpos.le le_rfl ht_pos (by linarith)
    have hLtA : L / t = 2 * A / L2 := by
      have hA2 : (A / 2 : ℝ) ≠ 0 := by linarith [hApos]
      rw [htdef, div_eq_div_iff hA2 hL2pos.ne']
      linarith [hAsq]
    calc (u : ℝ) * L2 ≤ (L / t) * L2 :=
          mul_le_mul_of_nonneg_right (huv.trans hLt) hL2pos.le
      _ = (2 * A / L2) * L2 := by rw [hLtA]
      _ = 2 * A := div_mul_cancel₀ _ hL2pos.ne'
  have hden : 4 * (t + 2) * ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)
      ≤ Real.exp (7 * A) := by
    have hd1 : 4 * (t + 2) ≤ Real.exp A := by
      have h1 : 4 * (t + 2) ≤ 8 * L := by linarith [ht_hi, hL]
      have hlog : Real.log (8 * L) ≤ A := by
        have h8 : Real.log (8 * L) = Real.log 8 + L2 := by
          rw [hL2def, Real.log_mul (by norm_num) hLpos.ne']
        have hlog8 : Real.log 8 ≤ 3 := by
          have e : Real.log 8 = 3 * Real.log 2 := by
            rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
          rw [e]
          linarith [Real.log_two_lt_d9]
        linarith [hA8]
      have h2 : 8 * L ≤ Real.exp A := by
        calc 8 * L = Real.exp (Real.log (8 * L)) :=
              (Real.exp_log (mul_pos (by norm_num) hLpos)).symm
          _ ≤ Real.exp A := Real.exp_le_exp.mpr hlog
      linarith
    have hd2 : (16 * (t + 1)) ^ u ≤ Real.exp (4 * A) := by
      have h1 : 16 * (t + 1) ≤ (L : ℝ) ^ 2 := by nlinarith [ht1_L, hL]
      have e : Real.exp ((2 * u : ℕ) * L2) = ((L : ℝ) ^ 2) ^ u := by
        rw [Real.exp_nat_mul, eL, pow_mul]
      have hcast : ((2 * u : ℕ) : ℝ) * L2 = 2 * (u : ℝ) * L2 := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
      calc (16 * (t + 1)) ^ u ≤ ((L : ℝ) ^ 2) ^ u :=
            pow_le_pow_left₀ (by linarith [ht_pos]) h1 _
        _ = Real.exp ((2 * u : ℕ) * L2) := e.symm
        _ = Real.exp (2 * (u : ℝ) * L2) := by rw [hcast]
        _ ≤ Real.exp (4 * A) := Real.exp_le_exp.mpr (by linarith [huL2])
    have hd3 : (L : ℝ) ^ u ≤ Real.exp (2 * A) := by
      have e : Real.exp ((u : ℝ) * L2) = (L : ℝ) ^ u := by
        rw [Real.exp_nat_mul, eL]
      rw [← e]
      exact Real.exp_le_exp.mpr huL2
    calc 4 * (t + 2) * ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)
        ≤ Real.exp A * (Real.exp (4 * A) * Real.exp (2 * A)) :=
          mul_le_mul hd1 (mul_le_mul hd2 hd3 (pow_nonneg hLpos.le _)
            (Real.exp_nonneg _))
            (mul_nonneg (pow_nonneg (by linarith [ht_pos]) _)
              (pow_nonneg hLpos.le _)) (Real.exp_nonneg _)
      _ = Real.exp (7 * A) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  -- final assembly
  have hDpos : (0 : ℝ) < 4 * (t + 2) * ((16 * (t + 1)) ^ u * (L : ℝ) ^ u) :=
    mul_pos (mul_pos (by norm_num) (by linarith [ht_pos]))
      (mul_pos (pow_pos (by linarith [ht_pos]) _) (pow_pos hLpos _))
  calc (x : ℝ) * Real.exp (-10 * A)
      = Real.exp (L - 10 * A) := by
        have e : (x : ℝ) = Real.exp L := (Real.exp_log hxp).symm
        rw [e, ← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (t + (u : ℝ) * t) /
          (4 * (t + 2) * ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)) := by
        rw [le_div_iff₀ hDpos]
        calc Real.exp (L - 10 * A) *
              (4 * (t + 2) * ((16 * (t + 1)) ^ u * (L : ℝ) ^ u))
            ≤ Real.exp (L - 10 * A) * Real.exp (7 * A) :=
              mul_le_mul_of_nonneg_left hden (Real.exp_nonneg _)
          _ = Real.exp (L - 3 * A) := by rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (t + (u : ℝ) * t) := hnum
    _ = Real.exp t / (4 * (t + 2)) *
          (Real.exp ((u : ℝ) * t) / ((16 * (t + 1)) ^ u * (L : ℝ) ^ u)) := by
        rw [div_mul_div_comm, ← Real.exp_add]
    _ ≤ (badSingletonCount x : ℝ) := hprod

end SingletonLBz

end JSP314
