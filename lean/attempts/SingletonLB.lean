import JSP314.Defs

/-!
# JSP-000314 — stronger/complementary lower bounds for `badSingletonCount`

This scratch file (not part of the `JSP314` lake glob) proves lower bounds on
`badSingletonCount x` beyond `Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x`
(`JSP314.Counting.badSingletonCount_ge_primeCounting`), plus stability lemmas for
the bad-singleton predicate.

Main results (all fully proved):

* `largestPrimeFactor_two_pow_mul_prime_sq` : for an odd prime `p` and any
  `a ≥ 0`, `largestPrimeFactor (2^a * p^2) = p` — every prime divisor of
  `2^a * p^2` is `2` or `p`, so `P ≤ p`, while `p ∣ n` gives `p ≤ P`.
* `two_pow_mul_prime_sq_mem_badSingleton` : `2^a * p^2` is a bad singleton.
* `badSingletonCount_ge_dyadicPairs` : the clean pair count
  `#{(a, p) : a ≤ log₂ x, p ≤ √x odd prime, 2^a·p² ≤ x} ≤ badSingletonCount x`,
  via the injection `(a, p) ↦ 2^a·p²` (`p` is recovered as the unique odd prime
  factor of the image, then `p²` is cancelled and `Nat.pow_right_injective`
  recovers `a`).
* `badSingletonCount_ge_oddPrimeSum` : the dyadic sum
  `∑_{a < log₂ x + 1} #{p ∈ Nat.primesLE (Nat.sqrt (x / 2^a)) : 2 < p}
    ≤ badSingletonCount x`, proved via `Finset.sigma` + `card_le_card_of_injOn`.
* `badSingletonCount_ge_primeCounting_sum` : the explicit weakened form
  `∑_{a < log₂ x + 1} (Nat.primeCounting (Nat.sqrt (x / 2^a)) - 1)
    ≤ badSingletonCount x`,
  strictly stronger than the `a = 0` bound `π(√x) ≤ badSingletonCount x` (the
  `a = 0` summand alone is `π(√x) - 1`, and `a = 1` adds `π(√(x/2)) - 1`).
* `largestPrimeFactor_mul_prime_sq`, `badSingleton_mul_prime_sq` : the
  bad-singleton predicate is preserved under `n ↦ n * q^2` for primes
  `q ≤ largestPrimeFactor n` (every prime factor of `n*q²` is `≤ P(n)`).
* `badSingletonCount_mul_prime_sq_ge` : counting corollary of the above:
  `#{n ≤ x : bad ∧ q ≤ P(n)} ≤ badSingletonCount (x * q^2)` via `n ↦ n*q²`.
* `badSingletonCount_mul_mono` : `badSingletonCount x ≤ badSingletonCount (k*x)`
  for `k ≥ 1`.
* `badSingletonCount_eventually_ge_primeCounting` : the `∀ᶠ x in atTop`
  restatement of the prime-squares bound.

The real-analytic `√x / (2 log x)` bound is *not* included: it would need a
prime-number-theorem input and is not a trivial consequence of what is here.
-/

namespace JSP314

open Finset

/-- For an odd prime `p`, `largestPrimeFactor (2^a * p^2) = p`. -/
theorem largestPrimeFactor_two_pow_mul_prime_sq {a p : ℕ} (hp : Nat.Prime p)
    (hodd : 2 < p) :
    largestPrimeFactor (2 ^ a * p ^ 2) = p := by
  have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
  have h3 : 3 ≤ p := hodd
  have hp9 : 9 ≤ p ^ 2 :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
  have hn : 2 ≤ 2 ^ a * p ^ 2 := by
    have hle : p ^ 2 ≤ 2 ^ a * p ^ 2 := by
      conv_lhs => rw [← one_mul (p ^ 2)]
      exact Nat.mul_le_mul h2a le_rfl
    omega
  apply le_antisymm
  · have hPp := largestPrimeFactor_prime hn
    have hPd := largestPrimeFactor_dvd hn
    rcases hPp.dvd_mul.mp hPd with h | h
    · have h2 := hPp.dvd_of_dvd_pow h
      have he : largestPrimeFactor (2 ^ a * p ^ 2) = 2 :=
        (Nat.prime_dvd_prime_iff_eq hPp Nat.prime_two).mp h2
      omega
    · have h2 := hPp.dvd_of_dvd_pow h
      exact ((Nat.prime_dvd_prime_iff_eq hPp hp).mp h2).le
  · exact prime_dvd_le_largestPrimeFactor hn hp
      (dvd_mul_of_dvd_right (dvd_pow_self p two_ne_zero) (2 ^ a))

/-- For an odd prime `p`, `2^a * p^2` is a bad singleton. -/
theorem two_pow_mul_prime_sq_mem_badSingleton {a p : ℕ} (hp : Nat.Prime p)
    (hodd : 2 < p) :
    1 < 2 ^ a * p ^ 2 ∧
      (largestPrimeFactor (2 ^ a * p ^ 2)) ^ 2 ∣ 2 ^ a * p ^ 2 := by
  have h2a : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
  have h3 : 3 ≤ p := hodd
  have hp9 : 9 ≤ p ^ 2 :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
  have hn : 2 ≤ 2 ^ a * p ^ 2 := by
    have hle : p ^ 2 ≤ 2 ^ a * p ^ 2 := by
      conv_lhs => rw [← one_mul (p ^ 2)]
      exact Nat.mul_le_mul h2a le_rfl
    omega
  refine ⟨hn, ?_⟩
  rw [largestPrimeFactor_two_pow_mul_prime_sq hp hodd]
  exact dvd_mul_of_dvd_right (dvd_refl _) _

/-- Injectivity helper: if `2^a₁·p₁² = 2^a₂·p₂²` with `p₁` an odd prime and
`p₂` prime, then `a₁ = a₂` and `p₁ = p₂`. -/
private lemma dyadic_inj_aux {a₁ a₂ p₁ p₂ : ℕ} (hp₁ : Nat.Prime p₁)
    (hodd₁ : 2 < p₁) (hp₂ : Nat.Prime p₂)
    (h : 2 ^ a₁ * p₁ ^ 2 = 2 ^ a₂ * p₂ ^ 2) :
    a₁ = a₂ ∧ p₁ = p₂ := by
  have hdvd : p₁ ∣ 2 ^ a₂ * p₂ ^ 2 := by
    have h0 : p₁ ∣ 2 ^ a₁ * p₁ ^ 2 :=
      dvd_mul_of_dvd_right (dvd_pow_self p₁ two_ne_zero) _
    rwa [h] at h0
  have hpp : p₁ = p₂ := by
    rcases hp₁.dvd_mul.mp hdvd with hd | hd
    · have h2 : p₁ = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp₁ Nat.prime_two).mp (hp₁.dvd_of_dvd_pow hd)
      omega
    · exact (Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp (hp₁.dvd_of_dvd_pow hd)
  have haa : a₁ = a₂ := by
    have h' : 2 ^ a₁ * p₁ ^ 2 = 2 ^ a₂ * p₁ ^ 2 := by rwa [← hpp] at h
    have h2 : 2 ^ a₁ = 2 ^ a₂ :=
      mul_right_cancel₀ (pow_ne_zero _ hp₁.ne_zero) h'
    exact Nat.pow_right_injective (le_refl 2) h2
  exact ⟨haa, hpp⟩

/-- Extract primality and oddness of the second component from membership in
the dyadic sigma domain. -/
private lemma sigma_fiber_prime {x : ℕ} {σ : Σ _ : ℕ, ℕ}
    (hσ : σ ∈ (Finset.range (Nat.log 2 x + 1)).sigma
      (fun a => (Nat.primesLE (Nat.sqrt (x / 2 ^ a))).filter fun p => 2 < p)) :
    σ.2 ≤ Nat.sqrt (x / 2 ^ σ.1) ∧ Nat.Prime σ.2 ∧ 2 < σ.2 := by
  rw [Finset.mem_sigma, Finset.mem_filter, Nat.mem_primesLE] at hσ
  exact ⟨hσ.2.1.1, hσ.2.1.2, hσ.2.2⟩

/-- Clean pair-count lower bound: the number of pairs `(a, p)` with
`a ≤ Nat.log 2 x`, `p ≤ √x` an odd prime, and `2^a·p² ≤ x` is at most
`badSingletonCount x`, via the injection `(a, p) ↦ 2^a * p^2`. -/
theorem badSingletonCount_ge_dyadicPairs (x : ℕ) :
    (((Finset.range (Nat.log 2 x + 1)) ×ˢ (Nat.primesLE (Nat.sqrt x))).filter
        (fun ap : ℕ × ℕ => 2 < ap.2 ∧ 2 ^ ap.1 * ap.2 ^ 2 ≤ x)).card
      ≤ badSingletonCount x := by
  unfold badSingletonCount
  apply Finset.card_le_card_of_injOn (fun ap : ℕ × ℕ => 2 ^ ap.1 * ap.2 ^ 2)
  · rintro ⟨a, p⟩ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Nat.mem_primesLE] at h
    obtain ⟨⟨-, ⟨-, hpp⟩⟩, hodd, hle⟩ := h
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), ?_⟩)
    exact two_pow_mul_prime_sq_mem_badSingleton hpp hodd
  · rintro ⟨a₁, p₁⟩ h₁ ⟨a₂, p₂⟩ h₂ h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
      Nat.mem_primesLE] at h₁ h₂
    obtain ⟨⟨-, ⟨-, hp₁⟩⟩, hodd₁, -⟩ := h₁
    obtain ⟨⟨-, ⟨-, hp₂⟩⟩, -, -⟩ := h₂
    obtain ⟨haa, hpp⟩ := dyadic_inj_aux hp₁ hodd₁ hp₂ h
    subst haa; subst hpp; rfl

/-- Dyadic-sum lower bound: for every `a ≤ Nat.log 2 x`, each odd prime
`p ≤ √(x/2^a)` contributes the bad singleton `2^a·p² ≤ x`, and these are all
distinct.  Equivalently `∑_{a} #{odd primes p : p² ≤ x/2^a} ≤ badSingletonCount x`. -/
theorem badSingletonCount_ge_oddPrimeSum (x : ℕ) :
    (∑ a ∈ Finset.range (Nat.log 2 x + 1),
      ((Nat.primesLE (Nat.sqrt (x / 2 ^ a))).filter fun p => 2 < p).card)
      ≤ badSingletonCount x := by
  unfold badSingletonCount
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun σ : Σ _ : ℕ, ℕ => 2 ^ σ.1 * σ.2 ^ 2)
  · intro σ hσ
    obtain ⟨hple, hpp, hodd⟩ := sigma_fiber_prime (Finset.mem_coe.mp hσ)
    have hp2 : σ.2 ^ 2 ≤ x / 2 ^ σ.1 := Nat.le_sqrt'.mp hple
    have hx : 2 ^ σ.1 * (x / 2 ^ σ.1) ≤ x := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hle : 2 ^ σ.1 * σ.2 ^ 2 ≤ x :=
      le_trans (Nat.mul_le_mul le_rfl hp2) hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), ?_⟩)
    exact two_pow_mul_prime_sq_mem_badSingleton hpp hodd
  · intro σ hσ τ hτ h
    obtain ⟨-, hp₁, hodd₁⟩ := sigma_fiber_prime (Finset.mem_coe.mp hσ)
    obtain ⟨-, hp₂, -⟩ := sigma_fiber_prime (Finset.mem_coe.mp hτ)
    obtain ⟨haa, hpp⟩ := dyadic_inj_aux hp₁ hodd₁ hp₂ h
    exact Sigma.ext haa (by rw [hpp]; exact HEq.rfl)

/-- `card (primesLE y) - 1 ≤ card {p ∈ primesLE y : 2 < p}`: the only prime
`≤ 2` is `2` itself, so filtering out `p ≤ 2` removes at most one element. -/
private lemma card_primesLE_filter_two_lt (y : ℕ) :
    (Nat.primesLE y).card - 1 ≤
      ((Nat.primesLE y).filter fun p => 2 < p).card := by
  have hneg : ((Nat.primesLE y).filter fun p => ¬ 2 < p).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter, Nat.mem_primesLE] at ha hb
    have ha2 : a = 2 := le_antisymm (by omega) ha.1.2.two_le
    have hb2 : b = 2 := le_antisymm (by omega) hb.1.2.two_le
    rw [ha2, hb2]
  have hsum := Finset.filter_card_add_filter_neg_card_eq_card (Nat.primesLE y)
    (fun p => 2 < p)
  omega

/-- Explicit `primeCounting` form of the dyadic-sum bound:
`∑_{a < log₂ x + 1} (π(√(x/2^a)) - 1) ≤ badSingletonCount x`.  This strictly
improves `Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x` for `x ≥ 4`
(the `a = 1` term contributes `π(√(x/2)) - 1 ≥ 0`, and is positive once
`x ≥ 8`). -/
theorem badSingletonCount_ge_primeCounting_sum (x : ℕ) :
    (∑ a ∈ Finset.range (Nat.log 2 x + 1),
      (Nat.primeCounting (Nat.sqrt (x / 2 ^ a)) - 1)) ≤ badSingletonCount x := by
  refine le_trans ?_ (badSingletonCount_ge_oddPrimeSum x)
  apply Finset.sum_le_sum
  intro a _
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact card_primesLE_filter_two_lt _

/-- For `n ≥ 2`, multiplying by `q^2` with `q` prime, `q ≤ largestPrimeFactor n`,
does not change the largest prime factor. -/
theorem largestPrimeFactor_mul_prime_sq {n q : ℕ} (hn : 2 ≤ n) (hq : Nat.Prime q)
    (hqle : q ≤ largestPrimeFactor n) :
    largestPrimeFactor (n * q ^ 2) = largestPrimeFactor n := by
  have hq2 : 0 < q ^ 2 := pow_pos hq.pos _
  have hm : 2 ≤ n * q ^ 2 := by
    have hle : n ≤ n * q ^ 2 := by
      conv_lhs => rw [← mul_one n]
      exact Nat.mul_le_mul le_rfl hq2
    exact le_trans hn hle
  apply le_antisymm
  · have hPp := largestPrimeFactor_prime hm
    have hPd := largestPrimeFactor_dvd hm
    rcases hPp.dvd_mul.mp hPd with h | h
    · exact prime_dvd_le_largestPrimeFactor hn hPp h
    · have h2 := hPp.dvd_of_dvd_pow h
      have he : largestPrimeFactor (n * q ^ 2) = q :=
        (Nat.prime_dvd_prime_iff_eq hPp hq).mp h2
      omega
  · exact prime_dvd_le_largestPrimeFactor hm (largestPrimeFactor_prime hn)
      (dvd_mul_of_dvd_left (largestPrimeFactor_dvd hn) (q ^ 2))

/-- Stability of bad singletons: if `n` is a bad singleton and `q` is a prime
with `q ≤ largestPrimeFactor n`, then `n * q^2` is again a bad singleton. -/
theorem badSingleton_mul_prime_sq {n q : ℕ} (hn : 1 < n)
    (hdvd : (largestPrimeFactor n) ^ 2 ∣ n) (hq : Nat.Prime q)
    (hqle : q ≤ largestPrimeFactor n) :
    1 < n * q ^ 2 ∧ (largestPrimeFactor (n * q ^ 2)) ^ 2 ∣ n * q ^ 2 := by
  have hq2 : 0 < q ^ 2 := pow_pos hq.pos _
  have hm : 2 ≤ n * q ^ 2 := by
    have hle : n ≤ n * q ^ 2 := by
      conv_lhs => rw [← mul_one n]
      exact Nat.mul_le_mul le_rfl hq2
    exact le_trans hn hle
  refine ⟨hm, ?_⟩
  rw [largestPrimeFactor_mul_prime_sq hn hq hqle]
  exact dvd_mul_of_dvd_left hdvd _

/-- Counting corollary: bad singletons `n ≤ x` with `q ≤ P(n)` inject via
`n ↦ n * q^2` into bad singletons `≤ x * q^2`. -/
theorem badSingletonCount_mul_prime_sq_ge (x q : ℕ) (hq : Nat.Prime q) :
    (((Finset.range (x + 1)).filter fun n =>
        1 < n ∧ (largestPrimeFactor n) ^ 2 ∣ n ∧
          q ≤ largestPrimeFactor n).card)
      ≤ badSingletonCount (x * q ^ 2) := by
  unfold badSingletonCount
  apply Finset.card_le_card_of_injOn (· * q ^ 2)
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, hn1, hdvd, hqle⟩ := hn
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩)
    · have hle : n * q ^ 2 ≤ x * q ^ 2 := Nat.mul_le_mul (by omega) le_rfl
      omega
    · exact badSingleton_mul_prime_sq hn1 hdvd hq hqle
  · intro a _ b _ h
    exact mul_right_cancel₀ (pow_ne_zero _ hq.ne_zero) h

/-- Monotonicity of `badSingletonCount` (private copy; the public version
`badSingletonCount_mono` lives in `JSP314.Counting`). -/
private lemma badSingletonCount_mono_aux : Monotone badSingletonCount := by
  intro x y hxy
  unfold badSingletonCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨by omega, hn.2⟩

/-- `badSingletonCount` is monotone under multiplication by a factor `k ≥ 1`. -/
theorem badSingletonCount_mul_mono (k x : ℕ) (hk : 1 ≤ k) :
    badSingletonCount x ≤ badSingletonCount (k * x) :=
  badSingletonCount_mono_aux (Nat.le_mul_of_pos_left x hk)

/-- Private copy of the prime-squares bound (public version lives in
`JSP314.Counting`). -/
private lemma badSingletonCount_ge_primeCounting_aux (x : ℕ) :
    Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x := by
  unfold badSingletonCount
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p ^ 2)
  · intro p hp
    rw [Finset.mem_coe, Nat.mem_primesLE] at hp
    obtain ⟨hple, hpp⟩ := hp
    have hpsq : p ^ 2 ≤ x := Nat.le_sqrt'.mp hple
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by show p ^ 2 < x + 1; omega), ?_⟩)
    refine ⟨one_lt_pow₀ hpp.one_lt two_ne_zero, ?_⟩
    rw [largestPrimeFactor_prime_sq_self hpp]
  · intro a _ b _ hab
    exact Nat.pow_left_injective two_ne_zero hab

/-- Eventual lower bound: for all sufficiently large `x`,
`π(√x) ≤ badSingletonCount x` (in fact this holds pointwise for every `x`). -/
theorem badSingletonCount_eventually_ge_primeCounting :
    ∀ᶠ x in Filter.atTop,
      Nat.primeCounting (Nat.sqrt x) ≤ badSingletonCount x :=
  Filter.Eventually.of_forall badSingletonCount_ge_primeCounting_aux

end JSP314
