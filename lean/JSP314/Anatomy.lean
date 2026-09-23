import JSP314.ShortLong
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# JSP-000314 — the anatomy of smooth numbers

Elementary "anatomy of integers" input to Tao's argument
(arXiv:2603.27990 §6.4): a `p`-smooth number `r` is, relative to a cutoff
`z`, either *exceptional* — its `z`-rough part has few prime factors — or
else it carries `s` large prime factors `q₁ ≥ ⋯ ≥ qₛ` in `(z, p]`.

## Main definitions

* `roughPart n z`, `smoothPart n z`: the multiplicative split of `n` at the
  cutoff `z`, with `n = roughPart n z * smoothPart n z`
  (`roughPart_mul_smoothPart`), every prime factor of the rough part `> z`
  (`prime_dvd_roughPart`), and the smooth part `(z+1)`-smooth in Mathlib's
  sense (`smoothPart_mem_smoothNumbers`).

## Main results

* `le_pow_cardFactors_of_lpf_le` / `le_pow_factorization_sum_of_lpf_le`:
  a `p`-smooth `r` satisfies `r ≤ p^{Ω r}`.
* `lt_cardFactors_of_pow_lt`: `p`-smooth `r > p^s` has `Ω r > s`.
* `le_lpf_pow_cardFactors`, `le_lpf_rpow_cardFactors`, `rpow_inv_le_lpf`:
  `r ≤ P(r)^{Ω r}` and, if `Ω r ≤ s`, `r^{1/s} ≤ P(r)` over `ℝ`.
* `exists_primeList_mul_smooth`: `r = q₁···qₖ·b` with the `qᵢ` prime in
  `(z, p]`, sorted descending, and `b` `z`-smooth.
* `exists_large_prime_factorization`: if the `z`-rough part has at least
  `s` prime factors counted with multiplicity, `r = q₁···qₛ·c` with `qᵢ`
  prime in `(z, p]`, `q₁ ≥ ⋯ ≥ qₛ`.
* `smooth_dichotomy`: the headline either/or — `s` large prime factors or
  `r = a·b` with `a ≤ p^{s-1}` `z`-rough and `b` `z`-smooth.
* `exceptionalSet_card_le`: the exceptional set
  `{r ≤ y : p-smooth, Ω(roughPart r z) < s}` has cardinality
  `≤ p^{s-1} · Ψ(y, z)` with `Ψ(y, z) = (Nat.smoothNumbersUpTo y (z+1)).card`.
-/

namespace JSP314

open Classical
open scoped ArithmeticFunction.Omega

/-! ### The rough/smooth split -/

/-- The `z`-rough part of `n`: the product of the prime powers `q^{v_q(n)}`
over the prime factors `q > z` of `n`. -/
noncomputable def roughPart (n z : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter fun p => z < p, p ^ n.factorization p

/-- The `z`-smooth part of `n`: the complementary product over the prime
factors `q ≤ z`. -/
noncomputable def smoothPart (n z : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter fun p => ¬ z < p, p ^ n.factorization p

/-- `n` splits as its `z`-rough part times its `z`-smooth part. -/
theorem roughPart_mul_smoothPart {n z : ℕ} (hn : 1 ≤ n) :
    n = roughPart n z * smoothPart n z := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (by omega : n ≠ 0)]
  unfold roughPart smoothPart
  exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

theorem roughPart_dvd {n z : ℕ} (hn : 1 ≤ n) : roughPart n z ∣ n :=
  ⟨smoothPart n z, roughPart_mul_smoothPart hn⟩

theorem smoothPart_dvd {n z : ℕ} (hn : 1 ≤ n) : smoothPart n z ∣ n :=
  ⟨roughPart n z, by rw [mul_comm]; exact roughPart_mul_smoothPart hn⟩

theorem one_le_roughPart (n z : ℕ) : 1 ≤ roughPart n z := by
  unfold roughPart
  apply Finset.one_le_prod
  intro p hp
  exact one_le_pow₀
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt.le

theorem one_le_smoothPart (n z : ℕ) : 1 ≤ smoothPart n z := by
  unfold smoothPart
  apply Finset.one_le_prod
  intro p hp
  exact one_le_pow₀
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).one_lt.le

/-- Every prime divisor of the `z`-rough part exceeds `z`. -/
theorem prime_dvd_roughPart {n z q : ℕ} (hq : q.Prime)
    (hd : q ∣ roughPart n z) : z < q := by
  classical
  unfold roughPart at hd
  obtain ⟨p, hp, hpdvd⟩ := hq.prime.exists_mem_finset_dvd hd
  obtain ⟨hp', hplt⟩ := Finset.mem_filter.mp hp
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hp')).mp
      (hq.dvd_of_dvd_pow hpdvd)
  subst hqp
  exact hplt

/-- Every prime divisor of the `z`-smooth part is `≤ z`. -/
theorem prime_dvd_smoothPart {n z q : ℕ} (hq : q.Prime)
    (hd : q ∣ smoothPart n z) : q ≤ z := by
  classical
  unfold smoothPart at hd
  obtain ⟨p, hp, hpdvd⟩ := hq.prime.exists_mem_finset_dvd hd
  obtain ⟨hp', hplt⟩ := Finset.mem_filter.mp hp
  have hqp : q = p :=
    (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hp')).mp
      (hq.dvd_of_dvd_pow hpdvd)
  subst hqp
  exact le_of_not_gt hplt

/-- The `z`-smooth part is `z`-smooth: it lies in
`Nat.smoothNumbers (z + 1)`. -/
theorem smoothPart_mem_smoothNumbers (n z : ℕ) :
    smoothPart n z ∈ Nat.smoothNumbers (z + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hd
  exact Nat.lt_succ_iff.mpr (prime_dvd_smoothPart hq hd)

/-- A prime divisor of the `z`-rough part of a `p`-smooth `r` is `≤ p`. -/
theorem prime_dvd_roughPart_le {r p z q : ℕ} (hr : 1 ≤ r)
    (hp : largestPrimeFactor r ≤ p) (hq : q.Prime)
    (hd : q ∣ roughPart r z) : q ≤ p := by
  have hdr : q ∣ r := hd.trans (roughPart_dvd hr)
  rcases Nat.lt_or_ge r 2 with h1 | h2
  · have hr1 : r = 1 := by omega
    rw [hr1] at hdr
    exact absurd (Nat.dvd_one.mp hdr) hq.ne_one
  · exact (prime_dvd_le_largestPrimeFactor h2 hq hdr).trans hp

/-! ### Size vs. the number of prime factors `Ω r` -/

/-- If all prime factors of `a` are `≤ p` then `a ≤ p^{Ω a}`: `a` is the
product of its `Ω a` prime factors, each `≤ p`. -/
theorem le_pow_cardFactors_of_forall_prime_dvd_le {a p : ℕ} (ha : 1 ≤ a)
    (h : ∀ q : ℕ, q.Prime → q ∣ a → q ≤ p) :
    a ≤ p ^ Ω a := by
  rcases Nat.lt_or_ge a 2 with h1 | h2
  · have : a = 1 := by omega
    subst this
    simp
  · rw [ArithmeticFunction.cardFactors_apply]
    conv_lhs => rw [← Nat.prod_primeFactorsList (by omega : a ≠ 0)]
    exact List.prod_le_pow_length _ _ fun q hq =>
      h q (Nat.prime_of_mem_primeFactorsList hq)
        (Nat.dvd_of_mem_primeFactorsList hq)

/-- **Size bound for smooth numbers.**  If `r` is `p`-smooth
(`largestPrimeFactor r ≤ p`), then `r ≤ p^{Ω r}` where `Ω r` is the number
of prime factors of `r` counted with multiplicity. -/
theorem le_pow_cardFactors_of_lpf_le {r p : ℕ} (hr : 1 ≤ r)
    (h : largestPrimeFactor r ≤ p) :
    r ≤ p ^ Ω r := by
  rcases Nat.lt_or_ge r 2 with h1 | h2
  · have : r = 1 := by omega
    subst this
    simp
  · apply le_pow_cardFactors_of_forall_prime_dvd_le hr
    intro q hq hd
    exact (prime_dvd_le_largestPrimeFactor h2 hq hd).trans h

/-- The same bound with `Ω r` written as the sum of the factorization. -/
theorem le_pow_factorization_sum_of_lpf_le {r p : ℕ} (hr : 1 ≤ r)
    (h : largestPrimeFactor r ≤ p) :
    r ≤ p ^ (r.factorization.sum fun _ k => k) := by
  rw [← ArithmeticFunction.cardFactors_eq_sum_factorization]
  exact le_pow_cardFactors_of_lpf_le hr h

/-- **Many prime factors.**  A `p`-smooth `r > p^s` has more than `s` prime
factors counted with multiplicity: `s < Ω r`. -/
theorem lt_cardFactors_of_pow_lt {r p s : ℕ} (hr : 2 ≤ r)
    (hp : largestPrimeFactor r ≤ p) (h : p ^ s < r) :
    s < Ω r := by
  have hp2 : 1 < p := (one_lt_largestPrimeFactor hr).trans_le hp
  exact (Nat.pow_lt_pow_iff_right hp2).mp
    (h.trans_le (le_pow_cardFactors_of_lpf_le (by omega) hp))

/-- `r ≤ P(r)^{Ω r}`: a number is at most its largest prime factor raised
to its number of prime factors. -/
theorem le_lpf_pow_cardFactors {r : ℕ} (hr : 1 ≤ r) :
    r ≤ largestPrimeFactor r ^ Ω r :=
  le_pow_cardFactors_of_lpf_le hr le_rfl

/-- If `Ω r ≤ s` then `r ≤ P(r)^s`.  Equivalently, `r > P^s` forces
`Ω r > s`. -/
theorem le_lpf_pow_of_cardFactors_le {r s : ℕ} (hr : 1 ≤ r)
    (h : Ω r ≤ s) : r ≤ largestPrimeFactor r ^ s :=
  (le_lpf_pow_cardFactors hr).trans
    (Nat.pow_le_pow_right (largestPrimeFactor_pos r) h)

/-- The real-valued form: `(r : ℝ) ≤ P(r)^{Ω r}`. -/
theorem le_lpf_rpow_cardFactors {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) ≤ (largestPrimeFactor r : ℝ) ^ (Ω r : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast le_lpf_pow_cardFactors hr

/-- If `Ω r ≤ s` then `r^{1/s} ≤ P(r)`: the largest prime factor is at
least the `s`-th root of `r`. -/
theorem rpow_inv_le_lpf {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : Ω r ≤ s) :
    (r : ℝ) ^ ((1 : ℝ) / s) ≤ largestPrimeFactor r := by
  have hle : (r : ℝ) ≤ (largestPrimeFactor r : ℝ) ^ s := by
    exact_mod_cast le_lpf_pow_of_cardFactors_le hr h
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hstep : (r : ℝ) ^ ((1 : ℝ) / s) ≤
      ((largestPrimeFactor r : ℝ) ^ s) ^ ((1 : ℝ) / s) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    mul_one_div_cancel hs'.ne', Real.rpow_one] at hstep

/-! ### Iterated extraction of large prime factors -/

/-- **Anatomy lemma, list form.**  A `p`-smooth `r ≥ 1` factors as
`r = q₁···qₖ·b` where the `qᵢ` are primes in `(z, p]` — the `z`-rough prime
factors of `r`, counted with multiplicity and listed in decreasing order —
and `b` is `z`-smooth. -/
theorem exists_primeList_mul_smooth {r p z : ℕ} (hr : 1 ≤ r)
    (hp : largestPrimeFactor r ≤ p) :
    ∃ L : List ℕ, ∃ b : ℕ,
      r = L.prod * b ∧ L.SortedGE ∧ L.length = Ω (L.prod) ∧
        (∀ q ∈ L, q.Prime ∧ z < q ∧ q ≤ p) ∧
        (∀ q : ℕ, q.Prime → q ∣ b → q ≤ z) ∧
        b ∈ Nat.smoothNumbers (z + 1) := by
  classical
  have ha1 : 1 ≤ roughPart r z := one_le_roughPart r z
  have hprod : (roughPart r z).primeFactorsList.prod = roughPart r z :=
    Nat.prod_primeFactorsList (by omega)
  refine ⟨(roughPart r z).primeFactorsList.reverse, smoothPart r z,
    ?_, ?_, ?_, ?_, fun q hq hd => prime_dvd_smoothPart hq hd,
    smoothPart_mem_smoothNumbers r z⟩
  · rw [List.prod_reverse, hprod]
    exact roughPart_mul_smoothPart hr
  · exact List.sortedGE_reverse.mpr (Nat.primeFactorsList_sorted _)
  · rw [List.length_reverse]
    rw [ArithmeticFunction.cardFactors_apply]
    congr 1
    rw [List.prod_reverse, hprod]
  · intro q hq
    rw [List.mem_reverse] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hq
    have hd : q ∣ roughPart r z := Nat.dvd_of_mem_primeFactorsList hq
    exact ⟨hqp, prime_dvd_roughPart hqp hd,
      prime_dvd_roughPart_le hr hp hqp hd⟩

/-- **Iterated extraction of large prime factors** (the
`exists_large_prime_factorization` of the anatomy argument).  If `r` is
`p`-smooth and its `z`-rough part has at least `s` prime factors counted
with multiplicity — the "non-exceptional" case — then `r = q₁···qₛ·c` with
`q₁ ≥ ⋯ ≥ qₛ` primes in `(z, p]`. -/
theorem exists_large_prime_factorization {r p z s : ℕ} (hr : 1 ≤ r)
    (hp : largestPrimeFactor r ≤ p) (h : s ≤ Ω (roughPart r z)) :
    ∃ L : List ℕ, ∃ c : ℕ, r = L.prod * c ∧ L.length = s ∧ L.SortedGE ∧
      (∀ q ∈ L, q.Prime ∧ z < q ∧ q ≤ p) := by
  classical
  have ha1 : 1 ≤ roughPart r z := one_le_roughPart r z
  have hprod : (roughPart r z).primeFactorsList.prod = roughPart r z :=
    Nat.prod_primeFactorsList (by omega)
  have hsplit : (roughPart r z).primeFactorsList.reverse.prod =
      ((roughPart r z).primeFactorsList.reverse.take s).prod *
        ((roughPart r z).primeFactorsList.reverse.drop s).prod := by
    conv_lhs => rw [← List.take_append_drop s
      (roughPart r z).primeFactorsList.reverse]
    rw [List.prod_append]
  have hLq : ∀ q ∈ (roughPart r z).primeFactorsList.reverse,
      q.Prime ∧ z < q ∧ q ≤ p := by
    intro q hq
    rw [List.mem_reverse] at hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hq
    have hd : q ∣ roughPart r z := Nat.dvd_of_mem_primeFactorsList hq
    exact ⟨hqp, prime_dvd_roughPart hqp hd,
      prime_dvd_roughPart_le hr hp hqp hd⟩
  have hsrt : (roughPart r z).primeFactorsList.reverse.SortedGE :=
    List.sortedGE_reverse.mpr (Nat.primeFactorsList_sorted _)
  refine ⟨(roughPart r z).primeFactorsList.reverse.take s,
    ((roughPart r z).primeFactorsList.reverse.drop s).prod * smoothPart r z,
    ?_, ?_, ?_, fun q hq => hLq q (List.mem_of_mem_take hq)⟩
  · calc r = roughPart r z * smoothPart r z := roughPart_mul_smoothPart hr
      _ = (roughPart r z).primeFactorsList.prod * smoothPart r z := by
          rw [hprod]
      _ = (roughPart r z).primeFactorsList.reverse.prod * smoothPart r z := by
          rw [List.prod_reverse]
      _ = ((roughPart r z).primeFactorsList.reverse.take s).prod *
            (((roughPart r z).primeFactorsList.reverse.drop s).prod *
              smoothPart r z) := by
          rw [hsplit, mul_assoc]
  · rw [List.length_take, List.length_reverse,
      ← ArithmeticFunction.cardFactors_apply]
    exact min_eq_left h
  · exact List.sortedGE_iff_pairwise.mpr
      (List.Pairwise.sublist (List.take_sublist _ _)
        (List.sortedGE_iff_pairwise.mp hsrt))

/-- **The anatomy dichotomy.**  For a `p`-smooth `r ≥ 1` and a cutoff `z`,
either

* `r = q₁···qₛ·c` with `q₁ ≥ ⋯ ≥ qₛ` primes in `(z, p]` (the generic,
  non-exceptional case), or

* `r = a·b` with `a ≤ p^{s-1}` `z`-rough and `b` `z`-smooth — the
  exceptional case, counted by `exceptionalSet_card_le`. -/
theorem smooth_dichotomy {r p z s : ℕ} (hr : 1 ≤ r)
    (hp : largestPrimeFactor r ≤ p) :
    (∃ L : List ℕ, ∃ c : ℕ, r = L.prod * c ∧ L.length = s ∧ L.SortedGE ∧
        (∀ q ∈ L, q.Prime ∧ z < q ∧ q ≤ p)) ∨
    (∃ a b : ℕ, r = a * b ∧ a ≤ p ^ (s - 1) ∧ 1 ≤ a ∧ 1 ≤ b ∧
        (∀ q : ℕ, q.Prime → q ∣ a → z < q) ∧
        (∀ q : ℕ, q.Prime → q ∣ b → q ≤ z) ∧
        b ∈ Nat.smoothNumbers (z + 1)) := by
  rcases lt_or_ge (Ω (roughPart r z)) s with h | h
  · have ha1 : 1 ≤ roughPart r z := one_le_roughPart r z
    refine Or.inr ⟨roughPart r z, smoothPart r z, roughPart_mul_smoothPart hr,
      ?_, ha1, one_le_smoothPart r z,
      fun q hq hd => prime_dvd_roughPart hq hd,
      fun q hq hd => prime_dvd_smoothPart hq hd,
      smoothPart_mem_smoothNumbers r z⟩
    have hΩ : Ω (roughPart r z) ≤ s - 1 := by omega
    have hp1 : 1 ≤ p := (largestPrimeFactor_pos r).trans hp
    exact (le_pow_cardFactors_of_forall_prime_dvd_le ha1
      fun q hq hd => prime_dvd_roughPart_le hr hp hq hd).trans
        (pow_le_pow_right₀ hp1 hΩ)
  · exact Or.inl (exists_large_prime_factorization hr hp h)

/-- The rough part is bounded below by `z^{Ω}`: since each of its `Ω`
prime factors exceeds `z`, `z^{Ω(roughPart)} < roughPart` whenever the
rough part is nontrivial. -/
theorem pow_cardFactors_lt_roughPart {r z : ℕ} (hr : 1 ≤ r)
    (h : 1 ≤ Ω (roughPart r z)) :
    z ^ Ω (roughPart r z) < roughPart r z := by
  classical
  have ha1 : 1 ≤ roughPart r z := one_le_roughPart r z
  have hprod : (roughPart r z).primeFactorsList.prod = roughPart r z :=
    Nat.prod_primeFactorsList (by omega)
  rw [ArithmeticFunction.cardFactors_apply] at h ⊢
  conv_rhs => rw [← hprod]
  -- `L := (roughPart r z).primeFactorsList`; every `x ∈ L` satisfies `x ≥ z+1`
  set L := (roughPart r z).primeFactorsList with hL
  have hmem : ∀ x ∈ L, z + 1 ≤ x := by
    intro x hx
    have hxp : x.Prime := Nat.prime_of_mem_primeFactorsList hx
    exact (prime_dvd_roughPart hxp (Nat.dvd_of_mem_primeFactorsList hx))
  have hle : ∀ M : List ℕ, (∀ x ∈ M, z + 1 ≤ x) → (z + 1) ^ M.length ≤ M.prod := by
    intro M hM
    induction M with
    | nil => simp
    | cons x t ih =>
      rw [List.length_cons, pow_succ', List.prod_cons]
      exact Nat.mul_le_mul (hM x List.mem_cons_self)
        (ih (fun y hy => hM y (List.mem_cons_of_mem x hy)))
  calc z ^ L.length < (z + 1) ^ L.length :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self z) (by omega)
    _ ≤ L.prod := hle L hmem

/-- Consequently, a rough part with `≥ s` prime factors is large:
`z^s < roughPart r z`. -/
theorem pow_lt_roughPart_of_le_cardFactors {r z s : ℕ} (hr : 1 ≤ r)
    (hs : 1 ≤ s) (h : s ≤ Ω (roughPart r z)) :
    z ^ s < roughPart r z := by
  have hz : z ^ s ≤ z ^ Ω (roughPart r z) := by
    rcases Nat.eq_zero_or_pos z with hz | hz
    · rw [hz] at h ⊢
      rw [zero_pow (show s ≠ 0 by omega)]
      exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hz h
  exact hz.trans_lt (pow_cardFactors_lt_roughPart hr (by omega))

/-! ### The exceptional set and its cardinality -/

/-- The exceptional set: `p`-smooth `r ∈ [1, y]` whose `z`-rough part has
fewer than `s` prime factors counted with multiplicity.  These are the `r`
to which `exists_large_prime_factorization` does not apply. -/
noncomputable def exceptionalSet (y p z s : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    largestPrimeFactor r ≤ p ∧ Ω (roughPart r z) < s

/-- **The exceptional set is small**: its cardinality is at most
`p^{s-1} · Ψ(y, z)` where `Ψ(y, z)` is realised as
`(Nat.smoothNumbersUpTo y (z+1)).card`.  Indeed `r ↦ (a, b)` with `a` the
`z`-rough and `b` the `z`-smooth part is injective (`r = a·b`), `a` ranges
over `[1, p^{s-1}]`, and `b` over the `z`-smooth numbers `≤ y`. -/
theorem exceptionalSet_card_le (y p z s : ℕ) :
    (exceptionalSet y p z s).card ≤
      p ^ (s - 1) * (Nat.smoothNumbersUpTo y (z + 1)).card := by
  classical
  have hsub : (exceptionalSet y p z s).card ≤
      ((Finset.Icc 1 (p ^ (s - 1))) ×ˢ
        (Nat.smoothNumbersUpTo y (z + 1))).card := by
    apply Finset.card_le_card_of_injOn
      (fun r => (roughPart r z, smoothPart r z))
    · intro r hrmem
      obtain ⟨hri, hlp, hΩ⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hrmem)
      obtain ⟨hr1, hry⟩ := Finset.mem_Icc.mp hri
      rw [Finset.mem_coe, Finset.mem_product]
      constructor
      · rw [Finset.mem_Icc]
        refine ⟨one_le_roughPart r z, ?_⟩
        have hΩ' : Ω (roughPart r z) ≤ s - 1 := by omega
        have hp1 : 1 ≤ p := (largestPrimeFactor_pos r).trans hlp
        exact (le_pow_cardFactors_of_forall_prime_dvd_le
          (one_le_roughPart r z)
          fun q hq hd => prime_dvd_roughPart_le hr1 hlp hq hd).trans
            (pow_le_pow_right₀ hp1 hΩ')
      · rw [Nat.mem_smoothNumbersUpTo]
        exact ⟨(Nat.le_of_dvd (by omega) (smoothPart_dvd hr1)).trans hry,
          smoothPart_mem_smoothNumbers r z⟩
    · intro r₁ hr₁ r₂ hr₂ heq
      obtain ⟨hr₁mem, -, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr₁)
      obtain ⟨hr₂mem, -, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hr₂)
      have h₁ : r₁ = roughPart r₁ z * smoothPart r₁ z :=
        roughPart_mul_smoothPart (Finset.mem_Icc.mp hr₁mem).1
      have h₂ : r₂ = roughPart r₂ z * smoothPart r₂ z :=
        roughPart_mul_smoothPart (Finset.mem_Icc.mp hr₂mem).1
      rw [Prod.mk.injEq] at heq
      obtain ⟨he1, he2⟩ := heq
      rw [h₁, h₂, he1, he2]
  rwa [Finset.card_product, Nat.card_Icc,
    show p ^ (s - 1) + 1 - 1 = p ^ (s - 1) by omega] at hsub

end JSP314
