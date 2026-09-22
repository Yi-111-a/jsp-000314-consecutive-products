import JSP314.Defs

/-!
# JSP-000314 — structural lemmas for the "long" bad-interval case

A bad interval `[u, v]` with `u < v` is called **long** when it contains *no*
element divisible by `P²`, where `P` is the largest prime factor of the
interval product `prod = ∏_{i=u}^{v} i`.  By the dichotomy
(`JSP314/Dichotomy.lean`, `bad_interval_sq_multiple_or_long`) such intervals
satisfy `P ≤ v - u`; this file develops the elementary structural
consequences of that situation.

This file is intentionally self-contained modulo `JSP314.Defs`: the handful
of auxiliary facts that elsewhere live in `JSP314.ProdLPF` /
`JSP314.Localization` / `JSP314.Dichotomy` are re-derived here as private
lemmas so that the file compiles against the `Defs` oleans alone.

## What is proved

* `lpf_le_of_mem_bad_interval` — every `i ∈ [u, v]` of a bad interval
  satisfies `largestPrimeFactor i ≤ largestPrimeFactor prod`
  (re-export of `ProdLPF.le_largestPrimeFactor_prod` in private form).
* `exists_pair_ne_mem_dvd_lpf_prod_of_long` — a long bad interval contains
  at least **two distinct** multiples of `P`.
* `lpf_prod_le_length_of_long_interval` — `P ≤ v - u` (the "long" branch of
  the dichotomy, re-derived from the two-multiples construction).
* `lpf_le_length_of_mem_long_interval` — every `n ∈ [u, v]` satisfies
  `largestPrimeFactor n ≤ v - u`.
* `lpf_prod_lt_card_of_long_interval` — a long bad interval has strictly
  more than `P` elements: `P < (Icc u v).card`.
* `two_le_card_dvd_of_long_interval` — counting form of the two-multiples
  lemma: the number of elements of `[u, v]` divisible by `P` is `≥ 2`.
* `card_Icc_inter_range_le_filter_lpf_le` — a first counting bound: for any
  `x`, the elements of a long bad interval that are `≤ x` are counted by the
  integers `n ≤ x` with `largestPrimeFactor n ≤ v - u`.

## What remains

The full analytic bound of Ta26c (that points covered by long bad intervals
are `o(badSingletonCount)`-many) requires the covering/sparse-multiples
argument of the paper and is not attempted here; the counting bound above is
only the trivial superset bound.
-/

namespace JSP314

/-- Unfolded (zeta-reduced) characterisation of `IsBadInterval`
(private copy of `Localization.isBadInterval_iff`). -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- The product over a bad interval is at least `2` (since its largest
prime factor is `≠ 1`). -/
private theorem prod_ge_two_of_isBadInterval {u v : ℕ}
    (hbad : IsBadInterval u v) :
    2 ≤ (Finset.Icc u v).prod id := by
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  by_contra h
  push_neg at h
  exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))

/-- A prime dividing a finite product divides one of the factors:
`P(prod)` divides some member of `[u, v]` whenever `2 ≤ prod`
(private copy of `ProdLPF.exists_mem_dvd_of_largestPrimeFactor`). -/
private theorem exists_mem_dvd_of_largestPrimeFactor' {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id :=
    largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- Every `i ∈ [u, v]` has `largestPrimeFactor i ≤ largestPrimeFactor prod`
when `2 ≤ prod` (private copy of `ProdLPF.le_largestPrimeFactor_prod`). -/
private theorem le_largestPrimeFactor_prod' {u v i : ℕ}
    (hi : i ∈ Finset.Icc u v) (h : 2 ≤ (Finset.Icc u v).prod id) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) := by
  rcases le_or_lt i 1 with hi1 | hi1
  · rw [largestPrimeFactor_eq_one_iff.mpr hi1]
    exact (one_lt_largestPrimeFactor h).le
  · have hi2 : 2 ≤ i := hi1
    exact prime_dvd_le_largestPrimeFactor h (largestPrimeFactor_prime hi2)
      ((largestPrimeFactor_dvd hi2).trans (Finset.dvd_prod_of_mem id hi))

/-- **Lemma 1.** Every element `i` of a bad interval `[u, v]` has
`largestPrimeFactor i ≤ P`, where `P = largestPrimeFactor (∏_{j=u}^{v} j)`. -/
theorem lpf_le_of_mem_bad_interval {u v i : ℕ} (hbad : IsBadInterval u v)
    (hi : i ∈ Finset.Icc u v) :
    largestPrimeFactor i ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
  le_largestPrimeFactor_prod' hi (prod_ge_two_of_isBadInterval hbad)

/-- **Lemma 2.** A bad interval `[u, v]` containing no `P²`-multiple contains
at least two *distinct* multiples `m₁ ≠ m₂` of `P`.  This is the
`m₁, m₂` construction of `Dichotomy.bad_interval_sq_multiple_or_long`:
`P ∣ m₁`, and cancelling one factor of `P` from `P² ∣ prod = m₁ · r`
(with `P ∤ a` where `m₁ = P · a`, else `P² ∣ m₁`) forces `P ∣ r`, hence
`P ∣ m₂` for a different element `m₂ ∈ [u, v] \ {m₁}`. -/
theorem exists_pair_ne_mem_dvd_lpf_prod_of_long {u v : ℕ} (_huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    ∃ m1 m2 : ℕ, m1 ∈ Finset.Icc u v ∧ m2 ∈ Finset.Icc u v ∧ m1 ≠ m2 ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 := by
  obtain ⟨-, -, hP2⟩ := isBadInterval_iff'.1 hbad
  have hprod2 := prod_ge_two_of_isBadInterval hbad
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  -- `P` divides some `m₁ ∈ [u, v]`.
  obtain ⟨m1, hm1, hdvd1⟩ := exists_mem_dvd_of_largestPrimeFactor' hprod2
  have hnot1 : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m1 :=
    hnsq m1 hm1
  obtain ⟨a, ha⟩ := hdvd1
  -- `P ∣ a` would force `P² ∣ m₁`.
  have hPa : ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a := by
    rintro ⟨b, hb⟩
    apply hnot1
    exact ⟨b, by rw [ha, hb]; ring⟩
  -- Factor `prod = m₁ * r` where `r` is the product over `[u, v] \ {m₁}`.
  have hprod_eq : (Finset.Icc u v).prod id
      = m1 * ((Finset.Icc u v).erase m1).prod id :=
    (Finset.mul_prod_erase _ _ hm1).symm
  -- `P² ∣ prod = m₁ * r = P * (a * r)`, so `P ∣ a * r` after cancelling.
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2
      ∣ m1 * ((Finset.Icc u v).erase m1).prod id := by
    rw [← hprod_eq]
    exact hP2
  rw [ha, pow_two, mul_assoc] at hdvd
  have hPar : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∣ a * ((Finset.Icc u v).erase m1).prod id :=
    (mul_dvd_mul_iff_left hPprime.ne_zero).mp hdvd
  -- `P` prime and `P ∤ a` give `P ∣ r`.
  have hPr : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∣ ((Finset.Icc u v).erase m1).prod id :=
    (hPprime.dvd_mul.mp hPar).resolve_left hPa
  -- Hence a second, distinct element `m₂ ∈ [u, v]` is divisible by `P`.
  obtain ⟨m2, hm2, hdvd2⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPr
  obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
  exact ⟨m1, m2, hm1, hm2', hne.symm, ⟨a, ha⟩, hdvd2⟩

/-- **Lemma 3a.** The "long" branch of the dichotomy: if the bad interval
`[u, v]` contains no `P²`-multiple then `P ≤ v - u`, because `P` divides the
nonzero difference of the two distinct `P`-multiples found above. -/
theorem lpf_prod_le_length_of_long_interval {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u := by
  obtain ⟨m1, m2, hm1, hm2, hne, hd1, hd2⟩ :=
    exists_pair_ne_mem_dvd_lpf_prod_of_long huv hbad hnsq
  rw [Finset.mem_Icc] at hm1 hm2
  have hd12 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m1 - m2 :=
    Nat.dvd_sub hd1 hd2
  have hd21 : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m2 - m1 :=
    Nat.dvd_sub hd2 hd1
  rcases lt_or_gt_of_ne hne with h | h
  · -- `m1 < m2`, so `P ∣ m2 - m1` with `0 < m2 - m1 ≤ v - u`.
    have hpos : 0 < m2 - m1 := by omega
    have hle := Nat.le_of_dvd hpos hd21
    omega
  · -- `m1 > m2`, so `P ∣ m1 - m2` with `0 < m1 - m2 ≤ v - u`.
    have hpos : 0 < m1 - m2 := by omega
    have hle := Nat.le_of_dvd hpos hd12
    omega

/-- **Lemma 3.** Every `n` lying in a long bad interval `[u, v]` satisfies
`largestPrimeFactor n ≤ v - u` (since `largestPrimeFactor n ≤ P ≤ v - u`). -/
theorem lpf_le_length_of_mem_long_interval {u v n : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)
    (hn : n ∈ Finset.Icc u v) :
    largestPrimeFactor n ≤ v - u :=
  (lpf_le_of_mem_bad_interval hbad hn).trans
    (lpf_prod_le_length_of_long_interval huv hbad hnsq)

/-- A long bad interval has strictly more than `P` elements:
`P < (Finset.Icc u v).card` (since `P ≤ v - u` and `u ≤ v` gives
`(Icc u v).card = v - u + 1`). -/
theorem lpf_prod_lt_card_of_long_interval {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    largestPrimeFactor ((Finset.Icc u v).prod id) < (Finset.Icc u v).card := by
  have hle := lpf_prod_le_length_of_long_interval huv hbad hnsq
  have huv' : u ≤ v := (isBadInterval_iff'.1 hbad).1
  rw [Finset.card_Icc]
  omega

/-- **Counting form of Lemma 2**: the number of elements of the long bad
interval `[u, v]` divisible by `P` is at least `2`. -/
theorem two_le_card_dvd_of_long_interval {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ ((Finset.Icc u v).filter
      (fun m => largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m)).card := by
  obtain ⟨m1, m2, hm1, hm2, hne, hd1, hd2⟩ :=
    exists_pair_ne_mem_dvd_lpf_prod_of_long huv hbad hnsq
  have hsub : ({m1, m2} : Finset ℕ) ⊆
      (Finset.Icc u v).filter
        (fun m => largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m) := by
    intro x hx
    rw [Finset.mem_filter]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hm1, hd1⟩
    · exact ⟨hm2, hd2⟩
  have hcard : ({m1, m2} : Finset ℕ).card = 2 := Finset.card_pair hne
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- **Stretch counting bound.**  For a long bad interval `[u, v]` and any
threshold `x`, the elements of the interval lying at or below `x` are
counted by the integers `n ≤ x` with `largestPrimeFactor n ≤ v - u`:
each element of a long interval has largest prime factor at most the
interval's length defect `v - u`. -/
theorem card_Icc_inter_range_le_filter_lpf_le {u v x : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    ((Finset.Icc u v) ∩ (Finset.range (x + 1))).card ≤
      ((Finset.range (x + 1)).filter
        (fun n => largestPrimeFactor n ≤ v - u)).card := by
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_inter] at hn
  rw [Finset.mem_filter]
  exact ⟨hn.2, lpf_le_length_of_mem_long_interval huv hbad hnsq hn.1⟩

end JSP314
