import JSP314.Defs
import JSP314.Squeeze
import JSP314.Type2Run
import Mathlib.NumberTheory.SmoothNumbers

/-!
# JSP-000314 — the type-2 smoothness containment

Let `[u, v]` be a bad interval (`IsBadInterval u v`) with `u < v`, in the
*type-2* regime: no element of `[u, v]` is divisible by `P²`, where
`P = largestPrimeFactor (∏_{i=u}^{v} i)`.  Then `P ≤ v - u`
(`bad_interval_largestPrimeFactor_le_sub`), and since every prime factor of
every `i ∈ [u, v]` is at most `P`, each element is `(v − u + 1)`-smooth in
Mathlib's sense (`Nat.smoothNumbers`).

Proved here:

* `type2_all_primeFactors_le` — every prime divisor `q` of every
  `i ∈ Finset.Icc u v` satisfies `q ≤ v - u`;
* `type2_mem_smoothNumbers` — `i ∈ Nat.smoothNumbers (v - u + 1)`;
* `type2_mem_smoothNumbersUpTo` — `i ∈ Nat.smoothNumbersUpTo v (v - u + 1)`;
* `type2_two_multiples` — re-export: two distinct elements of `[u, v]` are
  divisible by `P`;
* `type2_length_ge` — `2 ≤ P ≤ v - u`, so the interval has length `≥ 3`;
* `type2_subset_Icc` — `Finset.Icc u v ⊆ Finset.Icc (v / 2 + 1) v`;
* `type2_mem_Icc_and_smooth` — combined containment;
* `type2_card_le_smooth`, `type2_card_le` — the interval's cardinality is at
  most that of the `(v - u + 1)`-smooth numbers up to `v`, hence at most
  `2 ^ #(Nat.primesBelow (v - u + 1)) * v.sqrt` (Mathlib's smooth-number count).
-/

namespace JSP314

/-- In a bad interval, the interval product is at least `2`
(otherwise its largest prime factor would be `1`). -/
theorem bad_interval_prod_ge_two {u v : ℕ} (hbad : IsBadInterval u v) :
    2 ≤ (Finset.Icc u v).prod id := by
  rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
  · exact absurd
      (largestPrimeFactor_eq_one_iff.mpr
        (show (Finset.Icc u v).prod id ≤ 1 by omega))
      hbad.2.1
  · exact h

/-- No element of a bad interval is zero (else the product would vanish). -/
theorem bad_interval_mem_ne_zero {u v i : ℕ} (hbad : IsBadInterval u v)
    (hi : i ∈ Finset.Icc u v) : i ≠ 0 := by
  intro hi0
  have h0 : (Finset.Icc u v).prod id = 0 :=
    Finset.prod_eq_zero hi (by simpa using hi0)
  exact hbad.2.1 (largestPrimeFactor_eq_one_iff.mpr (by omega))

/-- In a bad interval `u ≥ 1`. -/
theorem bad_interval_one_le_u {u v : ℕ} (hbad : IsBadInterval u v) : 1 ≤ u := by
  by_contra hc
  have h0mem : (0 : ℕ) ∈ Finset.Icc u v :=
    Finset.mem_Icc.mpr ⟨Nat.zero_le u, by omega⟩
  have h0 : (Finset.Icc u v).prod id = 0 := Finset.prod_eq_zero h0mem rfl
  exact hbad.2.1 (largestPrimeFactor_eq_one_iff.mpr (by omega))

/-- **(1) Type-2 smoothness.**  In the type-2 regime of a bad interval
`[u, v]`, every prime divisor `q` of every element `i ∈ [u, v]` satisfies
`q ≤ v - u`: `q ≤ largestPrimeFactor i ≤ P ≤ v - u`. -/
theorem type2_all_primeFactors_le {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m))
    {i q : ℕ} (hi : i ∈ Finset.Icc u v) (hq : Nat.Prime q) (hqdvd : q ∣ i) :
    q ≤ v - u := by
  have hi0 : i ≠ 0 := bad_interval_mem_ne_zero hbad hi
  have hi2 : 2 ≤ i :=
    hq.two_le.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hqdvd)
  calc q ≤ largestPrimeFactor i :=
        prime_dvd_le_largestPrimeFactor hi2 hq hqdvd
    _ ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
        bad_interval_forall_lpf_le hbad i hi
    _ ≤ v - u :=
        bad_interval_largestPrimeFactor_le_sub hbad huv hnsq

/-- **(2)** Restated in Mathlib's smooth-number vocabulary: every element of a
type-2 bad interval is `(v - u + 1)`-smooth. -/
theorem type2_mem_smoothNumbers {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m))
    {i : ℕ} (hi : i ∈ Finset.Icc u v) :
    i ∈ Nat.smoothNumbers (v - u + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro q hq hqdvd
  have h := type2_all_primeFactors_le hbad huv hnsq hi hq hqdvd
  omega

/-- Finset version: every element of a type-2 bad interval lies in
`Nat.smoothNumbersUpTo v (v - u + 1)`. -/
theorem type2_mem_smoothNumbersUpTo {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m))
    {i : ℕ} (hi : i ∈ Finset.Icc u v) :
    i ∈ Nat.smoothNumbersUpTo v (v - u + 1) := by
  rw [Nat.mem_smoothNumbersUpTo]
  exact ⟨(Finset.mem_Icc.mp hi).2, type2_mem_smoothNumbers hbad huv hnsq hi⟩

/-- **(3a)** Re-export: in the type-2 regime `P` divides two distinct elements
of `[u, v]` (so the interval contains at least two multiples of `P`). -/
theorem type2_two_multiples {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    ∃ a b : ℕ, a ∈ Finset.Icc u v ∧ b ∈ Finset.Icc u v ∧ a ≠ b ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ a ∧
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ b :=
  bad_interval_two_mul_le_of_no_sq hbad huv hnsq

/-- **(3b)** In the type-2 regime `2 ≤ P ≤ v - u`, so the interval
`[u, v]` has length `v + 1 - u ≥ 3`. -/
theorem type2_length_ge {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    2 ≤ largestPrimeFactor ((Finset.Icc u v).prod id)
      ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u
      ∧ 3 ≤ v + 1 - u := by
  have h2 : 2 ≤ (Finset.Icc u v).prod id := bad_interval_prod_ge_two hbad
  have hP2 : 2 ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    (largestPrimeFactor_prime h2).two_le
  have hPle : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u :=
    bad_interval_largestPrimeFactor_le_sub hbad huv hnsq
  exact ⟨hP2, hPle, by omega⟩

/-- **(3c)** A (non-singleton) bad interval lies in the dyadic window
`(v/2, v]`: every element `i` satisfies `v / 2 < i ≤ v`. -/
theorem type2_subset_Icc {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v) :
    Finset.Icc u v ⊆ Finset.Icc (v / 2 + 1) v := by
  have hsqueeze : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  intro i hi
  rw [Finset.mem_Icc] at hi ⊢
  omega

/-- **(3d)** Combined: each element of a type-2 bad interval lies in
`(v/2, v]` and is `(v - u + 1)`-smooth. -/
theorem type2_mem_Icc_and_smooth {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m))
    {i : ℕ} (hi : i ∈ Finset.Icc u v) :
    i ∈ Finset.Icc (v / 2 + 1) v ∧ i ∈ Nat.smoothNumbers (v - u + 1) :=
  ⟨type2_subset_Icc hbad huv hi, type2_mem_smoothNumbers hbad huv hnsq hi⟩

/-- **(4)** Cardinality bound: a type-2 bad interval is contained in the set of
`(v - u + 1)`-smooth numbers up to `v`, so its size is bounded by the number of
such smooth numbers. -/
theorem type2_card_le_smooth {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    (Finset.Icc u v).card ≤ (Nat.smoothNumbersUpTo v (v - u + 1)).card :=
  Finset.card_le_card (fun i hi ↦ type2_mem_smoothNumbersUpTo hbad huv hnsq hi)

/-- **(4')** Chained with Mathlib's smooth-number count
(`Nat.smoothNumbersUpTo_card_le`): the interval's size is at most
`2 ^ #(Nat.primesBelow (v - u + 1)) * v.sqrt`. -/
theorem type2_card_le {u v : ℕ} (hbad : IsBadInterval u v) (huv : u < v)
    (hnsq : ∀ m ∈ Finset.Icc u v,
      ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) :
    (Finset.Icc u v).card
      ≤ 2 ^ (Nat.primesBelow (v - u + 1)).card * v.sqrt :=
  (type2_card_le_smooth hbad huv hnsq).trans
    (Nat.smoothNumbersUpTo_card_le v (v - u + 1))

end JSP314
