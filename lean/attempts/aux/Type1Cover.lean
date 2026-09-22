import JSP314.Defs
import JSP314.Squeeze
import JSP314.Type2Run
import Mathlib.Tactic.Push

/-!
# JSP-000314 — the "type-1" cover

Type-1 branch of the dichotomy for a bad interval `[u, v]`: writing
`prod := ∏_{i ∈ [u, v]} i` and `P := largestPrimeFactor prod`, some element
`m ∈ [u, v]` is divisible by `P²`.  Then:

* `m` is itself a **bad singleton**: `1 < m` and `P(m)² ∣ m`.  Indeed
  `P ∣ m` forces `P ≤ P(m)`, while `P(m) ≤ P` holds for every element of a
  bad interval, so `P(m) = P`.
* Because a non-singleton bad interval satisfies `v + 2 ≤ 2u`, every covered
  point `n ∈ [u, v]` satisfies `n ≤ m + (m - 2)` and `m ≤ n + (n - 2)`:
  covered points lie within distance `< m` of a bad singleton `m` with
  `m ≤ 2n` and `n ≤ 2m`.

Lemmas proved here:

* `bad_interval_sq_dvd_or_not` — the type-1/type-2 case split as plain
  excluded middle.
* `sq_dvd_mem_is_bad_singleton` — a `P²`-multiple in a bad interval is a bad
  singleton.
* `type1_dist_le`, `type1_dist_le_abs` — two points of `[u, v]` differ by at
  most `v - u`.
* `type1_window` — the window estimate `n ≤ m + (m - 2) ∧ m ≤ n + (n - 2)`.
* `type1_cover` — the combined statement: every `n` in a type-1 bad interval
  is covered by a bad singleton `m` with `n ≤ m + (m - 2)` and
  `m ≤ n + (n - 2)`.
-/

namespace JSP314

/-- The type-1/type-2 dichotomy as a plain excluded middle: either some
element of `[u, v]` is divisible by `P²` (where `P` is the largest prime
factor of the interval product), or none is. -/
theorem bad_interval_sq_dvd_or_not {u v : ℕ} (_hbad : IsBadInterval u v) :
    (∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) ∨
      (∀ m ∈ Finset.Icc u v,
        ¬ (largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)) := by
  rcases em (∃ m ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) with h | h
  · exact Or.inl h
  · push_neg at h
    exact Or.inr h

/-- If `m ∈ [u, v]` is divisible by `P²`, where `P` is the largest prime
factor of the interval product (and `[u, v]` is bad, so `P` is genuinely
prime), then `m` is a bad singleton: `1 < m` and `P(m)² ∣ m`.

Proof: `P² ∣ m` gives `m ≥ P² ≥ 2` and `P ∣ m`, hence `P ≤ P(m)` by
maximality of `P(m)` among the prime factors of `m`.  On the other hand
`P(m) ≤ P` since `m` divides the interval product
(`bad_interval_forall_lpf_le`).  So `P(m) = P` and `P(m)² = P² ∣ m`. -/
theorem sq_dvd_mem_is_bad_singleton {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m := by
  obtain ⟨_huv, hP1, _hP2⟩ := hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    rcases Nat.lt_or_ge ((Finset.Icc u v).prod id) 2 with h | h
    · exact absurd
        (largestPrimeFactor_eq_one_iff.mpr
          (show (Finset.Icc u v).prod id ≤ 1 by omega))
        hP1
    · exact h
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  -- `m` divides the (positive) interval product, so `m` is positive.
  have hmdvd : m ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [zero_dvd_iff] at hmdvd; omega
    · exact h0
  -- `m ≥ P² ≥ 2`, so `P(m)` is a genuine prime.
  have hm2 : 2 ≤ m :=
    (one_lt_pow₀ hPprime.one_lt two_ne_zero).trans_le
      (Nat.le_of_dvd hmpos hdvd)
  -- `P ∣ m` since `P ∣ P² ∣ m`; maximality of `P(m)` gives `P ≤ P(m)`.
  have hPdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
    (dvd_pow_self _ two_ne_zero).trans hdvd
  have hle2 :
      largestPrimeFactor ((Finset.Icc u v).prod id) ≤ largestPrimeFactor m :=
    prime_dvd_le_largestPrimeFactor hm2 hPprime hPdvd
  -- `P(m) ≤ P`: every element of a bad interval has `P(·) ≤ P`.
  have hle1 :
      largestPrimeFactor m ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    bad_interval_forall_lpf_le hbad m hm
  have heq :
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) :=
    le_antisymm hle1 hle2
  refine ⟨hm2, ?_⟩
  rw [heq]
  exact hdvd

/-- Two points of `[u, v]` differ by at most `v - u` (truncated natural
subtraction, both directions). -/
theorem type1_dist_le {u v n m : ℕ}
    (hn : n ∈ Finset.Icc u v) (hm : m ∈ Finset.Icc u v) :
    n - m ≤ v - u ∧ m - n ≤ v - u := by
  rw [Finset.mem_Icc] at hn hm
  omega

/-- Two points of `[u, v]` differ by at most `v - u` (integer absolute
value). -/
theorem type1_dist_le_abs {u v n m : ℕ}
    (hn : n ∈ Finset.Icc u v) (hm : m ∈ Finset.Icc u v) :
    |(n : ℤ) - (m : ℤ)| ≤ (v : ℤ) - (u : ℤ) := by
  rw [Finset.mem_Icc] at hn hm
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> omega

/-- The type-1 window estimate: in a non-singleton bad interval `[u, v]`,
every covered point `n` and the `P²`-multiple `m` satisfy
`n ≤ m + (m - 2)` and `m ≤ n + (n - 2)`.  This is just
`v + 2 ≤ 2u` (`bad_interval_v_add_two_le`) combined with `u ≤ m, n ≤ v`:
`n ≤ v ≤ 2u - 2 ≤ m + (m - 2)` and symmetrically. -/
theorem type1_window {u v m n : ℕ}
    (hbad : IsBadInterval u v) (huv : u < v)
    (hm : m ∈ Finset.Icc u v)
    (_hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)
    (hn : n ∈ Finset.Icc u v) :
    n ≤ m + (m - 2) ∧ m ≤ n + (n - 2) := by
  have h2u : v + 2 ≤ 2 * u := bad_interval_v_add_two_le hbad huv
  rw [Finset.mem_Icc] at hm hn
  omega

/-- The combined type-1 cover statement: every point `n` of a type-1 bad
interval `[u, v]` (i.e. `u < v` and some `m ∈ [u, v]` is divisible by `P²`)
is covered by a bad singleton `m` with `n ≤ m + (m - 2)` and
`m ≤ n + (n - 2)`. -/
theorem type1_cover {u v n : ℕ}
    (hbad : IsBadInterval u v) (huv : u < v)
    (ht1 : ∃ m ∈ Finset.Icc u v,
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)
    (hn : n ∈ Finset.Icc u v) :
    ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
      n ≤ m + (m - 2) ∧ m ≤ n + (n - 2) := by
  obtain ⟨m, hm, hdvd⟩ := ht1
  obtain ⟨hm1, hm2⟩ := sq_dvd_mem_is_bad_singleton hbad hm hdvd
  obtain ⟨h3, h4⟩ := type1_window hbad huv hm hdvd hn
  exact ⟨m, hm1, hm2, h3, h4⟩

end JSP314
