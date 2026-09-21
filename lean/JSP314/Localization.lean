import JSP314.Defs
import Mathlib

/-!
# JSP-000314 — the localization lemma

Tao's bad-interval argument localizes as follows: if a bad interval `[u, v]`
contains an element `m` divisible by `P²`, where `P` is the largest prime
factor of the interval product `∏_{i ∈ [u,v]} i`, then `m` is itself a
"bad singleton" (`1 < m` and `P(m)² ∣ m`), and every point of `[u, v]` lies
within distance `v - u` of `m`.

* `sq_dvd_mem_largestPrimeFactor_eq`: `P(m) = P(prod)` under the divisibility
  hypothesis (each of `P(m)` and `P(prod)` is a prime divisor of `prod`, so
  they are equal by maximality of `P(prod)` and `P(m)` respectively).
* `sq_dvd_mem_isBadSingleton`: `m` is a bad singleton.
* `dist_le_of_mem_Icc`: two points of `[u, v]` are within `v - u` of each
  other (with truncated natural subtraction).
* `mem_Icc_near_badSingleton`: the combined statement used downstream.
-/

namespace JSP314

/-- Unfolded (zeta-reduced) characterisation of `IsBadInterval`. -/
theorem isBadInterval_iff {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- The core estimate: if `m ∈ [u, v]` is divisible by `P²` with `P` the
largest prime factor of the interval product (and the interval is bad, so `P`
is genuinely prime), then `2 ≤ m` and `P(m) = P`. -/
private theorem two_le_and_lpf_eq_of_sq_dvd_mem {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨huv, hP1, _hP2⟩ := isBadInterval_iff.1 hbad
  -- Since `P ≠ 1`, the product is at least `2` and `P` is genuinely prime.
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  -- `m` divides the product, which is positive, so `m` is positive.
  have hmdvd : m ∣ (Finset.Icc u v).prod id := Finset.dvd_prod_of_mem id hm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h0
    · rw [zero_dvd_iff] at hmdvd; omega
    · exact h0
  -- `m ≥ P² ≥ 2`.
  have hm2 : 2 ≤ m :=
    (one_lt_pow₀ hPprime.one_lt two_ne_zero).le.trans
      (Nat.le_of_dvd hmpos hdvd)
  -- `P ∣ m` since `P ∣ P² ∣ m`.
  have hPdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m :=
    (dvd_pow_self _ two_ne_zero).trans hdvd
  -- `P(m) ≤ P`: `P(m)` is a prime dividing `prod`.
  have hle1 :
      largestPrimeFactor m ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor hprod2 (largestPrimeFactor_prime hm2)
      ((largestPrimeFactor_dvd hm2).trans hmdvd)
  -- `P ≤ P(m)`: `P` is a prime dividing `m`.
  have hle2 :
      largestPrimeFactor ((Finset.Icc u v).prod id) ≤ largestPrimeFactor m :=
    prime_dvd_le_largestPrimeFactor hm2 hPprime hPdvd
  exact ⟨hm2, le_antisymm hle1 hle2⟩

/-- If `m ∈ [u, v]` is divisible by `P²` where `P` is the largest prime factor
of the interval product (and `[u, v]` is bad so `P` is genuinely prime), then
`largestPrimeFactor m = P`. -/
theorem sq_dvd_mem_largestPrimeFactor_eq {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) :=
  (two_le_and_lpf_eq_of_sq_dvd_mem hbad hm hdvd).2

/-- If `m ∈ [u, v]` is divisible by `P²` where `P` is the largest prime factor
of the interval product, then `m` is a bad singleton: `1 < m` and
`P(m)² ∣ m`. -/
theorem sq_dvd_mem_isBadSingleton {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem hbad hm hdvd
  refine ⟨hm2, ?_⟩
  rw [heq]
  exact hdvd

/-- Every point of `[u, v]` is within distance `v - u` of `m ∈ [u, v]`
(truncated natural subtraction). -/
theorem dist_le_of_mem_Icc {u v m n : ℕ}
    (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    n ≤ m + (v - u) ∧ m ≤ n + (v - u) := by
  rw [Finset.mem_Icc] at hm hn
  omega

/-- The combined localization statement: a bad interval containing a `P²`
multiple contains a bad singleton within distance `v - u` of every point of
the interval. -/
theorem mem_Icc_near_badSingleton {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m)
    {n : ℕ} (hn : n ∈ Finset.Icc u v) :
    ∃ m' : ℕ, 1 < m' ∧ largestPrimeFactor m' ^ 2 ∣ m' ∧
      n ≤ m' + (v - u) ∧ m' ≤ n + (v - u) := by
  obtain ⟨h1, h2⟩ := sq_dvd_mem_isBadSingleton hbad hm hdvd
  obtain ⟨h3, h4⟩ := dist_le_of_mem_Icc hm hn
  exact ⟨m, h1, h2, h3, h4⟩

end JSP314
