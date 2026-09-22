import Mathlib
import JSP314.Defs

/-!
# JSP-000314 — a finite covering bound for short type-1 bad intervals

Points `n ≤ x` lying in a "short type-1" bad interval — a bad interval
`[u, v]` with `u < v`, of length `v - u ≤ L`, and containing an element `m`
divisible by `P²`, where `P` is the largest prime factor of the interval
product — are within distance `L` of a bad singleton `≤ x + L`.  Counting
the covered points through the covering by the intervals
`[m - L, m + L]` gives

  # covered points ≤ `badSingletonCount (x + L) * (2 * L + 1)`.

The file is self-contained on `JSP314.Defs`: the localization facts
(`sq_dvd_mem_isBadSingleton`, `dist_le_of_mem_Icc` from
`JSP314.Localization`) are re-proved as private helpers so this file does
not depend on modules that may still be compiling.

* `covered_by_short_type1_interval_card_le`: the covering bound.
-/

namespace JSP314

open Classical

/-- If `m ∈ [u, v]` is divisible by `P²` where `P` is the largest prime
factor of the interval product (and `[u, v]` is bad, so `P` is genuinely
prime), then `2 ≤ m` and `largestPrimeFactor m = P`.
(Local copy of the localization estimate from `JSP314.Localization`.) -/
private theorem two_le_and_lpf_eq_of_sq_dvd_mem {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    2 ≤ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) := by
  obtain ⟨_huv, hP1, _hP2⟩ := hbad
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

/-- If `m ∈ [u, v]` is divisible by `P²` where `P` is the largest prime
factor of the interval product, then `m` is a bad singleton:
`1 < m` and `P(m)² ∣ m`. -/
private theorem sq_dvd_mem_isBadSingleton {u v m : ℕ}
    (hbad : IsBadInterval u v) (hm : m ∈ Finset.Icc u v)
    (hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m) :
    1 < m ∧ largestPrimeFactor m ^ 2 ∣ m := by
  obtain ⟨hm2, heq⟩ := two_le_and_lpf_eq_of_sq_dvd_mem hbad hm hdvd
  refine ⟨hm2, ?_⟩
  rw [heq]
  exact hdvd

/-- Every point of `[u, v]` is within distance `v - u` of `m ∈ [u, v]`
(truncated natural subtraction). -/
private theorem dist_le_of_mem_Icc {u v m n : ℕ}
    (hm : m ∈ Finset.Icc u v) (hn : n ∈ Finset.Icc u v) :
    n ≤ m + (v - u) ∧ m ≤ n + (v - u) := by
  rw [Finset.mem_Icc] at hm hn
  omega

/-- Covering bound: the number of `n ≤ x` lying in a bad interval `[u, v]`
with `u < v`, `v - u ≤ L`, and containing a `P²`-multiple (`P` the largest
prime factor of `∏_{i=u}^{v} i`) is at most `S(x + L) · (2L + 1)`, where
`S` is `badSingletonCount`.

Proof: each such `n` is within distance `v - u ≤ L` of `m ∈ [u, v]`, and
`m` is a bad singleton (`sq_dvd_mem_isBadSingleton`) with
`m ≤ n + (v - u) ≤ x + L`.  Hence the counted points are covered by the
intervals `[m - L, m + L]` as `m` ranges over the bad singletons
`≤ x + L`; each such interval has at most `2L + 1` elements, and the union
bound `Finset.card_biUnion_le` gives the claim. -/
theorem covered_by_short_type1_interval_card_le (x L : ℕ) :
    ((Finset.range (x + 1)).filter fun n =>
      ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
        m ∈ Finset.Icc u v ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
        u ≤ n ∧ n ≤ v).card
      ≤ badSingletonCount (x + L) * (2 * L + 1) := by
  set S := (Finset.range (x + L + 1)).filter
    (fun m => 1 < m ∧ largestPrimeFactor m ^ 2 ∣ m) with hS
  -- Each counted `n` lies in `[m - L, m + L]` for a bad singleton
  -- `m ≤ x + L`.
  have hsub : (Finset.range (x + 1)).filter (fun n =>
        ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
          m ∈ Finset.Icc u v ∧
          largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
          u ≤ n ∧ n ≤ v)
      ⊆ S.biUnion (fun m => Finset.Icc (m - L) (m + L)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnx, u, v, m, _huv, hbad, hlen, hm, hdvd, hun, hnv⟩ := hn
    obtain ⟨hm1, hm2⟩ := sq_dvd_mem_isBadSingleton hbad hm hdvd
    have hnIcc : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
    obtain ⟨hd1, hd2⟩ := dist_le_of_mem_Icc hm hnIcc
    rw [Finset.mem_biUnion]
    refine ⟨m, ?_, ?_⟩
    · -- `m ∈ S`: `m ≤ n + (v - u) ≤ x + L`, and `m` is a bad singleton.
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hm1, hm2⟩
    · -- `n ∈ [m - L, m + L]` from `dist_le_of_mem_Icc` and `v - u ≤ L`.
      rw [Finset.mem_Icc]
      omega
  -- Each covering interval has at most `2L + 1` elements.
  have hIcc_card : ∀ m : ℕ, (Finset.Icc (m - L) (m + L)).card ≤ 2 * L + 1 := by
    intro m
    rw [Finset.card_Icc]
    omega
  -- `S.card` is exactly `badSingletonCount (x + L)`.
  have hS_card : S.card = badSingletonCount (x + L) := by
    rw [hS]
    rfl
  calc ((Finset.range (x + 1)).filter fun n =>
          ∃ u v m : ℕ, u < v ∧ IsBadInterval u v ∧ v - u ≤ L ∧
            m ∈ Finset.Icc u v ∧
            largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣ m ∧
            u ≤ n ∧ n ≤ v).card
      ≤ (S.biUnion fun m => Finset.Icc (m - L) (m + L)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ m ∈ S, (Finset.Icc (m - L) (m + L)).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ S, (2 * L + 1) := Finset.sum_le_sum fun m _ => hIcc_card m
    _ = S.card * (2 * L + 1) := Finset.sum_const_nat fun _ _ => rfl
    _ = badSingletonCount (x + L) * (2 * L + 1) := by rw [hS_card]

end JSP314
