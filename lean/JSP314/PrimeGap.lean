import JSP314.ShortLong
import JSP314.Type2Run
import JSP314.Squeeze
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
# JSP-000314 — long bad intervals live inside prime gaps

Let `[u, v]` be a *long* non-singleton bad interval, i.e. `P ≤ v - u` where
`P = largestPrimeFactor (∏_{i=u}^{v} i)`.  Then:

* `bad_interval_prime_le_of_long`: every prime `i ∈ [u, v]` satisfies
  `i ≤ v - u`, because `i = lpf i ≤ lpf prod = P ≤ v - u`.
* `bad_interval_all_composite_of_long`: every element of `[u, v]` is
  composite — a prime `i ∈ [u, v]` would satisfy `u ≤ i ≤ v - u`, but the
  dyadic squeeze `v + 2 ≤ 2u` gives `v - u < u`.
* `bad_interval_mem_prime_gap_of_long`: `[u, v]` lies strictly inside a gap
  between consecutive primes: taking `q` to be the least prime `> v`
  (Euclid) and `p` the greatest prime `≤ v`, we get `p < u ≤ v < q` with no
  prime strictly between `p` and `q`.
-/

namespace JSP314

/-- In a *long* bad interval (`P ≤ v - u`), every prime member `i` of the
interval satisfies `i ≤ v - u`: indeed `i = lpf i ≤ lpf prod = P ≤ v - u`. -/
theorem bad_interval_prime_le_of_long {u v i : ℕ} (hbad : IsBadInterval u v)
    (hlong : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u)
    (hi : i ∈ Finset.Icc u v) (hp : i.Prime) :
    i ≤ v - u := by
  have hlpf : largestPrimeFactor i = i := by
    rw [largestPrimeFactor_eq_maxPrimeFac hp.two_le, hp.maxPrimeFac_eq_self]
  have hle := bad_interval_forall_lpf_le hbad i hi
  rw [hlpf] at hle
  exact hle.trans hlong

/-- **Every element of a long non-singleton bad interval is composite.**
A prime `i ∈ [u, v]` would satisfy `u ≤ i ≤ v - u` by
`bad_interval_prime_le_of_long`, but the squeeze `v + 2 ≤ 2u` gives
`v - u < u`. -/
theorem bad_interval_all_composite_of_long {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hlong : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u) :
    ∀ i ∈ Finset.Icc u v, ¬ i.Prime := by
  intro i hi hp
  have hle := bad_interval_prime_le_of_long hbad hlong hi hp
  have hsq := bad_interval_v_add_two_le hbad huv
  have hiu : u ≤ i := (Finset.mem_Icc.mp hi).1
  omega

/-- **A long non-singleton bad interval lies inside a consecutive-prime
gap**: there exist primes `p < q` with `p < u` and `v < q` (so
`[u, v] ⊆ (p, q)`) and no prime strictly between `p` and `q`.

Take `q` to be the least prime exceeding `v` — it exists by Euclid
(`Nat.exists_infinite_primes`) — and `p := Nat.findGreatest Nat.Prime v`,
the greatest prime `≤ v` (which is `≥ 2` since `v ≥ 4`).  Minimality of `q`
forces every prime `< q` to be `≤ v`; compositeness of `[u, v]`
(`bad_interval_all_composite_of_long`) then gives `p < u`, and maximality
of `p` excludes primes in `(p, q)`. -/
theorem bad_interval_mem_prime_gap_of_long {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hlong : largestPrimeFactor ((Finset.Icc u v).prod id) ≤ v - u) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < u ∧ v < q ∧
      ∀ r : ℕ, p < r → r < q → ¬ r.Prime := by
  have hcomp := bad_interval_all_composite_of_long hbad huv hlong
  have hsq := bad_interval_v_add_two_le hbad huv
  -- `u ≥ 3` (from `u + 3 ≤ v + 2 ≤ 2u`), hence `v ≥ 4`.
  have hu3 : 3 ≤ u := by omega
  -- `q`: the least prime exceeding `v`.
  obtain ⟨Q, hQge, hQprime⟩ := Nat.exists_infinite_primes (v + 1)
  have hQ : ∃ q : ℕ, v < q ∧ q.Prime := ⟨Q, by omega, hQprime⟩
  obtain ⟨hvq, hqprime⟩ := Nat.find_spec hQ
  -- `p`: the greatest prime `≤ v`.  It is prime since `2 ≤ v`.
  have hpprime : (Nat.findGreatest Nat.Prime v).Prime :=
    Nat.findGreatest_spec (show 2 ≤ v by omega) Nat.prime_two
  have hpv : Nat.findGreatest Nat.Prime v ≤ v := Nat.findGreatest_le v
  -- `p < u`: otherwise `p ∈ [u, v]` would be composite.
  have hpu : Nat.findGreatest Nat.Prime v < u := by
    by_contra hc
    push Not at hc
    exact hcomp _ (Finset.mem_Icc.mpr ⟨hc, hpv⟩) hpprime
  refine ⟨Nat.findGreatest Nat.Prime v, Nat.find hQ,
    hpprime, hqprime, hpu, hvq, ?_⟩
  -- No prime in `(p, q)`: a prime `r < q` satisfies `r ≤ v` (minimality of
  -- `q`), hence `r ≤ p` (maximality of `p`).
  intro r hpr hrq hrr
  have hrv : r ≤ v := by
    by_contra hc
    push Not at hc
    exact Nat.find_min hQ hrq ⟨hc, hrr⟩
  have hrp : r ≤ Nat.findGreatest Nat.Prime v := Nat.le_findGreatest hrv hrr
  omega

end JSP314
