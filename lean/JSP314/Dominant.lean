import JSP314.ShortLong

/-!
# JSP-000314 — the dominant bad singleton of a short bad interval

In a *short* non-singleton bad interval `[u, v]` (i.e. `v - u < P`, where
`P = largestPrimeFactor (∏ i ∈ [u, v], i)`), the `P²`-multiple `m` furnished by
`bad_interval_sq_multiple_of_short` is *dominant*: it is a bad singleton whose
largest prime factor attains `P`, and every other element of the interval is
strictly smoother.  Indeed, if `i ≠ m` also had largest prime factor `P`, then
`P` would divide two distinct elements of the interval, hence divide their
positive difference, which is at most `v - u < P` — a contradiction.

This file proves:

* `short_bad_interval_dominant`: existence and uniqueness-in-`P` of the
  dominant bad singleton in a short bad interval;
* `shortBadCovered_dominant`: every point `n ≤ x` covered by a short bad
  interval has a dominant bad singleton `m ≤ 2x` within distance `< lpf m`,
  with `n` itself (and every point strictly between `n` and `m`) strictly
  smoother than `m`.
-/

namespace JSP314

open Classical

/-- In a short bad interval, the `P²`-multiple `m` is dominant: it is a bad
singleton with `largestPrimeFactor m = P`, and every other element `i` of the
interval satisfies `largestPrimeFactor i < P`. -/
theorem short_bad_interval_dominant {u v : ℕ} (hbad : IsBadInterval u v)
    (huv : u < v)
    (hshort : v - u < largestPrimeFactor ((Finset.Icc u v).prod id)) :
    ∃ m ∈ Finset.Icc u v, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧
      largestPrimeFactor m = largestPrimeFactor ((Finset.Icc u v).prod id) ∧
      ∀ i ∈ Finset.Icc u v, i ≠ m →
        largestPrimeFactor i < largestPrimeFactor m := by
  obtain ⟨m, hm, hdvd⟩ := bad_interval_sq_multiple_of_short hbad huv hshort
  have hlpf : largestPrimeFactor m =
      largestPrimeFactor ((Finset.Icc u v).prod id) :=
    sq_dvd_mem_lpf_eq hbad hm hdvd
  have hbs := sq_dvd_mem_is_bad_singleton' hbad hm hdvd
  refine ⟨m, hm, hbs.1, hbs.2, hlpf, fun i hi hne => ?_⟩
  have hle : largestPrimeFactor i ≤ largestPrimeFactor m := by
    rw [hlpf]
    exact bad_interval_forall_lpf_le hbad i hi
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    -- If `lpf i = lpf m = P`, then `P` divides both `i` and `m`, hence their
    -- positive difference, which is at most `v - u < P`.
    have hP2 : 2 ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
      (bad_interval_P_prime hbad).two_le
    have hi2 : 2 ≤ i := by
      rcases Nat.lt_or_ge i 2 with h1 | h1
      · exfalso
        have e1 : largestPrimeFactor i = 1 :=
          largestPrimeFactor_eq_one_iff.mpr (by omega)
        rw [e1, hlpf] at heq
        omega
      · exact h1
    have hPi : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ i := by
      have h := largestPrimeFactor_dvd hi2
      rwa [heq, hlpf] at h
    have hPm : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
      have h := largestPrimeFactor_dvd (show 2 ≤ m by omega)
      rwa [hlpf] at h
    have hiu := (Finset.mem_Icc.mp hi).1
    have hiv := (Finset.mem_Icc.mp hi).2
    have hmu := (Finset.mem_Icc.mp hm).1
    have hmv := (Finset.mem_Icc.mp hm).2
    rcases le_total i m with h | h
    · have hpos : 0 < m - i := by omega
      have hd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m - i :=
        Nat.dvd_sub hPm hPi
      have hle2 := Nat.le_of_dvd hpos hd
      omega
    · have hpos : 0 < i - m := by omega
      have hd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣ i - m :=
        Nat.dvd_sub hPi hPm
      have hle2 := Nat.le_of_dvd hpos hd
      omega

/-- Every point `n ≤ x` covered by a short bad interval has a dominant bad
singleton `m ≤ 2x` within distance `< lpf m`; `n` (unless equal to `m`) and
every point strictly between `n` and `m` are strictly smoother than `m`. -/
theorem shortBadCovered_dominant {n x : ℕ} (hn : InShortBadInterval n)
    (hx : n ≤ x) :
    ∃ m : ℕ, 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m ∧ m ≤ 2 * x ∧
      (n ≠ m → largestPrimeFactor n < largestPrimeFactor m) ∧
      (∀ i ∈ Finset.Icc (min n m) (max n m), i ≠ m →
        largestPrimeFactor i < largestPrimeFactor m) ∧
      n ≤ m + largestPrimeFactor m ∧ m ≤ n + largestPrimeFactor m := by
  obtain ⟨u, v, huv, hbad, hun, hnv, hshort⟩ := hn
  obtain ⟨m, hm, hm1, hmsq, hlpf, hdom⟩ :=
    short_bad_interval_dominant hbad huv hshort
  have hnmem : n ∈ Finset.Icc u v := Finset.mem_Icc.mpr ⟨hun, hnv⟩
  have hmu : u ≤ m := (Finset.mem_Icc.mp hm).1
  have hmv : m ≤ v := (Finset.mem_Icc.mp hm).2
  have hv2 : v ≤ 2 * n := bad_interval_v_le_two_mul hbad huv hun hnv
  obtain ⟨h1, h2⟩ := mem_Icc_cover hnmem hm
  refine ⟨m, hm1, hmsq, by omega, fun hne => hdom n hnmem hne, ?_,
    by omega, by omega⟩
  intro i hi hne
  have hiI := Finset.mem_Icc.mp hi
  refine hdom i (Finset.mem_Icc.mpr ⟨?_, ?_⟩) hne <;> omega

end JSP314
