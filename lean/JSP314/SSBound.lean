import JSP314.Assault5
import JSP314.QuadMid
import JSP314.QuadThin
import JSP314.Nagura

/-!
# Boundedness of Sylvester–Schur witness points

The long-bad-interval branch of `badNonSingletonCount` is bounded by the
`ssWitness` count (`badNonSingletonCount_le_short_add_ssWitness` in
`Assault5.lean`).  This file shows that every ssWitness point is bounded by
the *absolute constant* `2·10^16`, so `ssWitnessCount x ≤ 2·10^16 + 1` for
all `x` and the long branch contributes only a constant error.

Recall (`Assault5.ssWitness_quadRegimeOpen`): an ssWitness point `n` lies in a
run `[a, a + L - 1]` of `L`-smooth integers with `L < a` and
`QuadRegimeOpen (a + L - 1) L`, i.e. `38 ≤ L`, `2L + 2 ≤ a + L - 1 ≤ L²`.

Two already-proved inputs cover the whole quadratic regime:

* **Thin band** `a + L - 1 ≤ 3L` (equivalently `a ≤ 2L + 1`): the Nagura-type
  theorem `exists_prime_in_band_of_ge` (a prime in `(x, 3x/2]` for
  `x ≥ 10^16`) supplies, at `x = a - 1`, a prime
  `p ∈ (a - 1, 3(a-1)/2] ⊆ (a - 1, a + L - 1]` — a prime inside the run,
  contradicting the fact that every run element is composite.  Failure
  therefore requires `a - 1 < 10^16`, whence `n ≤ a + L - 1 ≤ 2a - 2`.
  (Routed through `quadRegimeOpen_thin_of_prime_gap` for a uniform
  contradiction shape.)

* **Upper region** `a + L - 1 ≥ 3L` (equivalently `a ≥ 2L + 2`): the Erdős
  iterated-primorial bound `quadRegimeOpen_of_linear` supplies a prime
  `q > L` dividing `C(a + L - 1, L)` whenever `L ≥ 2^26`, again a
  contradiction.  Failure requires `L < 2^26`, whence
  `n ≤ a + L - 1 ≤ L² < 2^52`.

Combining, `ssWitness n → n ≤ 2·10^16`.
-/

namespace JSP314

open SylvesterSchur

/-- A prime `q > L` dividing `C(a + L - 1, L)` contradicts the `L`-smoothness
of the run `[a, a + L - 1]` (for `L < a`): such a prime divides some run
element, forcing `q ≤ largestPrimeFactor ≤ L`. -/
theorem ssWitness_choose_contra {a L : ℕ} (hLa : L < a)
    (hsmooth : ∀ i ∈ Finset.Icc a (a + L - 1), largestPrimeFactor i ≤ L)
    (h : ∃ q, q.Prime ∧ L < q ∧ q ∣ (a + L - 1).choose L) : False := by
  obtain ⟨m, hm, q, hq, hqL, hqm⟩ :=
    SylvesterSchur.exists_prime_mem_Icc_dvd_of_choose (by omega : L ≤ a + L - 1) h
  rw [Finset.mem_Icc] at hm
  have hmem : m ∈ Finset.Icc a (a + L - 1) := Finset.mem_Icc.mpr ⟨by omega, hm.2⟩
  have hle := prime_dvd_le_largestPrimeFactor (by omega : 2 ≤ m) hq hqm
  have hsm := hsmooth m hmem
  omega

/-- Every ssWitness point is at most `2·10^16`.

Case split on the run end `a + L - 1` versus `3L`:
* thin band (`≤ 3L`): Nagura gives a prime inside the run unless
  `a ≤ 10^16`, which bounds `n ≤ 2a - 2 < 2·10^16`.
* upper region (`> 3L`): the linear-range bound gives a large prime divisor
  of `C(a + L - 1, L)` unless `L < 2^26`, which bounds `n ≤ L² < 2^52`. -/
theorem ssWitness_le {n : ℕ} (h : ssWitness n) : n ≤ 2 * 10 ^ 16 := by
  obtain ⟨a, L, hq, hn, hsmooth⟩ := ssWitness_quadRegimeOpen h
  obtain ⟨hL38, h2L2, hLsq⟩ := hq
  have hLa : L < a := by omega
  rw [Finset.mem_Icc] at hn
  rcases le_or_gt (a + L - 1) (3 * L) with hthin | hup
  · -- Thin band: `a ≤ 2L + 1`.
    by_cases hX : 10 ^ 16 ≤ a - 1
    · -- Nagura supplies a prime in `(a - 1, 3(a-1)/2] ⊆ (a - 1, a + L - 1]`.
      exact absurd
        (quadRegimeOpen_thin_of_prime_gap (10 ^ 16) exists_prime_in_band_of_ge
          ⟨hL38, h2L2, hLsq⟩ (n := a + L - 1) (k := L) (by omega) hthin)
        (ssWitness_choose_contra hLa hsmooth)
    · -- `a ≤ 10^16`: then `n ≤ a + L - 1 ≤ 2a - 2 < 2·10^16`.
      have ha : a ≤ 10 ^ 16 := by omega
      omega
  · -- Upper region: `3L < a + L - 1`, i.e. `a ≥ 2L + 2`.
    have h3L : 3 * L ≤ a + L - 1 := by omega
    by_cases hL26 : 2 ^ 26 ≤ L
    · exact absurd
        (quadRegimeOpen_of_linear (a + L - 1) L ⟨hL38, h2L2, hLsq⟩ hL26 h3L)
        (ssWitness_choose_contra hLa hsmooth)
    · -- `L < 2^26`: `n ≤ a + L - 1 ≤ L² < 2^52 < 2·10^16`.
      have hL : L < 2 ^ 26 := by omega
      have hLsq' : L ^ 2 < 2 ^ 52 := by
        calc L ^ 2 ≤ (2 ^ 26 - 1) ^ 2 := by
              apply Nat.pow_le_pow_left; omega
          _ < (2 ^ 26) ^ 2 := by
              apply Nat.pow_lt_pow_left (by norm_num : 2 ^ 26 - 1 < 2 ^ 26)
                (by norm_num)
          _ = 2 ^ 52 := by rw [← pow_mul]
      have : n ≤ 2 ^ 52 := by omega
      omega

/-- The ssWitness count is bounded by the absolute constant `2·10^16 + 1`:
every witness point is `≤ 2·10^16`. -/
theorem ssWitnessCount_le (x : ℕ) : ssWitnessCount x ≤ 2 * 10 ^ 16 + 1 := by
  classical
  unfold ssWitnessCount
  have hsub : (Finset.range (x + 1)).filter (fun n => ssWitness n) ⊆
      Finset.range (2 * 10 ^ 16 + 1) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [Finset.mem_range]
    have := ssWitness_le hm.2
    omega
  calc ((Finset.range (x + 1)).filter fun n => ssWitness n).card
      ≤ (Finset.range (2 * 10 ^ 16 + 1)).card := Finset.card_le_card hsub
    _ = 2 * 10 ^ 16 + 1 := Finset.card_range _

/-- The non-singleton bad-interval count is bounded by the short-interval
count plus the absolute constant `2·10^16 + 1`: the entire long branch
(Sylvester–Schur witnesses) contributes only a constant. -/
theorem badNonSingletonCount_le_short_add_const (x : ℕ) :
    badNonSingletonCount x ≤ shortBadCount x + (2 * 10 ^ 16 + 1) := by
  have h1 := badNonSingletonCount_le_short_add_ssWitness x
  have h2 := ssWitnessCount_le x
  omega

end JSP314
