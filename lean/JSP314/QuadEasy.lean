import JSP314.QuadRegime
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Sqrt

/-!
# The large-`n` part of the quadratic regime

This file discharges the *large* `n` portion of the residual quadratic regime
`QuadRegimeOpen n k` (that is, `38 ≤ k` and `2 * k + 2 ≤ n ≤ k ^ 2`) of the
Sylvester–Schur theorem, shrinking the residual estimate needed downstream.

## The bound

If every prime divisor of `C(n,k)` is at most `k`, then

    C(n,k) = ∏_{p ≤ k} p^{a_p} ≤ n^{π(√n)} · 4 ^ k

(`choose_le_pow_primeCounting_sqrt_mul_four_pow`): each `p ≤ √n` contributes
`p^{a_p} ≤ n` (`Nat.pow_factorization_choose_le`, in the form
`p ^ p.log n ≤ n`), and there are only `π(√n)` such primes; each `p > √n`
occurs with multiplicity `a_p ≤ 1` (`Nat.factorization_choose_le_one`), so
those primes contribute at most the primorial `∏_{p ≤ k} p ≤ 4 ^ k`
(`primorial_le_four_pow`).

Together with `n ^ k ≤ k ^ k · C(n,k)` (`pow_le_pow_mul_choose`), the
Sylvester–Schur conclusion follows as soon as
`k ^ k · 4 ^ k · n ^ {π(√n)} < n ^ k`
(`exists_prime_dvd_choose_of_smooth_sqrt`).

## What is closed

* `quadRegimeOpen_of_sqrt_sieve`: using the mod-6 sieve
  `π(x) ≤ x / 3 + 3` (`primeCounting_le_div_three`), the strict inequality
  `(4k) ^ k · n ^ (√n / 3 + 3) < n ^ k` suffices.  This is the sharpest
  elementary condition here; numerically it already covers `n ≥ k ^ {3/2}`
  once `k` is moderately large (about `k ≥ 105`), and more generally covers
  `n` beyond roughly `(4k) ^ {k / (k - √n / 3 - 3)}`.
* `quadRegimeOpen_of_sqrt_sieve_thirty`: the same with the mod-30 sieve
  `π(x) ≤ 4x / 15 + 10` for `√n ≥ 30` — slightly sharper when `n` is large.
* `quadRegimeOpen_of_large`: the clean *monotone-in-`n`* condition
  `(64 · k³) ^ k < n ^ {2k - 9}` (from `√n ≤ k`).  Inside `n ≤ k²` this is
  non-vacuous exactly when `(64k³) ^ k < (k²) ^ {2k - 9}`, i.e.
  `64 ^ k < k ^ {k - 18}`, which first holds at `k = 128`
  (`64 ^ 128 = 2 ^ {768} < 2 ^ {770} = 128 ^ {110}`) and then for all larger
  `k` since the ratio grows by a factor `≥ k + 1 ≥ 64` at each step
  (`sixtyfour_pow_lt_pow_sub_eighteen`).  Asymptotically the threshold is
  `n > (64k³) ^ {k / (2k - 9)} ≈ 8 · k ^ {3/2} · k ^ {o(1)}`.
* `quadRegimeOpen_of_large_cubic`: the fully explicit range
  `400 · k³ ≤ n²` (i.e. `n ≥ 20 · k ^ {3/2}`), non-vacuous for `k ≥ 400`.

## Remaining residual

After this file the open part of the quadratic regime is

    38 ≤ k,  2k + 2 ≤ n ≤ k²,  (4k) ^ k · n ^ (√n / 3 + 3) ≥ n ^ k

— concretely, for each `k` a bounded initial segment `n ≲ 8 · k ^ {3/2}` (for
large `k`; for `38 ≤ k ≤ 127` the elementary bound does not reach `n = k²` and
the whole regime stays open).  This complements
`quadRegimeOpen_of_smooth_prod_lt` in `JSP314.QuadRegime`, which packages the
sharper Erdős iterated-primorial estimate needed for the small-`n` end.

No placeholder tactics; kernel-checkable.
-/

namespace SylvesterSchur

open Finset
open scoped Nat

/-- For `p > √n` the multiplicity of `p` in `C(n,k)` is at most one —
`Nat.factorization_choose_le_one` applied to `n < p²`, which is what
`Nat.sqrt n < p` means (`Nat.sqrt_lt'`). -/
theorem factorization_choose_le_one_of_sqrt_lt {n k p : ℕ} (hp : Nat.sqrt n < p) :
    (n.choose k).factorization p ≤ 1 :=
  Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp hp)

/-- **Squarefree-tail bound.** If every prime divisor of `C(n,k)` is at most
`k`, then `C(n,k) ≤ n ^ {π(√n)} · 4 ^ k`. -/
theorem choose_le_pow_primeCounting_sqrt_mul_four_pow {n k : ℕ} (hn : 0 < n)
    (hkn : k ≤ n) (h : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k) :
    n.choose k ≤ n ^ (Nat.sqrt n).primeCounting * 4 ^ k := by
  refine (choose_le_prod_pow_log hkn h).trans ?_
  rw [← Finset.prod_filter_mul_prod_filter_not k.primesLE
    (fun p ↦ p ≤ Nat.sqrt n) (fun p ↦ p ^ p.log n)]
  have hcard : ((k.primesLE).filter (fun p ↦ p ≤ Nat.sqrt n)).card ≤
      (Nat.sqrt n).primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    refine Finset.card_le_card fun p hp ↦ ?_
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.2, (Nat.mem_primesLE.mp hp.1).2⟩
  have hsmall : (∏ p ∈ (k.primesLE).filter (fun p ↦ p ≤ Nat.sqrt n), p ^ p.log n)
      ≤ n ^ (Nat.sqrt n).primeCounting := by
    calc ∏ p ∈ (k.primesLE).filter (fun p ↦ p ≤ Nat.sqrt n), p ^ p.log n
        ≤ ∏ _p ∈ (k.primesLE).filter (fun p ↦ p ≤ Nat.sqrt n), n :=
          Finset.prod_le_prod fun p _ ↦ Nat.pow_log_le_self p hn.ne'
      _ = n ^ ((k.primesLE).filter (fun p ↦ p ≤ Nat.sqrt n)).card := by
          rw [Finset.prod_const]
      _ ≤ n ^ (Nat.sqrt n).primeCounting := Nat.pow_le_pow_right hn hcard
  have hlarge : (∏ p ∈ (k.primesLE).filter (fun p ↦ ¬ p ≤ Nat.sqrt n),
        p ^ p.log n) ≤ 4 ^ k := by
    calc ∏ p ∈ (k.primesLE).filter (fun p ↦ ¬ p ≤ Nat.sqrt n), p ^ p.log n
        ≤ ∏ p ∈ (k.primesLE).filter (fun p ↦ ¬ p ≤ Nat.sqrt n), p := by
          refine Finset.prod_le_prod fun p hp ↦ ?_
          rw [Finset.mem_filter] at hp
          have hpp := (Nat.mem_primesLE.mp hp.1).2
          have hlog : p.log n ≤ 1 := by
            have h2 : p.log n < 2 := by
              rw [Nat.log_lt_iff_lt_pow hpp.one_lt hn.ne']
              exact Nat.sqrt_lt'.mp (lt_of_not_ge hp.2)
            omega
          calc p ^ p.log n ≤ p ^ 1 := Nat.pow_le_pow_right hpp.pos hlog
            _ = p := pow_one p
      _ ≤ ∏ p ∈ k.primesLE, p :=
          Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
            fun p hp _ ↦ (Nat.mem_primesLE.mp hp).2.one_lt.le
      _ = primorial k := (primorial_eq_prod_primesLE k).symm
      _ ≤ 4 ^ k := primorial_le_four_pow k
  exact Nat.mul_le_mul hsmall hlarge

/-- **Conditional Sylvester–Schur, sqrt-split form.**  If
`k ^ k · 4 ^ k · n ^ {π(√n)} < n ^ k` then `C(n,k)` has a prime divisor
`> k`. -/
theorem exists_prime_dvd_choose_of_smooth_sqrt {n k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n)
    (hlt : k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting < n ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ q : ℕ, q.Prime → q ∣ n.choose k → q ≤ k :=
    fun q hq hqd ↦ le_of_not_gt fun h2 ↦ hcon q hq h2 hqd
  have hlb := pow_le_pow_mul_choose hkn
  have hub := choose_le_pow_primeCounting_sqrt_mul_four_pow (by omega) hkn hall
  have h : n ^ k ≤ k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting := by
    calc n ^ k ≤ k ^ k * n.choose k := hlb
      _ ≤ k ^ k * (n ^ (Nat.sqrt n).primeCounting * 4 ^ k) :=
          Nat.mul_le_mul_left _ hub
      _ = k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting := by ring
  exact absurd (h.trans_lt hlt) (lt_irrefl _)

/-- **Large-`n` quadratic regime, sieve form.**  Via the mod-6 sieve
`π(x) ≤ x / 3 + 3`, the strict inequality
`(4k) ^ k · n ^ (√n / 3 + 3) < n ^ k` gives the Sylvester–Schur conclusion. -/
theorem quadRegimeOpen_of_sqrt_sieve {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hlt : (4 * k) ^ k * n ^ (Nat.sqrt n / 3 + 3) < n ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h1 := hq.1
  have h2 := hq.2.1
  have hn0 : 0 < n := by omega
  have h6 : 6 ≤ Nat.sqrt n :=
    Nat.le_sqrt'.mpr (by show (36 : ℕ) ≤ n; omega)
  have hπ : (Nat.sqrt n).primeCounting ≤ Nat.sqrt n / 3 + 3 :=
    primeCounting_le_div_three h6
  have hbound : k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting
      ≤ (4 * k) ^ k * n ^ (Nat.sqrt n / 3 + 3) := by
    have hpow : n ^ (Nat.sqrt n).primeCounting ≤ n ^ (Nat.sqrt n / 3 + 3) :=
      Nat.pow_le_pow_right hn0 hπ
    calc k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting
        ≤ k ^ k * 4 ^ k * n ^ (Nat.sqrt n / 3 + 3) := Nat.mul_le_mul_left _ hpow
      _ = (4 * k) ^ k * n ^ (Nat.sqrt n / 3 + 3) := by rw [mul_pow]; ring
  exact exists_prime_dvd_choose_of_smooth_sqrt (by omega) (by omega)
    (hbound.trans_lt hlt)

/-- **Large-`n` quadratic regime, mod-30 sieve form.**  For `n ≥ 900` (so
`√n ≥ 30`) the sharper sieve `π(x) ≤ 4x / 15 + 10` applies, and
`(4k) ^ k · n ^ (4√n / 15 + 10) < n ^ k` suffices. -/
theorem quadRegimeOpen_of_sqrt_sieve_thirty {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hn : 900 ≤ n)
    (hlt : (4 * k) ^ k * n ^ (4 * (Nat.sqrt n) / 15 + 10) < n ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h1 := hq.1
  have h2 := hq.2.1
  have hn0 : 0 < n := by omega
  have h30 : 30 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hn
  have hπ : (Nat.sqrt n).primeCounting ≤ 4 * (Nat.sqrt n) / 15 + 10 :=
    primeCounting_le_four_fifteenths h30
  have hbound : k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting
      ≤ (4 * k) ^ k * n ^ (4 * (Nat.sqrt n) / 15 + 10) := by
    have hpow : n ^ (Nat.sqrt n).primeCounting
        ≤ n ^ (4 * (Nat.sqrt n) / 15 + 10) := Nat.pow_le_pow_right hn0 hπ
    calc k ^ k * 4 ^ k * n ^ (Nat.sqrt n).primeCounting
        ≤ k ^ k * 4 ^ k * n ^ (4 * (Nat.sqrt n) / 15 + 10) :=
          Nat.mul_le_mul_left _ hpow
      _ = (4 * k) ^ k * n ^ (4 * (Nat.sqrt n) / 15 + 10) := by
          rw [mul_pow]; ring
  exact exists_prime_dvd_choose_of_smooth_sqrt (by omega) (by omega)
    (hbound.trans_lt hlt)

/-- **Large-`n` quadratic regime, clean form.**  The elementary monotone
condition `(64 · k³) ^ k < n ^ {2k - 9}` — equivalently
`n > (64k³) ^ {k / (2k - 9)}`, roughly `n > 8 · k ^ {3/2}` for large `k` —
gives the Sylvester–Schur conclusion.  In the regime `n ≤ k²` this is
non-vacuous once `64 ^ k < k ^ {k - 18}`, i.e. for `k ≥ 128`. -/
theorem quadRegimeOpen_of_large {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hlarge : (64 * k ^ 3) ^ k < n ^ (2 * k - 9)) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h1 := hq.1
  have h2 := hq.2.1
  have h22 := hq.2.2
  have hn0 : 0 < n := by omega
  have hsqrt : Nat.sqrt n ≤ k := by
    rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
    calc n ≤ k ^ 2 := h22
      _ = k * k := by rw [pow_two]
      _ < (k + 1) * (k + 1) :=
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self k) (by omega)).trans
            (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self k) (Nat.succ_pos k))
  refine quadRegimeOpen_of_sqrt_sieve hq ?_
  have hexp : Nat.sqrt n / 3 + 3 ≤ k / 3 + 3 := by omega
  suffices h : (4 * k) ^ k * n ^ (k / 3 + 3) < n ^ k from
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn0 hexp)).trans_lt h
  -- Cube both sides: it is enough that `A³ < (n^k)³ = n^{3k}`.
  have hA : ((4 * k) ^ k * n ^ (k / 3 + 3)) ^ 3 ≤ (64 * k ^ 3) ^ k * n ^ (k + 9) := by
    have e1 : ((4 * k) ^ k) ^ 3 = (64 * k ^ 3) ^ k := by
      rw [← pow_mul, mul_comm k 3, pow_mul]
      congr 1
      ring
    have e2 : (n ^ (k / 3 + 3)) ^ 3 ≤ n ^ (k + 9) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right hn0 (by omega)
    calc ((4 * k) ^ k * n ^ (k / 3 + 3)) ^ 3
        = ((4 * k) ^ k) ^ 3 * (n ^ (k / 3 + 3)) ^ 3 := mul_pow _ _ _
      _ ≤ (64 * k ^ 3) ^ k * n ^ (k + 9) := by
          rw [e1]
          exact Nat.mul_le_mul_left _ e2
  have hB : (64 * k ^ 3) ^ k * n ^ (k + 9) < n ^ (3 * k) := by
    have hmul : (64 * k ^ 3) ^ k * n ^ (k + 9) < n ^ (2 * k - 9) * n ^ (k + 9) :=
      Nat.mul_lt_mul_of_pos_right hlarge (pow_pos hn0 _)
    have hexp2 : 2 * k - 9 + (k + 9) = 3 * k := by omega
    rwa [← pow_add, hexp2] at hmul
  by_contra hc
  push Not at hc
  have hcube : n ^ (3 * k) ≤ ((4 * k) ^ k * n ^ (k / 3 + 3)) ^ 3 := by
    have h := Nat.pow_le_pow_left hc 3
    rwa [← pow_mul, mul_comm k 3] at h
  exact absurd (hcube.trans_lt (hA.trans_lt hB)) (lt_irrefl _)

/-- Auxiliary elementary estimate used in `quadRegimeOpen_of_large_cubic`:
for `m ≥ 10`, `(m + 1) ^ 18 ≤ 6 · m ^ 18` (since `(11/10) ^ 18 < 6`). -/
theorem pow_succ_le_six_mul_pow_eighteen {m : ℕ} (hm : 10 ≤ m) :
    (m + 1) ^ 18 ≤ 6 * m ^ 18 := by
  have h10 : 10 * (m + 1) ≤ 11 * m := by omega
  have h2 := Nat.pow_le_pow_left h10 18
  rw [mul_pow, mul_pow] at h2
  have h3 : (11 : ℕ) ^ 18 ≤ 6 * 10 ^ 18 := by norm_num
  have h4 : 11 ^ 18 * m ^ 18 ≤ 10 ^ 18 * (6 * m ^ 18) := by
    calc 11 ^ 18 * m ^ 18 ≤ (6 * 10 ^ 18) * m ^ 18 := Nat.mul_le_mul_right _ h3
      _ = 10 ^ 18 * (6 * m ^ 18) := by ring
  exact Nat.le_of_mul_le_mul_left (h2.trans h4) (by norm_num)

/-- For `k ≥ 38`, `k ^ 18 ≤ 6 ^ k` (base `38 ^ 18 = (38⁹)² ≤ (6¹⁹)² = 6³⁸`,
then each step multiplies the left side by `≤ 6`). -/
theorem pow_eighteen_le_six_pow {k : ℕ} (hk : 38 ≤ k) : k ^ 18 ≤ 6 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
      have h : (38 : ℕ) ^ 9 ≤ 6 ^ 19 := by norm_num
      have h2 := Nat.pow_le_pow_left h 2
      rwa [← pow_mul, ← pow_mul] at h2
  | succ k hk ih =>
      calc (k + 1) ^ 18 ≤ 6 * k ^ 18 := pow_succ_le_six_mul_pow_eighteen (by omega)
        _ ≤ 6 * 6 ^ k := Nat.mul_le_mul_left _ ih
        _ = 6 ^ (k + 1) := (pow_succ' 6 k).symm

/-- The top of the regime is non-vacuously covered once `k ≥ 128`:
`64 ^ k < k ^ {k - 18}` (it first holds at `k = 128`, where
`64 ^ {128} = 2 ^ {768} < 2 ^ {770} = 128 ^ {110}`, and each step multiplies
the left side by `64` while the right side grows by a factor `> k ≥ 128`). -/
theorem sixtyfour_pow_lt_pow_sub_eighteen {k : ℕ} (hk : 128 ≤ k) :
    64 ^ k < k ^ (k - 18) := by
  induction k, hk using Nat.le_induction with
  | base =>
      calc (64 : ℕ) ^ 128 = (2 ^ 6) ^ 128 := by
            rw [show (64 : ℕ) = 2 ^ 6 by norm_num]
        _ = 2 ^ 768 := by rw [← pow_mul]
        _ < 2 ^ 770 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
        _ = (2 ^ 7) ^ 110 := by rw [← pow_mul]
        _ = (128 : ℕ) ^ 110 := by rw [show (128 : ℕ) = 2 ^ 7 by norm_num]
  | succ k hk ih =>
      calc 64 ^ (k + 1) = 64 * 64 ^ k := pow_succ' 64 k
        _ < 64 * k ^ (k - 18) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ ≤ (k + 1) * k ^ (k - 18) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ (k + 1) * (k + 1) ^ (k - 18) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) _)
        _ = (k + 1) ^ (k + 1 - 18) := by
            have e : k + 1 - 18 = (k - 18) + 1 := by omega
            rw [e, pow_succ']

/-- **Explicit closed range.**  For `400 · k³ ≤ n²` (i.e. `n ≥ 20·k^{3/2}`)
in the quadratic regime — possible only for `k ≥ 400` — the Sylvester–Schur
conclusion holds. -/
theorem quadRegimeOpen_of_large_cubic {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hlarge : 400 * k ^ 3 ≤ n ^ 2) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h1 := hq.1
  have h2 := hq.2.1
  have h22 := hq.2.2
  have hn0 : 0 < n := by omega
  apply quadRegimeOpen_of_large hq
  have h9 : n ^ 9 ≤ k ^ 18 := by
    calc n ^ 9 ≤ (k ^ 2) ^ 9 := Nat.pow_le_pow_left h22 9
      _ = k ^ 18 := by rw [← pow_mul]
  have h49 : 4 ^ k * n ^ 9 < 25 ^ k := by
    calc 4 ^ k * n ^ 9 ≤ 4 ^ k * k ^ 18 := Nat.mul_le_mul_left _ h9
      _ ≤ 4 ^ k * 6 ^ k := Nat.mul_le_mul_left _ (pow_eighteen_le_six_pow h1)
      _ = 24 ^ k := (mul_pow 4 6 k).symm
      _ < 25 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega : k ≠ 0)
  have hstep : (64 * k ^ 3) ^ k * n ^ 9 < n ^ (2 * k) := by
    have e3 : (64 : ℕ) ^ k = 16 ^ k * 4 ^ k := mul_pow 16 4 k
    have e4 : (400 : ℕ) ^ k = 16 ^ k * 25 ^ k := mul_pow 16 25 k
    have hpos : 0 < (k ^ 3) ^ k := pow_pos (pow_pos (by omega) 3) k
    calc (64 * k ^ 3) ^ k * n ^ 9
        = 64 ^ k * (k ^ 3) ^ k * n ^ 9 := by rw [mul_pow]
      _ = (k ^ 3) ^ k * (16 ^ k * (4 ^ k * n ^ 9)) := by rw [e3]; ring
      _ < (k ^ 3) ^ k * (16 ^ k * 25 ^ k) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_pos_left h49 (pow_pos (by norm_num) k)) hpos
      _ = (400 * k ^ 3) ^ k := by rw [← e4, mul_pow, mul_comm]
      _ ≤ (n ^ 2) ^ k := Nat.pow_le_pow_left hlarge k
      _ = n ^ (2 * k) := by rw [← pow_mul]
  -- cancel the common factor `n ^ 9`
  have e9 : 2 * k - 9 + 9 = 2 * k := by omega
  rw [← e9, pow_add] at hstep
  exact (Nat.mul_lt_mul_right (pow_pos hn0 9)).mp hstep

end SylvesterSchur
