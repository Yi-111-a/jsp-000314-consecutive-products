/-
# Sylvester–Schur theorem (formalization for JSP-000314)

Target statement (downstream need for the Erdős–Graham/Tao problem, see
`JSP314.ShortLong.bad_interval_short_of_sylvesterSchur`):

  among any `L` consecutive integers `a, …, a + L - 1` with `L < a`,
  one of them is divisible by a prime `p > L`.

The equivalent binomial-coefficient form (Erdős 1934): for `n ≥ 2k`,
`C(n, k)` has a prime divisor `> k`.

## Status of this file

Everything below compiles with kernel `decide` only (no native-code decide, so no
`Lean.ofReduceBool` axiom).  The theorem is proved in *all* cases except the
genuinely hard "quadratic regime"

    38 ≤ k   ∧   2 * k + 2 ≤ n ≤ k ^ 2,

which needs Erdős's §§2–4 analysis: the Chebyshev `ψ`-type bound
`C(n,k) ≤ ∏_j (n^{1/j})# ≤ 4^{k + O(√n)}` (iterated dyadic covering of `(1, n]`
by intervals `(a_i, 2a_i]`), the refined lower bounds `C(n,k) ≥ 8^k / (2k)` for
`n ≥ 4k`, and a finite verification for the remaining small `n` (`n ≤ 2304`).

The residual regime is packaged as the predicate `QuadRegimeOpen` and supplied
as an explicit hypothesis `hquad` to the main theorems, so the file contains no
unproved assumptions and the full Sylvester–Schur theorem follows immediately
once `hquad` is discharged.

## What is proved here

* `pow_le_pow_mul_choose`: the lower bound `n ^ k ≤ k ^ k * C(n,k)`
  (i.e. `(n / k) ^ k ≤ C(n,k)`, phrased division-free).
* `choose_le_pow_primeCounting`: Erdős's lemma — if every prime divisor of
  `C(n,k)` is `≤ k` then `C(n,k) ≤ n ^ π(k)`, using Mathlib's valuation bound
  `Nat.pow_factorization_choose_le : p ^ (C(n,k)).factorization p ≤ n`.
* `choose_le_prod_pow_log`: the sharper §2 bound — under the same hypothesis,
  `C(n,k) ≤ ∏ p ∈ primesLE k, p ^ p.log n` (the product over primes `≤ k` of
  the largest `p`-power `≤ n`), the first step of Erdős's iterated-primorial
  estimate.
* `pow_sub_le_of_forall_prime_le`: combining the two bounds,
  `n ^ (k - π k) ≤ k ^ k`.
* `primeCounting_le_div_three`, `primeCounting_le_four_fifteenths`: the sieve
  bounds `π k ≤ k/3 + 3` (for `k ≥ 6`) and `π k ≤ 4k/15 + 10` (for `k ≥ 30`),
  obtained from `Nat.primeCounting_add_le` with moduli `6` and `30`.
* `exists_prime_dvd_choose_of_le`: the case `n ≤ 2 * k + 1` via Bertrand's
  postulate.
* `exists_prime_dvd_choose_of_sq_lt`: the case `k ^ 2 < n` whenever
  `2 * π k ≤ k` (proved for `8 ≤ k` via the mod-6 sieve).
* `check_small` / `check_mid`: *kernel-decided* finite verification of the
  statement "some prime `q > k` satisfies `n % q < k`" (equivalently, `q` has a
  multiple in `(n - k, n]`) for `n ≤ 93`, `k ≤ 7` and for `8 ≤ k ≤ 37`,
  `n ≤ 210`.  Evaluation uses an explicit list `primeList210` of primes
  `≤ 210`, so the kernel only ever performs `Nat` comparisons and `%`.
* `exists_prime_dvd_choose`: the Sylvester–Schur conclusion in the `choose`
  form, conditional on the quadratic-regime hypothesis.
* `exists_prime_mem_Icc_dvd` and `sylvesterSchur`: transfer to the
  consecutive-integers formulation used downstream (the body of
  `JSP314.SylvesterSchur a L`).
-/

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial

namespace SylvesterSchur

open Finset
open scoped Nat

/-!
### Transfer: a prime `p > k` divides `C(n,k)` iff it divides some `m ∈ (n - k, n]`
-/

/-- If a prime `p > k` divides some `m` in the "top interval" `(n - k, n]`,
then `p ∣ n.choose k`. The reason: `n.choose k` equals the product of the `k`
consecutive factors `n - k + 1, …, n` divided by `k !`, and `p ∤ k !`. -/
theorem dvd_choose_of_prime_dvd {n k m p : ℕ} (hp : p.Prime) (hk : k < p)
    (hm : m ∈ Finset.Icc (n + 1 - k) n) (hd : p ∣ m) : p ∣ n.choose k := by
  rw [Finset.mem_Icc] at hm
  rcases lt_or_ge n k with hnk | hkn
  · rw [Nat.choose_eq_zero_of_lt hnk]
    exact dvd_zero p
  · have hdvd : m ∣ n.descFactorial k := by
      rw [Nat.descFactorial_eq_prod_range]
      have hi : n - m ∈ Finset.range k := Finset.mem_range.2 (by omega)
      have hmi : n - (n - m) = m := Nat.sub_sub_self hm.2
      rw [← hmi]
      exact Finset.dvd_prod_of_mem (fun i => n - i) hi
    have hd2 : p ∣ k ! * n.choose k :=
      Nat.descFactorial_eq_factorial_mul_choose n k ▸ hd.trans hdvd
    exact (hp.coprime_factorial_of_lt hk).dvd_of_dvd_mul_left hd2

/-- Conversely, if a prime `p > k` divides `n.choose k`, it divides one of the top
factors `m ∈ (n - k, n]` — the Sylvester–Schur statement is equivalent to
"every `k` consecutive integers `> k` contain one with a prime factor `> k`". -/
theorem exists_mem_Icc_of_prime_dvd_choose {n k p : ℕ} (hp : p.Prime) (hk : k < p)
    (hkn : k ≤ n) (hd : p ∣ n.choose k) :
    ∃ m ∈ Finset.Icc (n + 1 - k) n, p ∣ m := by
  have hdp : p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact hd.mul_left _
  rw [Nat.descFactorial_eq_prod_range] at hdp
  obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdp
  rw [Finset.mem_range] at hi
  exact ⟨n - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpi⟩

/-- A prime `q > k` with `n % q < k` has the multiple `n - n % q` in `(n-k, n]`,
so it divides `C(n,k)`.  This is the computational form used for the finite
verifications below. -/
theorem prime_dvd_choose_of_mod_lt {n k q : ℕ} (hq : q.Prime) (hkq : k < q)
    (hkn : k ≤ n) (hmod : n % q < k) : q ∣ n.choose k := by
  have hmem : n - n % q ∈ Finset.Icc (n + 1 - k) n := by
    have h1 : n % q ≤ k - 1 := by omega
    have h2 : n % q ≤ n := Nat.mod_le _ _
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hdvd : q ∣ n - n % q := by
    have h := Nat.div_add_mod n q
    exact ⟨n / q, by omega⟩
  exact dvd_choose_of_prime_dvd hq hkq hmem hdvd

/-!
### The Bertrand cases `n ≤ 2k + 1` (and `n = 2k + 2` when `k + 2` is composite)
-/

/-- Sylvester–Schur for `2k ≤ n ≤ 2k + 1`: Bertrand's postulate supplies a prime
`p ∈ (n - k, n]`, which is itself one of the top factors and satisfies `p > k`. -/
theorem exists_prime_dvd_choose_of_le {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k ≤ n)
    (hn : n ≤ 2 * k + 1) : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨p, hp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (n - k) (by omega)
  have hpn : p ≤ n := by
    rcases (show p ≤ n + 1 by omega).eq_or_lt with h1 | h1
    · -- `p = n + 1`: then `n + 1 ≤ 2 (n - k)`, so `n = 2k + 1` and `p = 2k + 2`,
      -- an even number `> 2`, contradicting primality.
      exfalso
      have hnn : n = 2 * k + 1 := by omega
      rcases hp.eq_two_or_odd' with h2 | ⟨j, hj⟩
      · omega
      · omega
    · omega
  exact ⟨p, hp, by omega, hp.dvd_choose (by omega) (by omega) hpn⟩

/-- Sylvester–Schur for `n = 2k + 2` whenever `k + 2` is composite:
Bertrand's postulate at `k + 1` then yields a prime in `(k + 2, 2k + 2]`. -/
theorem exists_prime_dvd_choose_of_eq {n k : ℕ} (hk : 1 ≤ k) (hn : n = 2 * k + 2)
    (hcomp : ¬ (k + 2).Prime) : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨p, hp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (k + 1) (by omega)
  have hpne : p ≠ k + 2 := fun h2 => hcomp (h2 ▸ hp)
  subst hn
  exact ⟨p, hp, by omega, hp.dvd_choose (by omega) (by omega) (by omega)⟩

/-!
### The lower bound `(n / k) ^ k ≤ C(n,k)`
-/

/-- `n ^ k ≤ k ^ k * C(n,k)`: the division-free form of `(n / k) ^ k ≤ C(n,k)`.
Each of the `k` factors `(n - i) / (k - i)` of `C(n,k)` is `≥ n / k`. -/
theorem pow_le_pow_mul_choose {n k : ℕ} (hkn : k ≤ n) :
    n ^ k ≤ k ^ k * n.choose k := by
  have hfactor : ∀ i ∈ Finset.range k, n * (k - i) ≤ k * (n - i) := by
    intro i _
    have h' : k * i ≤ n * i := mul_le_mul_left hkn i
    calc n * (k - i) = n * k - n * i := Nat.mul_sub _ _ _
      _ = k * n - n * i := by rw [Nat.mul_comm n k]
      _ ≤ k * n - k * i := Nat.sub_le_sub_left h' _
      _ = k * (n - i) := (Nat.mul_sub _ _ _).symm
  have h1 : k ^ k * n.descFactorial k = ∏ i ∈ Finset.range k, k * (n - i) := by
    rw [Nat.descFactorial_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
  have h3 : ∏ i ∈ Finset.range k, n * (k - i) = n ^ k * k ! := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]
  have h4 : n ^ k * k ! ≤ (k ^ k * n.choose k) * k ! := by
    calc n ^ k * k ! = ∏ i ∈ Finset.range k, n * (k - i) := h3.symm
      _ ≤ ∏ i ∈ Finset.range k, k * (n - i) :=
          Finset.prod_le_prod hfactor
      _ = k ^ k * n.descFactorial k := h1.symm
      _ = (k ^ k * n.choose k) * k ! := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
  exact le_of_mul_le_mul_right h4 (Nat.factorial_pos k)

/-!
### Erdős's lemmas: `C(n,k)` with only small prime factors is small
-/

/-- If every prime divisor of `C(n,k)` is at most `k`, then `C(n,k) ≤ n ^ π(k)`:
the factorization `C(n,k) = ∏ p ^ a_p` ranges over primes `≤ k` (there are `π k`
of them) and each factor satisfies `p ^ a_p ≤ n` by `Nat.pow_factorization_choose_le`. -/
theorem choose_le_pow_primeCounting {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (h : ∀ q, q.Prime → q ∣ n.choose k → q ≤ k) :
    n.choose k ≤ n ^ k.primeCounting := by
  calc n.choose k = ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p :=
        (Nat.prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ k.primesLE, p ^ (n.choose k).factorization p := by
        refine (Finset.prod_subset ?_ ?_).symm
        · intro p hp
          rw [Nat.mem_primesLE] at hp
          exact Finset.mem_range.2 (by omega)
        · intro p _ hp2
          by_cases ha : (n.choose k).factorization p = 0
          · simp [ha]
          · exfalso
            have hpprime : p.Prime := by
              by_contra hnp
              exact ha (Nat.factorization_eq_zero_of_not_prime _ hnp)
            exact hp2 (Nat.mem_primesLE.mpr
              ⟨h p hpprime (Nat.dvd_of_factorization_pos ha), hpprime⟩)
    _ ≤ ∏ p ∈ k.primesLE, n :=
        Finset.prod_le_prod (fun i _ => Nat.pow_factorization_choose_le hn)
    _ = n ^ k.primeCounting := by
        rw [Finset.prod_const, Nat.primesLE_card_eq_primeCounting]

/-- Erdős's sharper §2 bound: under the same hypothesis,
`C(n,k) ≤ ∏ p ∈ primesLE k, p ^ p.log n`, since
`(C(n,k)).factorization p ≤ Nat.log p n`
(`Nat.factorization_choose_le_log`).  This is the product of the prime powers
`p^a ≤ n` over `p ≤ k` — equivalently `∏_{j ≥ 1} (min k ⌊n^{1/j}⌋)#`, which
Erdős bounds by `4^{k + O(√n)}` in the quadratic regime via the Chebyshev `ψ`
function. -/
theorem choose_le_prod_pow_log {n k : ℕ} (hkn : k ≤ n)
    (h : ∀ q, q.Prime → q ∣ n.choose k → q ≤ k) :
    n.choose k ≤ ∏ p ∈ k.primesLE, p ^ p.log n := by
  calc n.choose k = ∏ p ∈ Finset.range (n + 1), p ^ (n.choose k).factorization p :=
        (Nat.prod_pow_factorization_choose n k hkn).symm
    _ = ∏ p ∈ k.primesLE, p ^ (n.choose k).factorization p := by
        refine (Finset.prod_subset ?_ ?_).symm
        · intro p hp
          rw [Nat.mem_primesLE] at hp
          exact Finset.mem_range.2 (by omega)
        · intro p _ hp2
          by_cases ha : (n.choose k).factorization p = 0
          · simp [ha]
          · exfalso
            have hpprime : p.Prime := by
              by_contra hnp
              exact ha (Nat.factorization_eq_zero_of_not_prime _ hnp)
            exact hp2 (Nat.mem_primesLE.mpr
              ⟨h p hpprime (Nat.dvd_of_factorization_pos ha), hpprime⟩)
    _ ≤ ∏ p ∈ k.primesLE, p ^ p.log n :=
        Finset.prod_le_prod (fun p hp => Nat.pow_le_pow_right
          (Nat.mem_primesLE.mp hp).2.one_lt.le Nat.factorization_choose_le_log)

/-- The reduced form of the "no large prime factor" hypothesis:
`n ^ (k - π k) ≤ k ^ k`. -/
theorem pow_sub_le_of_forall_prime_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (h : ∀ q, q.Prime → q ∣ n.choose k → q ≤ k) :
    n ^ (k - k.primeCounting) ≤ k ^ k := by
  have hn0 : 0 < n := by omega
  have hπk : k.primeCounting ≤ k := by
    have hcard := Finset.card_le_card (s := k.primesLE) (t := Finset.Icc 2 k) (by
      intro p hp
      rw [Nat.mem_primesLE] at hp
      exact Finset.mem_Icc.mpr ⟨hp.2.two_le, hp.1⟩)
    rw [Nat.primesLE_card_eq_primeCounting, Nat.card_Icc] at hcard
    omega
  have hc := choose_le_pow_primeCounting hn0 hkn h
  have hb := pow_le_pow_mul_choose hkn
  have e : k - k.primeCounting + k.primeCounting = k := Nat.sub_add_cancel hπk
  have h2 : n ^ (k - k.primeCounting) * n ^ k.primeCounting ≤
      k ^ k * n ^ k.primeCounting := by
    rw [← pow_add, e]
    exact hb.trans (mul_le_mul_right hc _)
  exact le_of_mul_le_mul_right h2 (pow_pos hn0 _)

/-- If `n ^ e ≤ C < B ^ e` with `e > 0`, then `n < B`, i.e. `n ≤ B - 1`. -/
theorem lt_of_pow_le {n e C B : ℕ} (he : 0 < e) (h : n ^ e ≤ C) (hB : C < B ^ e) :
    n ≤ B - 1 := by
  by_contra hn
  push_neg at hn
  have hBn : B ≤ n := by omega
  have : B ^ e ≤ n ^ e := Nat.pow_le_pow_left hBn _
  omega

/-- For `k ≥ 8`, `2 * π k ≤ k` (mod-6 sieve via `Nat.primeCounting_add_le`,
with `8 ≤ k ≤ 17` verified directly). -/
theorem two_mul_primeCounting_le {k : ℕ} (hk : 8 ≤ k) : 2 * k.primeCounting ≤ k := by
  rcases lt_or_ge k 18 with h | h
  · interval_cases k <;> decide
  · have h6 := Nat.primeCounting_add_le (a := 6) (k := 6) (n := k - 6)
        (by decide) (by decide)
    rw [show (6 : ℕ) + (k - 6) = k by omega] at h6
    have hπ : Nat.primeCounting 6 = 3 := by decide
    have ht : Nat.totient 6 = 2 := by decide
    rw [hπ, ht] at h6
    omega

/-- Sharper sieve bound: `π k ≤ k / 3 + 3` for `k ≥ 6` — among any six
consecutive integers at most `φ(6) = 2` are prime. -/
theorem primeCounting_le_div_three {k : ℕ} (hk : 6 ≤ k) :
    k.primeCounting ≤ k / 3 + 3 := by
  have h6 := Nat.primeCounting_add_le (a := 6) (k := 6) (n := k - 6)
      (by decide) (by decide)
  rw [show (6 : ℕ) + (k - 6) = k by omega] at h6
  have hπ : Nat.primeCounting 6 = 3 := by decide
  have ht : Nat.totient 6 = 2 := by decide
  rw [hπ, ht] at h6
  omega

/-- Still sharper for larger `k`: `π k ≤ 4 * k / 15 + 10` for `k ≥ 30` —
among any thirty consecutive integers at most `φ(30) = 8` are prime. -/
theorem primeCounting_le_four_fifteenths {k : ℕ} (hk : 30 ≤ k) :
    k.primeCounting ≤ 4 * k / 15 + 10 := by
  have h30 := Nat.primeCounting_add_le (a := 30) (k := 30) (n := k - 30)
      (by decide) (by decide)
  rw [show (30 : ℕ) + (k - 30) = k by omega] at h30
  have hπ : Nat.primeCounting 30 = 10 := by decide
  have ht : Nat.totient 30 = 8 := by decide
  rw [hπ, ht] at h30
  omega

/-- For `k ≤ 7`, the bound `n ^ (k - π k) ≤ k ^ k` forces `n ≤ 93`. -/
theorem le_93_of_small {n k : ℕ} (hk : 1 ≤ k) (hk7 : k ≤ 7)
    (hb : n ^ (k - k.primeCounting) ≤ k ^ k) : n ≤ 93 := by
  interval_cases k <;> exact lt_of_pow_le (B := 94) (by decide) hb (by decide)

/-- For `8 ≤ k ≤ 37`, the bound `n ^ (k - π k) ≤ k ^ k` forces `n ≤ 210`. -/
theorem le_210_of_mid {n k : ℕ} (hk8 : 8 ≤ k) (hk37 : k ≤ 37)
    (hb : n ^ (k - k.primeCounting) ≤ k ^ k) : n ≤ 210 := by
  interval_cases k <;> exact lt_of_pow_le (B := 211) (by decide) hb (by decide)

/-- Sylvester–Schur for `k² < n` when `2 π k ≤ k`: then `n ^ (k - π k) ≤ k ^ k`
would give `n ^ k ≤ (k ^ 2) ^ k`, i.e. `n ≤ k ^ 2` — a contradiction. -/
theorem exists_prime_dvd_choose_of_sq_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hπ : 2 * k.primeCounting ≤ k) (hsq : k ^ 2 < n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have hb := pow_sub_le_of_forall_prime_le hk hkn
    (fun q hq hqd => le_of_not_gt (fun hqk => hcon q hq hqk hqd))
  have e2 : k ≤ 2 * (k - k.primeCounting) := by omega
  have hbig : n ^ k ≤ (k ^ 2) ^ k := by
    calc n ^ k ≤ n ^ (2 * (k - k.primeCounting)) :=
          pow_le_pow_right' (by omega : (1 : ℕ) ≤ n) e2
      _ = (n ^ (k - k.primeCounting)) ^ 2 := by
          rw [mul_comm 2 (k - k.primeCounting), pow_mul]
      _ ≤ (k ^ k) ^ 2 := pow_le_pow_left' hb 2
      _ = (k ^ 2) ^ k := by rw [← pow_mul, mul_comm k 2, pow_mul]
  have hnk : n ≤ k ^ 2 := (Nat.pow_le_pow_iff_left (by omega)).mp hbig
  omega

/-!
### Finite verification of the small cases

The checks below use kernel `decide` on the equivalent computational
formulation "there is a prime `q > k` with `n % q < k`" (such a `q` has the
multiple `n - n % q` in `(n - k, n]`), with primality outsourced to the
explicit list `primeList210`.  No native-code decide and no extra axioms.
-/

/-- All primes `≤ 210`, as an explicit list for kernel-efficient checking. -/
def primeList210 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

set_option maxRecDepth 10000 in
/-- Every element of `primeList210` is prime (kernel `decide`). -/
theorem primeList210_prime : ∀ q ∈ primeList210, q.Prime := by decide

set_option maxRecDepth 10000 in
/-- Finite check, `k ≤ 7`, `n ≤ 93` (kernel `decide`). -/
theorem check_small :
    ∀ n ∈ Finset.Icc 2 93, ∀ k ∈ Finset.Icc 1 7,
      2 * k ≤ n → ∃ q ∈ primeList210, k < q ∧ n % q < k := by
  decide

set_option maxRecDepth 10000 in
/-- Finite check, `8 ≤ k ≤ 37`, `n ≤ 210` (kernel `decide`). -/
theorem check_mid :
    ∀ n ∈ Finset.Icc 16 210, ∀ k ∈ Finset.Icc 8 37,
      2 * k ≤ n → ∃ q ∈ primeList210, k < q ∧ n % q < k := by
  decide

/-- Sylvester–Schur for `k ≤ 7`, `n ≤ 93` (finite verification). -/
theorem exists_prime_dvd_choose_small {n k : ℕ} (hk : 1 ≤ k) (hk7 : k ≤ 7)
    (h2k : 2 * k ≤ n) (hn : n ≤ 93) : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨q, hqL, hkq, hmod⟩ :=
    check_small n (Finset.mem_Icc.mpr ⟨by omega, hn⟩) k
      (Finset.mem_Icc.mpr ⟨hk, hk7⟩) h2k
  have hq : q.Prime := primeList210_prime q hqL
  exact ⟨q, hq, hkq, prime_dvd_choose_of_mod_lt hq hkq (by omega) hmod⟩

/-- Sylvester–Schur for `8 ≤ k ≤ 37`, `n ≤ 210` (finite verification). -/
theorem exists_prime_dvd_choose_mid {n k : ℕ} (hk : 1 ≤ k) (hk8 : 8 ≤ k)
    (hk37 : k ≤ 37) (h2k : 2 * k ≤ n) (hn : n ≤ 210) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨q, hqL, hkq, hmod⟩ :=
    check_mid n (Finset.mem_Icc.mpr ⟨by omega, hn⟩) k
      (Finset.mem_Icc.mpr ⟨hk8, hk37⟩) h2k
  have hq : q.Prime := primeList210_prime q hqL
  exact ⟨q, hq, hkq, prime_dvd_choose_of_mod_lt hq hkq (by omega) hmod⟩

/-!
### The residual quadratic regime and the main theorem
-/

/-- The residual **quadratic regime** of the Sylvester–Schur theorem:
`38 ≤ k` and `2 * k + 2 ≤ n ≤ k ^ 2`.  This is the case in which Erdős's 1934
§§2–4 analysis (iterated primorial/`ψ`-bounds together with a finite
verification up to `n = 2304`) is needed; it is the only case not discharged
in this file. -/
def QuadRegimeOpen (n k : ℕ) : Prop :=
  38 ≤ k ∧ 2 * k + 2 ≤ n ∧ n ≤ k ^ 2

/-- **Sylvester–Schur**, conditional on the quadratic-regime hypothesis
`hquad`: for `1 ≤ k` and `2 * k ≤ n`, the binomial coefficient `C(n,k)` has a
prime divisor `> k`.  Every case except `QuadRegimeOpen` is proved
unconditionally:

* `n ≤ 2k + 1`: Bertrand's postulate;
* `k ≤ 37`: the analytic bound `n ≤ 210` (resp. `n ≤ 93`) plus finite checks;
* `k ^ 2 < n`: Erdős's lemma with `2 π k ≤ k`. -/
theorem exists_prime_dvd_choose
    (hquad : ∀ n' k' : ℕ, QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k')
    {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have hkn : k ≤ n := by omega
  rcases lt_or_ge n (2 * k + 2) with hn | hn
  · exact exists_prime_dvd_choose_of_le hk h (by omega)
  · rcases le_or_gt 38 k with hk38 | hk37
    · rcases le_or_gt n (k ^ 2) with hsq | hsq
      · -- `38 ≤ k`, `2k + 2 ≤ n ≤ k ^ 2`: the residual quadratic regime.
        exact hquad n k ⟨hk38, hn, hsq⟩
      · exact exists_prime_dvd_choose_of_sq_lt hk hkn
          (two_mul_primeCounting_le (by omega)) (by omega)
    · -- `k ≤ 37`: if no large prime divides `C(n,k)`, the analytic bound
      -- forces `n ≤ 93` (`k ≤ 7`) or `n ≤ 210` (`8 ≤ k ≤ 37`), where the
      -- finite checks supply a large prime divisor — a contradiction.
      by_contra hcon
      push_neg at hcon
      have hb := pow_sub_le_of_forall_prime_le hk hkn
        (fun q hq hqd => le_of_not_gt (fun hqk => hcon q hq hqk hqd))
      rcases lt_or_ge k 8 with hk8 | hk8
      · obtain ⟨q, hq, hqk, hdvd⟩ := exists_prime_dvd_choose_small hk (by omega) h
          (le_93_of_small hk (by omega) hb)
        exact hcon q hq hqk hdvd
      · obtain ⟨q, hq, hqk, hdvd⟩ := exists_prime_dvd_choose_mid hk hk8 (by omega) h
          (le_210_of_mid hk8 (by omega) hb)
        exact hcon q hq hqk hdvd

/-!
### Consecutive-integers form (downstream shape)
-/

/-- Transfer: a prime `q > k` dividing `C(n,k)` supplies an `m ∈ (n - k, n]`
divisible by `q`. -/
theorem exists_prime_mem_Icc_dvd_of_choose {n k : ℕ} (hkn : k ≤ n)
    (h : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k) :
    ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q, q.Prime ∧ k < q ∧ q ∣ m := by
  obtain ⟨q, hq, hqk, hd⟩ := h
  obtain ⟨m, hm, hqm⟩ := exists_mem_Icc_of_prime_dvd_choose hq hqk hkn hd
  exact ⟨m, hm, q, hq, hqk, hqm⟩

/-- Downstream shape: among the `P` consecutive integers `u, …, u + P - 1` with
`P + 1 ≤ u`, one is divisible by a prime `> P` — conditional on the
quadratic-regime hypothesis `hquad`. -/
theorem exists_prime_mem_Icc_dvd
    (hquad : ∀ n' k' : ℕ, QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k')
    {u P : ℕ} (hP : 1 ≤ P) (hu : P + 1 ≤ u) :
    ∃ m ∈ Finset.Icc u (u + P - 1), ∃ q, q.Prime ∧ P < q ∧ q ∣ m := by
  obtain ⟨q, hq, hqP, hd⟩ :=
    exists_prime_dvd_choose (n := u + P - 1) (k := P) hquad hP (by omega)
  obtain ⟨m, hm, hqm⟩ :=
    exists_mem_Icc_of_prime_dvd_choose hq hqP (by omega : P ≤ u + P - 1) hd
  rw [Finset.mem_Icc] at hm
  exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, q, hq, hqP, hqm⟩

/-- **Sylvester–Schur** in the exact form of the downstream predicate
`JSP314.SylvesterSchur a L` (`∃ p, p.Prime ∧ L < p ∧ ∃ i ∈ Icc a (a+L-1), p ∣ i`),
conditional on the quadratic-regime hypothesis.  (The hypothesis `1 ≤ L` is
needed because the `L = 0` statement is vacuously false.) -/
theorem sylvesterSchur
    (hquad : ∀ n' k' : ℕ, QuadRegimeOpen n' k' →
      ∃ q, q.Prime ∧ k' < q ∧ q ∣ n'.choose k')
    {a L : ℕ} (hL : 1 ≤ L) (hLa : L < a) :
    ∃ p : ℕ, p.Prime ∧ L < p ∧ ∃ i ∈ Finset.Icc a (a + L - 1), p ∣ i := by
  obtain ⟨m, hm, q, hq, hqL, hqm⟩ :=
    exists_prime_mem_Icc_dvd (u := a) (P := L) hquad hL (by omega)
  exact ⟨q, hq, hqL, m, hm, hqm⟩

end SylvesterSchur
