/-
# Sylvester–Schur theorem (partial formalization)

Target statement (downstream need for the Erdős–Graham/Tao problem):

`theorem exists_prime_dvd_choose {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k ≤ n) :
    ∃ q, Nat.Prime q ∧ k < q ∧ q ∣ Nat.choose n k`

This file formalizes the elementary (Erdős 1934) machinery and proves the theorem in
all cases except the genuinely hard "quadratic regime" `38 ≤ k` and `2 * k + 2 ≤ n ≤ k ^ 2`,
which needs Erdős's §§2–4 analysis (iterated dyadic coverings of `(1, n]` by intervals
`(a_i, 2 a_i]`, Chebyshev-type `θ`-bounds extracted from `centralBinom`, and finite
verification for `k ≤ 37`, `n ≤ 2304`).

## What is proved here

* `pow_le_pow_mul_choose`: the lower bound `n ^ k ≤ k ^ k * C(n,k)`
  (i.e. `(n / k) ^ k ≤ C(n,k)`, phrased division-free).
* `choose_le_pow_primeCounting`: Erdős's lemma — if every prime divisor of `C(n,k)`
  is `≤ k` then `C(n,k) ≤ n ^ π(k)`, using Mathlib's valuation bound
  `Nat.pow_factorization_choose_le : p ^ (C(n,k)).factorization p ≤ n`.
* `pow_sub_le_of_forall_prime_le`: combining the two bounds, `n ^ (k - π k) ≤ k ^ k`.
* `exists_prime_dvd_choose_of_le`: the case `n ≤ 2 * k + 1` via Bertrand's postulate.
* `exists_prime_dvd_choose_of_sq_lt`: the case `k ^ 2 < n` whenever `2 * π k ≤ k`
  (proved for `8 ≤ k` via `Nat.primeCounting_add_le` — the mod-6 sieve).
* `sylvesterSchur_check_small` / `sylvesterSchur_check_mid`: finite verification of
  the statement "some `m ∈ (n - k, n]` has a prime divisor `> k`" for the small cases
  the analytic bounds cannot reach (`n ≤ 93` for `k ≤ 7`, `n ≤ 210` for `8 ≤ k ≤ 37`).
* `exists_prime_dvd_choose`: the Sylvester–Schur conclusion under the side condition
  `k ≤ 37 ∨ n ≤ 2 * k + 1 ∨ k ^ 2 < n`.
* `exists_prime_mem_Icc_dvd_of_choose` and `exists_prime_mem_Icc_dvd`: transfer to
  the consecutive-integers formulation used downstream
  (`∃ m ∈ Finset.Icc u (u + P - 1), ∃ q, q.Prime ∧ P < q ∧ q ∣ m`).

## Note on `native_decide`

`sylvesterSchur_check_mid` is proved by `native_decide`, which introduces Lean's
`Lean.ofReduceBool` trust axiom (native evaluation). `sylvesterSchur_check_small`
is proved by kernel `decide` and adds no axioms.
-/

import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

namespace SylvesterSchur

open Finset

/-!
### Transfer: a prime `p > k` divides `C(n,k)` iff it divides some `m ∈ (n - k, n]`
-/

/-- If a prime `p > k` divides some `m` in the "top interval" `(n - k, n]`,
then `p ∣ n.choose k`. The reason: `n.choose k` equals the product of the `k`
consecutive factors `n - k + 1, …, n` divided by `k !`, and `p ∤ k !`. -/
theorem dvd_choose_of_prime_dvd {n k m p : ℕ} (hp : p.Prime) (hk : k < p)
    (hm : m ∈ Finset.Icc (n + 1 - k) n) (hd : p ∣ m) : p ∣ n.choose k := by
  rw [Finset.mem_Icc] at hm
  have hkn : k ≤ n := by omega
  have hdvd : m ∣ n.descFactorial k := by
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
    have h' : k * i ≤ n * i := mul_le_mul_right' hkn i
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
          Finset.prod_le_prod (fun i _ => Nat.zero_le _) hfactor
      _ = k ^ k * n.descFactorial k := h1.symm
      _ = (k ^ k * n.choose k) * k ! := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
  exact le_of_mul_le_mul_right h4 (Nat.factorial_pos k)

/-!
### Erdős's lemma: `C(n,k)` with only small prime factors is small
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
        Finset.prod_le_prod (fun i _ => Nat.zero_le _)
          (fun i _ => Nat.pow_factorization_choose_le hn)
    _ = n ^ k.primeCounting := by
        rw [Finset.prod_const, Nat.primesLE_card_eq_primeCounting]

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
    exact hb.trans (mul_le_mul_left' hc _)
  exact le_of_mul_le_mul_right h2 (pow_pos hn0 _)

/-- If `n ^ e ≤ C < B ^ e` with `e > 0`, then `n < B`. -/
theorem lt_of_pow_le {n e C B : ℕ} (he : 0 < e) (h : n ^ e ≤ C) (hB : C < B ^ e) :
    n < B := by
  by_contra hn
  push_neg at hn
  have : B ^ e ≤ n ^ e := Nat.pow_le_pow_left hn _
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
-/

/-- Finite check, `k ≤ 7`, `n ≤ 93` (proved by `native_decide`,
hence relies on `Lean.ofReduceBool`; kernel `decide` is too slow here). -/
theorem sylvesterSchur_check_small :
    ∀ n ∈ Finset.Icc 2 93, ∀ k ∈ Finset.Icc 1 7,
      2 * k ≤ n → ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q ∈ Finset.Icc (k + 1) m,
        q.Prime ∧ q ∣ m := by
  native_decide

/-- Finite check, `8 ≤ k ≤ 37`, `n ≤ 210` (proved by `native_decide`,
hence relies on `Lean.ofReduceBool`). -/
theorem sylvesterSchur_check_mid :
    ∀ n ∈ Finset.Icc 16 210, ∀ k ∈ Finset.Icc 8 37,
      2 * k ≤ n → ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q ∈ Finset.Icc (k + 1) m,
        q.Prime ∧ q ∣ m := by
  native_decide

/-- Sylvester–Schur for `k ≤ 7`, `n ≤ 93` (finite verification). -/
theorem exists_prime_dvd_choose_small {n k : ℕ} (hk : 1 ≤ k) (hk7 : k ≤ 7)
    (h2k : 2 * k ≤ n) (hn : n ≤ 93) : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨m, hm, q, hq, hpq, hqm⟩ :=
    sylvesterSchur_check_small n (Finset.mem_Icc.mpr ⟨by omega, hn⟩) k
      (Finset.mem_Icc.mpr ⟨hk, hk7⟩) h2k
  rw [Finset.mem_Icc] at hm hq
  exact ⟨q, hpq, by omega, dvd_choose_of_prime_dvd hpq (by omega)
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hqm⟩

/-- Sylvester–Schur for `8 ≤ k ≤ 37`, `n ≤ 210` (finite verification). -/
theorem exists_prime_dvd_choose_mid {n k : ℕ} (hk : 1 ≤ k) (hk8 : 8 ≤ k)
    (hk37 : k ≤ 37) (h2k : 2 * k ≤ n) (hn : n ≤ 210) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨m, hm, q, hq, hpq, hqm⟩ :=
    sylvesterSchur_check_mid n (Finset.mem_Icc.mpr ⟨by omega, hn⟩) k
      (Finset.mem_Icc.mpr ⟨hk8, hk37⟩) h2k
  rw [Finset.mem_Icc] at hm hq
  exact ⟨q, hpq, by omega, dvd_choose_of_prime_dvd hpq (by omega)
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hqm⟩

/-!
### The main theorem
-/

/-- **Sylvester–Schur**, proved whenever `k ≤ 37`, `n ≤ 2k + 1`, or `k² < n`.

The remaining open case is `38 ≤ k` with `2k + 2 ≤ n ≤ k²` — Erdős's §§2–4
regime, which needs sharper Chebyshev-type estimates than are currently
available in Mathlib. -/
theorem exists_prime_dvd_choose {n k : ℕ} (hk : 1 ≤ k) (h : 2 * k ≤ n)
    (hcase : k ≤ 37 ∨ n ≤ 2 * k + 1 ∨ k ^ 2 < n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have hkn : k ≤ n := by omega
  rcases hcase with hk37 | hn | hsq
  · rcases Nat.lt_or_ge n 211 with hn211 | hn211
    · rcases lt_or_ge k 8 with hk8 | hk8
      · exact exists_prime_dvd_choose_small hk (by omega) h (by omega)
      · exact exists_prime_dvd_choose_mid hk hk8 hk37 h (by omega)
    · -- `n ≥ 211`, `k ≤ 37`: the analytic bound gives `n ≤ 210` (or `n ≤ 93`
      -- for `k ≤ 7`), a contradiction unless a large prime divides `C(n,k)`.
      by_contra hcon
      push_neg at hcon
      have hb := pow_sub_le_of_forall_prime_le hk hkn
        (fun q hq hqd => le_of_not_gt (fun hqk => hcon q hq hqk hqd))
      rcases lt_or_ge k 8 with hk8 | hk8
      · have := le_93_of_small hk (by omega) hb
        omega
      · have := le_210_of_mid hk8 hk37 hb
        omega
  · exact exists_prime_dvd_choose_of_le hk h hn
  · rcases lt_or_ge k 8 with hk8 | hk8
    · rcases Nat.lt_or_ge n 94 with h94 | h94
      · exact exists_prime_dvd_choose_small hk (by omega) h (by omega)
      · by_contra hcon
        push_neg at hcon
        have hb := pow_sub_le_of_forall_prime_le hk hkn
          (fun q hq hqd => le_of_not_gt (fun hqk => hcon q hq hqk hqd))
        have := le_93_of_small hk (by omega) hb
        omega
    · exact exists_prime_dvd_choose_of_sq_lt hk hkn (two_mul_primeCounting_le hk8) hsq

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
`P + 1 ≤ u`, one is divisible by a prime `> P` — whenever the corresponding
`C(u + P - 1, P)` case of Sylvester–Schur is available. -/
theorem exists_prime_mem_Icc_dvd {u P : ℕ} (hP : 1 ≤ P) (hu : P + 1 ≤ u)
    (hcase : P ≤ 37 ∨ u + P - 1 ≤ 2 * P + 1 ∨ P ^ 2 < u + P - 1) :
    ∃ m ∈ Finset.Icc u (u + P - 1), ∃ q, q.Prime ∧ P < q ∧ q ∣ m := by
  obtain ⟨q, hq, hqP, hd⟩ := exists_prime_dvd_choose hP (by omega) hcase
  obtain ⟨m, hm, hqm⟩ :=
    exists_mem_Icc_of_prime_dvd_choose hq hqP (by omega : P ≤ u + P - 1) hd
  rw [Finset.mem_Icc] at hm
  exact ⟨m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, q, hq, hqP, hqm⟩

end SylvesterSchur
