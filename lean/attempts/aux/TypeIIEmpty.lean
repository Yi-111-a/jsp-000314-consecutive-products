import JSP314.TwoCaseCount
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.IntervalCases

/-!
# Type-II coverage is empty modulo Sylvester–Schur

A Type-II covered `n` sits in a bad interval `[u, v]` with `u < v`,
`P ≤ v - u` (where `P` is the largest prime factor of `∏_{i=u}^{v} i`), every
element of `[u, v]` is `P`-smooth, and — by the Bertrand argument
`v < 2u` — `P < u`.  Hence `(u, u + P] ⊆ [u, v]` is a run of `P` consecutive
`P`-smooth integers all exceeding `P`.  Sylvester–Schur (`C(u+P, P)` has a
prime factor `> P`, which must divide one of the `P` consecutive top factors
`u + 1, …, u + P`) then gives a contradiction.

`attempts/` is outside the library glob, so the partial Sylvester–Schur file
`attempts/aux/SylvesterSchur.lean` cannot be imported.  This file therefore

* copies, verbatim and with credit, the *kernel-checkable* lemmas of that file
  (the Bertrand cases, the `k² < n` analytic case, and the choose↔consecutive
  transfer lemmas) — everything except the two `native_decide` finite checks;
* packages the finite checks as a single hypothesis `SylvesterSchur.finiteCheck`
  (discharged in `SylvesterSchur.lean` by `sylvesterSchur_check_small` and
  `sylvesterSchur_check_mid`, both `native_decide`);
* packages the remaining open regime as `JSP314.SSResidual` — Erdős's
  quadratic regime `38 ≤ P`, `P + 2 ≤ u`, `u + P ≤ P²` (with `u = P + 2`
  needed only when `P + 2` is prime).

## Proved here (no placeholders)

* `JSP314.typeIICovered_imp_smooth_run_ge`: a Type-II cover yields
  `P < u`, `u + P ≤ v` and a `P`-smooth `[u, v]`.
* `JSP314.typeIICovered_imp_choose_smooth`: the run `(u, u+P]` is `P`-smooth.
* `JSP314.ss_cases`: for `P` prime and `P < u`, either `C(u+P, P)` has a
  prime factor `> P`, or `(P, u)` lies in the residual quadratic regime —
  *conditionally on `SylvesterSchur.finiteCheck`*, covering exactly the cases
  `u = P + 1` (Bertrand), `u = P + 2` with `P + 2` composite (Bertrand),
  `P ≤ 37` (finite check `n ≤ 210` / analytic bound `n ≥ 211`), and
  `P² < u + P` (the `k² < n` Erdős bound, `8 ≤ P`).
* `JSP314.typeIICovered_imp_residual`: modulo `finiteCheck`, every Type-II
  cover produces a residual-regime smooth run.
* `JSP314.not_typeIICovered`, `JSP314.typeIICount_eq_zero`: `typeIICount x = 0`
  modulo `finiteCheck` and `SSResidual`.
-/

namespace SylvesterSchur

open Finset

/-! ### Copied verbatim from `attempts/aux/SylvesterSchur.lean` (kernel-checked
portion; the two `native_decide` finite checks are replaced by the hypothesis
`finiteCheck` below).  Credit: the sibling aux file. -/

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

/-- Conversely, if a prime `p > k` divides `n.choose k`, it divides one of the
top factors `m ∈ (n - k, n]` — the Sylvester–Schur statement is equivalent to
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

/-- Sylvester–Schur for `2k ≤ n ≤ 2k + 1`: Bertrand's postulate supplies a
prime `p ∈ (n - k, n]`, which is itself one of the top factors and satisfies
`p > k`. -/
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

/-- If every prime divisor of `C(n,k)` is at most `k`, then `C(n,k) ≤ n ^ π(k)`:
the factorization `C(n,k) = ∏ p ^ a_p` ranges over primes `≤ k` (there are
`π k` of them) and each factor satisfies `p ^ a_p ≤ n` by
`Nat.pow_factorization_choose_le`. -/
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

/-- Transfer: a prime `q > k` dividing `C(n,k)` supplies an `m ∈ (n - k, n]`
divisible by `q`. -/
theorem exists_prime_mem_Icc_dvd_of_choose {n k : ℕ} (hkn : k ≤ n)
    (h : ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k) :
    ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q, q.Prime ∧ k < q ∧ q ∣ m := by
  obtain ⟨q, hq, hqk, hd⟩ := h
  obtain ⟨m, hm, hqm⟩ := exists_mem_Icc_of_prime_dvd_choose hq hqk hkn hd
  exact ⟨m, hm, q, hq, hqk, hqm⟩

/-!
### The finite-verification hypothesis

The sibling file `attempts/aux/SylvesterSchur.lean` discharges this finite
range by `native_decide` (`sylvesterSchur_check_small` for `k ≤ 7`, `n ≤ 93`
and `sylvesterSchur_check_mid` for `8 ≤ k ≤ 37`, `n ≤ 210`; both statements
give an `m ∈ (n - k, n]` with a prime divisor `> k`, which transfers to
`q ∣ n.choose k` via `dvd_choose_of_prime_dvd`).  We keep it as a hypothesis so
that this file introduces no `Lean.ofReduceBool` dependency.
-/

/-- The finite range of Sylvester–Schur: for `k ≤ 37` and `2k ≤ n ≤ 210`,
some prime `q > k` divides `C(n,k)`.  True (and verified) by
`sylvesterSchur_check_small`/`sylvesterSchur_check_mid` in
`attempts/aux/SylvesterSchur.lean`. -/
def finiteCheck : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ 37 → 2 * k ≤ n → n ≤ 210 →
    ∃ q, Nat.Prime q ∧ k < q ∧ q ∣ Nat.choose n k

/-- The `P ≤ 37`, `n ≥ 211` sub-case: the analytic bound
`n ^ (k - π k) ≤ k ^ k` already forces `n ≤ 210` (or `n ≤ 93` for `k ≤ 7`),
contradicting `211 ≤ n`. -/
theorem exists_prime_dvd_choose_of_mid_large {n k : ℕ} (hk : 1 ≤ k)
    (hk37 : k ≤ 37) (hkn : k ≤ n) (hn : 211 ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have hb := pow_sub_le_of_forall_prime_le hk hkn
    (fun q hq hqd => le_of_not_gt (fun hqk => hcon q hq hqk hqd))
  rcases lt_or_ge k 8 with hk8 | hk8
  · have h93 := le_93_of_small hk (by omega) hb
    omega
  · have h210 := le_210_of_mid hk8 hk37 hb
    omega

end SylvesterSchur

namespace JSP314

open Classical

/-- Private copy of `isBadInterval_iff` (Localization.lean), kept local. -/
private theorem isBadInterval_iff' {u v : ℕ} :
    IsBadInterval u v ↔
      u ≤ v ∧ largestPrimeFactor ((Finset.Icc u v).prod id) ≠ 1 ∧
        largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2 ∣
          (Finset.Icc u v).prod id :=
  Iff.rfl

/-- Private copy of `exists_mem_dvd_of_largestPrimeFactor` (ProdLPF.lean /
TwoCaseCount.lean). -/
private theorem exists_mem_dvd_of_largestPrimeFactor' {u v : ℕ}
    (h : 2 ≤ (Finset.Icc u v).prod id) :
    ∃ m ∈ Finset.Icc u v, largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m := by
  have hP := largestPrimeFactor_prime h
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ∣
      (Finset.Icc u v).prod id :=
    largestPrimeFactor_dvd h
  obtain ⟨m, hm, hdiv⟩ :=
    ((Nat.prime_iff.mp hP).dvd_finsetProd_iff id).mp hdvd
  exact ⟨m, hm, hdiv⟩

/-- Private copy of `bad_interval_v_lt_two_mul_u` (TwoCaseCount.lean, where it
is `private`): a bad interval `[u, v]` with `u < v` satisfies `v < 2u`. -/
private theorem bad_interval_v_lt_two_mul_u' {u v : ℕ} (huv : u < v)
    (hbad : IsBadInterval u v) : v < 2 * u := by
  obtain ⟨-, hP1, hP2⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h
    push_neg at h
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · exfalso
      apply hP1
      apply largestPrimeFactor_eq_one_iff.2
      have hprod0 : (Finset.Icc u v).prod id = 0 := by
        rw [Finset.prod_eq_zero_iff]
        exact ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
      omega
    · exact h0
  by_contra h2u
  push_neg at h2u
  have hv2 : v / 2 ≠ 0 := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ := Nat.bertrand (v / 2) hv2
  have hpmem : p ∈ Finset.Icc u v := by
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hp_le_P : p ≤ largestPrimeFactor ((Finset.Icc u v).prod id) :=
    prime_dvd_le_largestPrimeFactor hprod2 hpprime
      (Finset.dvd_prod_of_mem id hpmem)
  have hv_lt_2P : v < 2 * largestPrimeFactor ((Finset.Icc u v).prod id) := by
    omega
  have huniq : ∀ m' ∈ Finset.Icc u v,
      largestPrimeFactor ((Finset.Icc u v).prod id) ∣ m' →
      m' = largestPrimeFactor ((Finset.Icc u v).prod id) := by
    intro m' hm' hdiv
    obtain ⟨k, hk⟩ := hdiv
    rw [Finset.mem_Icc] at hm'
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        rw [h0, mul_zero] at hk
        omega
      · exact h0
    have hk2 : k < 2 := by
      by_contra hk2
      push_neg at hk2
      have hle : largestPrimeFactor ((Finset.Icc u v).prod id) * 2 ≤
          largestPrimeFactor ((Finset.Icc u v).prod id) * k :=
        Nat.mul_le_mul (le_refl _) hk2
      rw [← hk] at hle
      omega
    interval_cases k
    · simpa using hk
  have hPmem : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∈ Finset.Icc u v := by
    obtain ⟨m, hm, hd⟩ := exists_mem_dvd_of_largestPrimeFactor' hprod2
    rwa [huniq m hm hd] at hm
  have hprod_eq : (Finset.Icc u v).prod id
      = largestPrimeFactor ((Finset.Icc u v).prod id) *
        ((Finset.Icc u v).erase
          (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id :=
    (Finset.mul_prod_erase _ _ hPmem).symm
  have hdvd : largestPrimeFactor ((Finset.Icc u v).prod id) ^ 2
      ∣ largestPrimeFactor ((Finset.Icc u v).prod id) *
        ((Finset.Icc u v).erase
          (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id := by
    rw [← hprod_eq]
    exact hP2
  rw [pow_two] at hdvd
  have hPe : largestPrimeFactor ((Finset.Icc u v).prod id)
      ∣ ((Finset.Icc u v).erase
        (largestPrimeFactor ((Finset.Icc u v).prod id))).prod id :=
    (mul_dvd_mul_iff_left hPprime.ne_zero).mp hdvd
  obtain ⟨m2, hm2, hdvd2⟩ :=
    ((Nat.prime_iff.mp hPprime).dvd_finsetProd_iff id).mp hPe
  obtain ⟨hne, hm2'⟩ := Finset.mem_erase.mp hm2
  exact hne (huniq m2 hm2' hdvd2)

/-- **Reduction**: a Type-II cover of `n` yields a prime `P < u`, a long
interval `u + P ≤ v`, and a `P`-smooth `[u, v]` (every prime divisor of every
element divides the interval product, hence is `≤ P`). -/
theorem typeIICovered_imp_smooth_run_ge {n : ℕ} (h : TypeIICovered n) :
    ∃ u v P : ℕ, Nat.Prime P ∧ P < u ∧ u + P ≤ v ∧ u ≤ n ∧ n ≤ v ∧
      ∀ m ∈ Finset.Icc u v, ∀ q, Nat.Prime q → q ∣ m → q ≤ P := by
  obtain ⟨u, v, huv, hbad, hPle, hun, hnv⟩ := h
  obtain ⟨-, hP1, -⟩ := isBadInterval_iff'.1 hbad
  have hprod2 : 2 ≤ (Finset.Icc u v).prod id := by
    by_contra h'
    push_neg at h'
    exact hP1 (largestPrimeFactor_eq_one_iff.2 (Nat.le_of_lt_succ h'))
  have hPprime : Nat.Prime (largestPrimeFactor ((Finset.Icc u v).prod id)) :=
    largestPrimeFactor_prime hprod2
  have hlt : v < 2 * u := bad_interval_v_lt_two_mul_u' huv hbad
  refine ⟨u, v, _, hPprime, by omega, by omega, hun, hnv, ?_⟩
  intro m hm q hq hqm
  exact prime_dvd_le_largestPrimeFactor hprod2 hq
    (dvd_trans hqm (Finset.dvd_prod_of_mem id hm))

/-- The Sylvester–Schur-shaped consequence: the run `(u, u + P]` of `P`
consecutive integers, all `> P`, is `P`-smooth. -/
theorem typeIICovered_imp_choose_smooth {n : ℕ} (h : TypeIICovered n) :
    ∃ u P : ℕ, Nat.Prime P ∧ P < u ∧
      ∀ m ∈ Finset.Icc (u + 1) (u + P), ∀ q, Nat.Prime q → q ∣ m → q ≤ P := by
  obtain ⟨u, v, P, hPp, hPu, huv, hun, hnv, hsm⟩ :=
    typeIICovered_imp_smooth_run_ge h
  refine ⟨u, P, hPp, hPu, fun m hm q hq hqm => hsm m ?_ q hq hqm⟩
  rw [Finset.mem_Icc] at hm ⊢
  omega

/-- Case analysis for `P` prime, `P < u`: either `C(u+P, P)` has a prime
factor `> P`, or `(P, u)` lies in the residual quadratic regime
(`38 ≤ P`, `P + 2 ≤ u`, `u + P ≤ P²`, and `u = P + 2` only if `P + 2` is
prime).  All other regimes are covered:

* `u = P + 1`: Bertrand (`exists_prime_dvd_choose_of_le`);
* `u = P + 2`, `P + 2` composite: Bertrand (`exists_prime_dvd_choose_of_eq`);
* `P ≤ 37`: `finiteCheck` for `u + P ≤ 210`, analytic bound otherwise;
* `u + P > P²` (and `P ≥ 38`): `exists_prime_dvd_choose_of_sq_lt`. -/
theorem ss_cases (hF : SylvesterSchur.finiteCheck) {P u : ℕ}
    (hPp : Nat.Prime P) (hPu : P < u) :
    (∃ q, Nat.Prime q ∧ P < q ∧ q ∣ Nat.choose (u + P) P) ∨
      (38 ≤ P ∧ P + 2 ≤ u ∧ u + P ≤ P ^ 2 ∧
        (u = P + 2 → Nat.Prime (P + 2))) := by
  have hP1 : 1 ≤ P := hPp.one_lt.le
  rcases lt_or_ge u (P + 2) with hu | hu
  · -- `u = P + 1`: `n = u + P = 2P + 1`, the Bertrand case.
    have hu1 : u = P + 1 := by omega
    subst u
    exact Or.inl (SylvesterSchur.exists_prime_dvd_choose_of_le hP1
      (by omega) (by omega))
  rcases lt_or_ge u (P + 3) with hu' | hu'
  · -- `u = P + 2`.
    have hu2 : u = P + 2 := by omega
    subst u
    by_cases hcomp : Nat.Prime (P + 2)
    · -- `P + 2` prime: residual only when `38 ≤ P` and `2P + 2 ≤ P²`.
      by_cases h38 : 38 ≤ P
      · refine Or.inr ⟨h38, le_refl _, ?_, fun _ => hcomp⟩
        rw [pow_two]
        calc P + 2 + P ≤ 38 * P := by omega
          _ ≤ P * P := mul_le_mul_right' h38 P
      · -- `P ≤ 37`, `n = 2P + 2 ≤ 76 ≤ 210`: finite check.
        exact Or.inl (hF (P + 2 + P) P hP1 (by omega) (by omega) (by omega))
    · -- `P + 2` composite: Bertrand `n = 2k + 2` case.
      exact Or.inl (SylvesterSchur.exists_prime_dvd_choose_of_eq hP1
        (by omega) hcomp)
  · -- `u ≥ P + 3`.
    by_cases h37 : P ≤ 37
    · rcases le_or_lt (u + P) 210 with hn | hn
      · exact Or.inl (hF (u + P) P hP1 h37 (by omega) hn)
      · exact Or.inl (SylvesterSchur.exists_prime_dvd_choose_of_mid_large hP1
          h37 (by omega) (by omega))
    · rcases le_or_lt (u + P) (P ^ 2) with hsq | hsq
      · exact Or.inr ⟨by omega, by omega, hsq, fun h => absurd h (by omega)⟩
      · exact Or.inl (SylvesterSchur.exists_prime_dvd_choose_of_sq_lt hP1
          (by omega)
          (SylvesterSchur.two_mul_primeCounting_le (by omega)) (by omega))

/-- **Residual extraction**: modulo the finite Sylvester–Schur check, every
Type-II cover produces a run of `P` consecutive `P`-smooth integers in the
residual quadratic regime `38 ≤ P`, `P + 2 ≤ u`, `u + P ≤ P²` (with
`u = P + 2` allowed only when `P + 2` is prime).  This isolates *exactly* the
(P, u) regimes the partial Sylvester–Schur file does not yet cover. -/
theorem typeIICovered_imp_residual (hF : SylvesterSchur.finiteCheck) {n : ℕ}
    (h : TypeIICovered n) :
    ∃ u P : ℕ, Nat.Prime P ∧ 38 ≤ P ∧ P + 2 ≤ u ∧ u + P ≤ P ^ 2 ∧
      (u = P + 2 → Nat.Prime (P + 2)) ∧
      ∀ m ∈ Finset.Icc (u + 1) (u + P), ∀ q, Nat.Prime q → q ∣ m → q ≤ P := by
  obtain ⟨u, P, hPp, hPu, hsm⟩ := typeIICovered_imp_choose_smooth h
  rcases ss_cases hF hPp hPu with hss | hres
  · obtain ⟨q, hq, hPq, hd⟩ := hss
    obtain ⟨m, hm, hqm⟩ := SylvesterSchur.exists_mem_Icc_of_prime_dvd_choose
      hq hPq (by omega : P ≤ u + P) hd
    rw [Finset.mem_Icc] at hm
    exact absurd (hsm m (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) q hq hqm)
      (not_le_of_gt hPq)
  · exact ⟨u, P, hPp, hres.1, hres.2.1, hres.2.2.1, hres.2.2.2, hsm⟩

/-- The residual Sylvester–Schur instances — Erdős's quadratic regime, the
only `(P, u)` configurations not discharged kernel-verifiably here:
`38 ≤ P`, `P + 2 ≤ u`, `u + P ≤ P²`, and `u = P + 2` only when `P + 2` is
prime.  This is a true mathematical statement (full Sylvester–Schur), but its
formal proof requires Erdős's §§2–4 dyadic-covering analysis. -/
def SSResidual : Prop :=
  ∀ P u : ℕ, Nat.Prime P → 38 ≤ P → P + 2 ≤ u → u + P ≤ P ^ 2 →
    (u = P + 2 → Nat.Prime (P + 2)) →
    ∃ q, Nat.Prime q ∧ P < q ∧ q ∣ Nat.choose (u + P) P

/-- Conditional emptiness of Type-II coverage: modulo the finite check and the
residual quadratic regime of Sylvester–Schur, no `n` is Type-II covered. -/
theorem not_typeIICovered (hF : SylvesterSchur.finiteCheck) (hR : SSResidual)
    {n : ℕ} (h : TypeIICovered n) : False := by
  obtain ⟨u, P, hPp, h38, h2u, hsq, hp2, hsm⟩ := typeIICovered_imp_residual hF h
  obtain ⟨q, hq, hPq, hd⟩ := hR P u hPp h38 h2u hsq hp2
  obtain ⟨m, hm, hqm⟩ := SylvesterSchur.exists_mem_Icc_of_prime_dvd_choose
    hq hPq (by omega : P ≤ u + P) hd
  rw [Finset.mem_Icc] at hm
  exact absurd (hsm m (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) q hq hqm)
    (not_le_of_gt hPq)

/-- Conditional headline: `typeIICount x = 0` modulo the finite check and the
residual quadratic regime of Sylvester–Schur. -/
theorem typeIICount_eq_zero (hF : SylvesterSchur.finiteCheck) (hR : SSResidual)
    (x : ℕ) : typeIICount x = 0 := by
  have h : ∀ n, ¬ TypeIICovered n := fun n hn => not_typeIICovered hF hR hn
  unfold typeIICount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  exact h n

end JSP314
