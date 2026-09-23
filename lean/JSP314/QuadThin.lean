import JSP314.QuadMid
import Mathlib.NumberTheory.Bertrand

/-!
# The thin band `2k + 2 ≤ n ≤ 3k` of the quadratic regime

This file isolates the *bookkeeping* core of the residual quadratic
regime `QuadRegimeOpen n k` (that is, `38 ≤ k`, `2k+2 ≤ n ≤ k²`) in the
thin band `n ≤ 3k`, where Erdős's iterated-primorial method
(`JSP314.QuadMid`) no longer applies.

## The valuation bookkeeping

For a prime `p > k`, `p ∣ C(n,k)` iff `p` divides one of the top `k`
factors `m ∈ (n-k, n]` — `prime_dvd_choose_iff_exists_dvd_mem`.  This
if-and-only-if needs *no* `p² > n` hypothesis (the `n < p²` condition of
Legendre's formula `v_p(C(n,k)) = ⌊n/p⌋ - ⌊k/p⌋ - ⌊(n-k)/p⌋` only serves
to bound the multiplicity by `1`; the divisibility criterion itself is
exact).  In the thin band `n ≤ 3k`, a multiple `m = r·p ≤ 3k < 3p` of a
prime `p > k` forces `r ∈ {1, 2}` (`prime_dvd_choose_thin`), so the
Sylvester–Schur conclusion in the band is *equivalent* to

    (n-k, n]  contains a prime      ∨      (k, n/2]  contains a prime

(`quadRegimeOpen_thin_iff`): a prime `p ∈ (k, n/2]` has its double
`2p ∈ (n-k, n]` since `2p ≥ 2k+2 ≥ n-k+1` when `n ≤ 3k+1`.  Failure is
therefore equivalent to both intervals being prime-free
(`quadRegimeOpen_thin_prime_free`), or, in the consecutive-integers
reformulation, to every element of `(n-k, n]` being `k`-smooth
(`quadRegimeOpen_thin_forall_prime_le`).

## What Bertrand's postulate reaches unconditionally

* `quadRegimeOpen_of_mem_Icc_prime`, `quadRegimeOpen_of_two_mul_prime`:
  a prime in `(n-k, n]`, or a prime `p > k` with `n-k < 2p ≤ n`, gives
  the conclusion for *every* `n` in the regime.
* `quadRegimeOpen_thin_of_forall_not_prime`: Bertrand's postulate at
  `k+1` produces a prime `p ∈ (k+1, 2k+2]`; it lands inside the top
  block `(n-k, n]` as soon as `(k+1, n-k]` is prime-free.  For
  `n = 2k+2` this is the single condition "`k+2` composite"; for
  `n = 2k+2+j` it is "`k+2, …, k+2+j` all composite".  This is the exact
  reach of one Bertrand application: no placement `(x, 2x]` can lie
  inside `(n-k, n]` for `n > 2k` (that would need `n-k ≤ x ≤ n/2`).
* `quadRegimeOpen_thin_of_prime_add`: if `k+1+t` is prime, then
  `2(k+1+t) ∈ (n-k, n]` for all `n` in the length-`k` window
  `2(k+1+t) ≤ n ≤ 2(k+1+t) + k - 1`.  In particular `k+1` prime closes
  the whole band `n ≤ 3k+1`.
* `quadRegimeOpen_thin_two_mul_add_two`: `n = 2k+2` is closed whenever
  `k+1` is prime or `k+2` is composite.  The leftover case — `k+1`
  composite and `k+2` prime — is exactly the statement "the least prime
  exceeding `k+2` is at most `2k+2`": Bertrand at `k+2` only delivers a
  prime `≤ 2k+3`, a single integer short.

## The conditional reduction

`quadRegimeOpen_thin_of_prime_gap` packages the remaining input as an
explicit hypothesis: any theorem of the shape

    ∀ x ≥ X₀, ∃ p prime, x < p ∧ 2p ≤ 3x          (a prime in (x, 3x/2])

applied at `x = n - k` closes the whole thin band `n ≤ 3k` for
`n - k ≥ X₀`, since `2p ≤ 3(n-k) ≤ 2n` iff `n ≤ 3k`.

On Bertrand iteration: a single application produces a prime in
`(x, 2x)`, and `2x` can be lowered to `2x - 1` only trivially (`2x` is
even and composite for `x ≥ 2`; see `exists_prime_lt_and_lt_two_mul`).
No finite iteration of the bare `p ≤ 2x` statement can force a prime
below `3x/2`: every application outputs an interval of ratio `2`, and the
existence of *some* prime in `(x, 2x]` gives no upper control on the
smallest such prime.  Reaching ratio `3/2` requires strengthening the
proof of Bertrand itself (Nagura-type `C(2n,n)` estimates) — i.e.
precisely the `hgap` input above.

No placeholder tactics; kernel-checkable.
-/

namespace SylvesterSchur

open Finset
open scoped Nat

/-!
### The valuation criterion
-/

/-- For a prime `p > k`, `p ∣ C(n,k)` iff `p` divides one of the top `k`
factors `m ∈ (n-k, n]`.  No `n < p²` hypothesis is needed — that
condition only bounds the multiplicity; the divisibility criterion is
exact for every `p > k`. -/
theorem prime_dvd_choose_iff_exists_dvd_mem {n k p : ℕ} (hp : p.Prime)
    (hkp : k < p) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ ∃ m ∈ Finset.Icc (n + 1 - k) n, p ∣ m :=
  ⟨exists_mem_Icc_of_prime_dvd_choose hp hkp hkn,
   fun ⟨_, hm, hdm⟩ ↦ dvd_choose_of_prime_dvd hp hkp hm hdm⟩

/-- The criterion with the Legendre-style hypotheses `p ≤ n < p²` (for
`p² > n` the valuation is `⌊n/p⌋ - ⌊k/p⌋ - ⌊(n-k)/p⌋`, which equals `1`
exactly when `p` has a multiple in `(n-k, n]`).  The hypothesis `hp2` is
in fact unused: the iff holds beyond the `p² > n` range. -/
theorem prime_dvd_choose_iff_mem {n k p : ℕ} (hp : p.Prime) (hkp : k < p)
    (hpn : p ≤ n) (_hp2 : n < p ^ 2) :
    p ∣ n.choose k ↔ ∃ m ∈ Finset.Icc (n + 1 - k) n, p ∣ m :=
  prime_dvd_choose_iff_exists_dvd_mem hp hkp (hkp.le.trans hpn)

/-- **Thin-band sharpening.**  For `n ≤ 3k`, a prime `p > k` dividing
`C(n,k)` satisfies `p ∈ (n-k, n]` or `2p ∈ (n-k, n]`: the multiple
`m = r·p` of `p` in the top block is `≤ n ≤ 3k < 3p`, forcing
`r ∈ {1, 2}`. -/
theorem prime_dvd_choose_thin {n k p : ℕ} (hn : n ≤ 3 * k) (hp : p.Prime)
    (hkp : k < p) (hkn : k ≤ n) (hd : p ∣ n.choose k) :
    p ∈ Finset.Icc (n + 1 - k) n ∨ 2 * p ∈ Finset.Icc (n + 1 - k) n := by
  obtain ⟨m, hm, hpm⟩ := exists_mem_Icc_of_prime_dvd_choose hp hkp hkn hd
  rw [Finset.mem_Icc] at hm
  obtain ⟨r, hr⟩ := hpm
  have hrpos : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, mul_zero] at hr
      omega
    · exact h0
  have hr3 : r < 3 := by
    by_contra hc
    push Not at hc
    have hle : p * 3 ≤ p * r := Nat.mul_le_mul (le_refl p) hc
    have hm3 : p * r ≤ 3 * k := by
      rw [← hr]
      exact hm.2.trans hn
    omega
  rcases (by omega : r = 1 ∨ r = 2) with h1 | h1
  · refine Or.inl ?_
    have hme : m = p := by rw [hr, h1, mul_one]
    rw [hme] at hm
    exact Finset.mem_Icc.mpr hm
  · refine Or.inr ?_
    have hme : m = 2 * p := by rw [hr, h1]; ring
    rw [hme] at hm
    exact Finset.mem_Icc.mpr hm

/-!
### Sufficient conditions valid in the whole regime
-/

/-- If some `m ∈ (n-k, n]` has a prime factor `p > k`, then
`p ∣ C(n,k)` — unconditionally, in the whole regime. -/
theorem quadRegimeOpen_of_mem_Icc_prime_factor {n k m p : ℕ}
    (_hq : QuadRegimeOpen n k) (hp : p.Prime) (hkp : k < p)
    (hm : m ∈ Finset.Icc (n + 1 - k) n) (hdm : p ∣ m) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  ⟨p, hp, hkp, dvd_choose_of_prime_dvd hp hkp hm hdm⟩

/-- A prime in the top block `(n-k, n]` is itself `> k` (since
`n - k ≥ k + 2` in the regime) and gives the conclusion. -/
theorem quadRegimeOpen_of_mem_Icc_prime {n k p : ℕ} (hq : QuadRegimeOpen n k)
    (hp : p.Prime) (hmem : p ∈ Finset.Icc (n + 1 - k) n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  rw [Finset.mem_Icc] at hmem
  exact ⟨p, hp, by omega,
    dvd_choose_of_prime_dvd hp (by omega) (Finset.mem_Icc.mpr hmem) (dvd_refl p)⟩

/-- A prime `p > k` whose double `2p` lies in the top block gives the
conclusion. -/
theorem quadRegimeOpen_of_two_mul_mem_Icc {n k p : ℕ} (_hq : QuadRegimeOpen n k)
    (hp : p.Prime) (hkp : k < p) (hmem : 2 * p ∈ Finset.Icc (n + 1 - k) n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  ⟨p, hp, hkp, dvd_choose_of_prime_dvd hp hkp hmem (dvd_mul_left p 2)⟩

/-- `n - k < 2p ≤ n` with `p > k` prime: the double `2p` is the
distinguished top-block element. -/
theorem quadRegimeOpen_of_two_mul_prime {n k p : ℕ} (hq : QuadRegimeOpen n k)
    (hp : p.Prime) (hkp : k < p) (h1 : n - k < 2 * p) (h2 : 2 * p ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  quadRegimeOpen_of_two_mul_mem_Icc hq hp hkp
    (Finset.mem_Icc.mpr ⟨by omega, h2⟩)

/-- In the thin band `n ≤ 3k + 1`, any prime `p ∈ (k, n/2]` has
`2p ∈ (n-k, n]` (since `2p ≥ 2k+2 ≥ n-k+1`) and hence gives the
conclusion. -/
theorem quadRegimeOpen_thin_of_prime_le_half {n k p : ℕ} (hq : QuadRegimeOpen n k)
    (hn : n ≤ 3 * k + 1) (hp : p.Prime) (hkp : k < p) (h2p : 2 * p ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  exact quadRegimeOpen_of_two_mul_prime hq hp hkp (by omega) h2p

/-- If `k + 1 + t` is prime, its double `2(k+1+t)` lies in `(n-k, n]` for
every `n` in the length-`k` window `2(k+1+t) ≤ n ≤ 2(k+1+t) + k - 1`,
closing the band there.  For `t = 0` this covers all `n ≤ 3k + 1`. -/
theorem quadRegimeOpen_thin_of_prime_add {n k t : ℕ} (hq : QuadRegimeOpen n k)
    (hp : (k + 1 + t).Prime) (h2 : 2 * (k + 1 + t) ≤ n)
    (h3 : n ≤ 2 * (k + 1 + t) + k - 1) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  quadRegimeOpen_of_two_mul_prime hq hp (by omega) (by omega) h2

/-!
### The thin-band equivalence
-/

/-- **Thin-band equivalence.**  For `n ≤ 3k` in the quadratic regime,
`C(n,k)` has a prime divisor `> k` iff `(n-k, n]` contains a prime or
`(k, n/2]` contains a prime (whose double then lies in `(n-k, n]`). -/
theorem quadRegimeOpen_thin_iff {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hn : n ≤ 3 * k) :
    (∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k) ↔
      (∃ p ∈ Finset.Icc (n + 1 - k) n, p.Prime) ∨
        (∃ p, p.Prime ∧ k < p ∧ 2 * p ≤ n) := by
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  constructor
  · rintro ⟨q, hqprime, hqk, hd⟩
    rcases prime_dvd_choose_thin hn hqprime hqk (by omega) hd with h | h
    · exact Or.inl ⟨q, h, hqprime⟩
    · rw [Finset.mem_Icc] at h
      exact Or.inr ⟨q, hqprime, hqk, h.2⟩
  · rintro (⟨p, hmem, hp⟩ | ⟨p, hp, hkp, h2p⟩)
    · exact quadRegimeOpen_of_mem_Icc_prime hq hp hmem
    · exact quadRegimeOpen_thin_of_prime_le_half hq (by omega) hp hkp h2p

/-- The packaged sufficient condition: a prime in the top block, or a
prime `p > k` with `2p ≤ n` (in the band), gives the conclusion. -/
theorem quadRegimeOpen_thin {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hn : n ≤ 3 * k)
    (h : (∃ p ∈ Finset.Icc (n + 1 - k) n, p.Prime) ∨
         (∃ p, p.Prime ∧ k < p ∧ 2 * p ≤ n)) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  (quadRegimeOpen_thin_iff hq hn).mpr h

/-- Contrapositive form: thin-band failure forces `(n-k, n]` to be
prime-free and `(k, n/2]` to be prime-free.  This is the exact
bookkeeping reduction of the thin band. -/
theorem quadRegimeOpen_thin_prime_free {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hn : n ≤ 3 * k)
    (hfail : ¬ ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k) :
    (∀ p ∈ Finset.Icc (n + 1 - k) n, ¬ p.Prime) ∧
      (∀ p, p.Prime → k < p → ¬ 2 * p ≤ n) := by
  rw [quadRegimeOpen_thin_iff hq hn] at hfail
  push Not at hfail
  obtain ⟨h1, h2⟩ := hfail
  exact ⟨h1, fun p hp hkp h2p ↦ by have h := h2 p hp hkp; omega⟩

/-- Smooth form of thin-band failure: every element of `(n-k, n]` has
all its prime factors `≤ k` (the consecutive-integers reformulation of
Sylvester–Schur; this direction needs no `3k` bound). -/
theorem quadRegimeOpen_thin_forall_prime_le {n k : ℕ} (_hq : QuadRegimeOpen n k)
    (hfail : ¬ ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k) :
    ∀ m ∈ Finset.Icc (n + 1 - k) n, ∀ p, p.Prime → p ∣ m → p ≤ k := by
  intro m hm p hp hpm
  by_contra hpk
  push Not at hpk
  exact hfail ⟨p, hp, hpk, dvd_choose_of_prime_dvd hp hpk hm hpm⟩

/-!
### The Bertrand reach
-/

/-- Bertrand's postulate with the composite endpoint removed: for
`x ≥ 2` there is a prime in `(x, 2x)` — `2x` is even and exceeds `2`,
hence composite.  This is the maximal reach of the bare statement. -/
theorem exists_prime_lt_and_lt_two_mul {x : ℕ} (hx : 2 ≤ x) :
    ∃ p, p.Prime ∧ x < p ∧ p < 2 * x := by
  obtain ⟨p, hp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul x (by omega)
  refine ⟨p, hp, hplt, ?_⟩
  rcases lt_or_eq_of_le hple with h | h
  · exact h
  · exfalso
    have h2dvd : 2 ∣ p := h ▸ dvd_mul_right 2 x
    rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h2 | h2 <;> omega

/-- **Bertrand reach.**  If `(k+1, n-k]` is prime-free, the Bertrand
prime `p ∈ (k+1, 2k+2]` satisfies `p > n - k`, hence lands in the top
block `(n-k, n]` (and `p ≤ 2k+2 ≤ n`).  This is the exact reach of one
Bertrand application in the band: for `n = 2k+2` the hypothesis is just
"`k+2` composite"; for `n = 2k+2+j` it is "`k+2, …, k+2+j` composite". -/
theorem quadRegimeOpen_thin_of_forall_not_prime {n k : ℕ}
    (hq : QuadRegimeOpen n k)
    (hfree : ∀ r, k + 1 < r → r ≤ n - k → ¬ r.Prime) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  obtain ⟨p, hp, hplt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (k + 1) (by omega)
  have hpgt : n - k < p := by
    by_contra hle
    push Not at hle
    exact hfree p hplt hle hp
  exact ⟨p, hp, by omega, dvd_choose_of_prime_dvd hp (by omega)
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (dvd_refl p)⟩

/-- Interval form of the Bertrand reach: `Icc (k+2) (n-k)` prime-free
suffices. -/
theorem quadRegimeOpen_thin_of_composite_Icc {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hcomp : ∀ r ∈ Finset.Icc (k + 2) (n - k), ¬ r.Prime) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  quadRegimeOpen_thin_of_forall_not_prime hq fun r h1 h2 ↦
    hcomp r (Finset.mem_Icc.mpr ⟨by omega, h2⟩)

/-- `n = 2k + 2` is closed whenever `k+1` is prime (then `2(k+1) = n` is
the distinguished top-block element) or `k+2` is composite (then the
Bertrand prime in `(k+1, 2k+2]` lands in `(k+2, 2k+2]`).  The leftover
case — `k+1` composite and `k+2` prime — is exactly "the least prime
exceeding `k+2` is `≤ 2k+2`", where Bertrand at `k+2` falls one short. -/
theorem quadRegimeOpen_thin_two_mul_add_two {n k : ℕ} (hq : QuadRegimeOpen n k)
    (hn : n = 2 * k + 2) (h : (k + 1).Prime ∨ ¬ (k + 2).Prime) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have hk38 : 38 ≤ k := hq.1
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  rcases h with hp | hcomp
  · exact quadRegimeOpen_thin_of_prime_le_half hq (by omega) hp (by omega) (by omega)
  · exact exists_prime_dvd_choose_of_eq (by omega) hn hcomp

/-!
### The conditional thin band
-/

/-- **Conditional thin band (prime-gap input).**  Any `(x, 3x/2]`-type
prime-gap theorem — `hgap x : ∃ p prime, x < p ∧ 2p ≤ 3x` for `x ≥ X₀` —
closes the whole thin band `n ≤ 3k` once `n - k ≥ X₀`: applied at
`x = n - k`, the prime satisfies `n - k < p` and `2p ≤ 3(n-k) ≤ 2n`
(since `n ≤ 3k` iff `3(n-k) ≤ 2n`), so `p ∈ (n-k, n]` and `p > k`. -/
theorem quadRegimeOpen_thin_of_prime_gap (X₀ : ℕ)
    (hgap : ∀ x : ℕ, X₀ ≤ x → ∃ p, p.Prime ∧ x < p ∧ 2 * p ≤ 3 * x)
    {n k : ℕ} (hq : QuadRegimeOpen n k) (hX : X₀ ≤ n - k) (hn : n ≤ 3 * k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  have h2k2 : 2 * k + 2 ≤ n := hq.2.1
  obtain ⟨p, hp, hplt, hp2⟩ := hgap (n - k) hX
  have hpn : p ≤ n := by omega
  exact ⟨p, hp, by omega, dvd_choose_of_prime_dvd hp (by omega)
    (Finset.mem_Icc.mpr ⟨by omega, hpn⟩) (dvd_refl p)⟩

end SylvesterSchur
