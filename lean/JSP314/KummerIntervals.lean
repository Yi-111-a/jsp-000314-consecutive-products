import Mathlib

/-!
# Primes in intervals divide binomial coefficients

Clean "prime in interval ⟹ divides `n.choose k`" lemmas, for use in the
residual quadratic regime `QuadRegimeOpen n k` of the Sylvester–Schur
proof.

## Mathematical background

For a prime `p > k`, Kummer's theorem (`padicValNat_choose`) says that
`padicValNat p (n.choose k)` counts the carries when `k` and `n - k` are
added in base `p`; in particular `p ∣ n.choose k` as soon as
`p ≤ k % p + (n - k) % p`.

* `prime_dvd_choose_of_mem_Ioc_one`: if `p ∈ (n - k, n]` is prime and
  `2 * k ≤ n`, then `p ∣ n.choose k`.  Proved directly via
  `Nat.Prime.dvd_choose`.
* `prime_dvd_choose_of_mem_Ioc`: the general version — if
  `p ∈ ((n - k) / j, n / j]` (i.e. `n - k < j * p ≤ n`) for some `j ≥ 1`
  and `k < p`, then `p ∣ n.choose k`.  Write `n = j * p + r` with
  `r = n - j * p < k < p`; then `k % p = k` and
  `n - k = (j - 1) * p + (p + r - k)` gives `(n - k) % p = p + r - k`,
  so `k % p + (n - k) % p = p + r ≥ p` — a carry occurs.
* `prime_dvd_choose_of_mem_Ioc_two`: the case `j = 2`, where `k < p`
  follows automatically from `3 * k ≤ n`.
* `exists_prime_dvd_choose_of_prime_mem_Ioc_one/two`: the same
  statements packaged as the Sylvester–Schur goal
  `∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k`.
-/

/-- **Case `j = 1`.** A prime `p` with `n - k < p ≤ n` divides `n.choose k`
whenever `2 * k ≤ n` (which gives `k ≤ n - k < p`). -/
theorem prime_dvd_choose_of_mem_Ioc_one {n k p : ℕ} (hp : p.Prime) (hk : 2 * k ≤ n)
    (h : n - k < p ∧ p ≤ n) : p ∣ n.choose k :=
  hp.dvd_choose (lt_of_le_of_lt (by omega) h.1) h.1 h.2

/-- **General interval version.** If `p` is prime, `k < p`, and
`n - k < j * p ≤ n` for some `j ≥ 1`, then adding `k` and `n - k` in base
`p` produces a carry in the units digit, hence `p ∣ n.choose k`. -/
theorem prime_dvd_choose_of_mem_Ioc {n k p j : ℕ} (hp : p.Prime) (hkp : k < p)
    (h : n - k < j * p ∧ j * p ≤ n) : p ∣ n.choose k := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlt, hle⟩ := h
  -- `j ≥ 1` is forced by `n - k < j * p`.
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · simp [h0] at hlt
    · exact h0
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [add_mul, one_mul] at hlt hle
  -- Now `n - k < m * p + p` and `m * p + p ≤ n`; `m * p` is an atom for `omega`.
  have hdec : n - k = (p + (n - (m * p + p)) - k) + m * p := by omega
  have hs_lt : p + (n - (m * p + p)) - k < p := by omega
  have hmod : (n - k) % p = p + (n - (m * p + p)) - k := by
    rw [hdec, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs_lt]
  have hkmod : k % p = k := Nat.mod_eq_of_lt hkp
  have hkn : k ≤ n := by omega
  have hlog : Nat.log p n < n + 1 :=
    lt_of_le_of_lt (Nat.log_le_self p n) (Nat.lt_succ_self n)
  apply dvd_of_one_le_padicValNat
  rw [padicValNat_choose hkn hlog]
  have hmem : 1 ∈ {i ∈ Finset.Ico 1 (n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨le_refl 1, by have h2 := hp.two_le; omega⟩, by
        simp only [pow_one, hkmod, hmod]
        omega⟩
  have hpos := Finset.card_pos.mpr ⟨1, hmem⟩
  omega

/-- **Case `j = 2`.** A prime `p` with `n - k < 2 * p ≤ n` divides
`n.choose k` whenever `3 * k ≤ n` (which gives `2 * k ≤ n - k < 2 * p`,
hence `k < p`). -/
theorem prime_dvd_choose_of_mem_Ioc_two {n k p : ℕ} (hp : p.Prime) (hn : 3 * k ≤ n)
    (h : n - k < 2 * p ∧ 2 * p ≤ n) : p ∣ n.choose k := by
  have hkp : k < p := by omega
  exact prime_dvd_choose_of_mem_Ioc hp hkp (j := 2) h

/-- Sylvester–Schur packaged form of `prime_dvd_choose_of_mem_Ioc_one`. -/
theorem exists_prime_dvd_choose_of_prime_mem_Ioc_one {n k p : ℕ} (hp : p.Prime)
    (hk : 2 * k ≤ n) (h : n - k < p ∧ p ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  ⟨p, hp, lt_of_le_of_lt (by omega) h.1, prime_dvd_choose_of_mem_Ioc_one hp hk h⟩

/-- Sylvester–Schur packaged form of `prime_dvd_choose_of_mem_Ioc_two`. -/
theorem exists_prime_dvd_choose_of_prime_mem_Ioc_two {n k p : ℕ} (hp : p.Prime)
    (hn : 3 * k ≤ n) (h : n - k < 2 * p ∧ 2 * p ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k :=
  ⟨p, hp, by omega, prime_dvd_choose_of_mem_Ioc_two hp hn h⟩
