import Mathlib

/-!
# Axiom-free finite verification for Sylvester–Schur

This file replaces the native-code `decide` proofs of `sylvesterSchur_check_small`
and `sylvesterSchur_check_mid` (in `attempts/aux/SylvesterSchur.lean`) by
kernel-checked proofs.

Idea: for `q` prime with `k < q ≤ n`, the largest multiple of `q` that is
`≤ n` is `m = n - n % q`, and `m ∈ (n - k, n]` iff `n % q < k`. So a bounded
search `findWit` over a fixed list of small primes suffices; its correctness is
proved once (`findWit_spec`), and the finite domain is exhausted by a single
kernel `decide` over the decidable proposition
`∀ n ∈ List.Icc …, ∀ k ∈ List.Icc …, …`.
-/

namespace SSCheck

/-- The primes `≤ 210` (the bound `n` in the mid-range check). -/
def primesLE210 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

set_option maxRecDepth 10000 in
/-- Every entry of `primesLE210` is prime (finite kernel check). -/
theorem primesLE210_prime : ∀ q ∈ primesLE210, q.Prime := by
  decide

/-- Search for a prime `q` with `k < q ≤ n` and `n % q < k`; returns
`(n - n % q, q)`. The returned `m = n - n % q` is a multiple of `q` lying in
`(n - k, n]`. -/
def findWit (n k : ℕ) : Option (ℕ × ℕ) :=
  (primesLE210.find? fun q =>
    decide (k < q) && decide (q ≤ n) && decide (n % q < k)).map
    fun q => (n - n % q, q)

/-- Correctness of `findWit`: any returned pair is a valid witness. -/
theorem findWit_spec {n k m q : ℕ} (h : findWit n k = some (m, q)) :
    m ∈ Finset.Icc (n + 1 - k) n ∧ q ∈ Finset.Icc (k + 1) m ∧
      q.Prime ∧ q ∣ m := by
  unfold findWit at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q', hq', hpair⟩ := h
  obtain ⟨hm, hq⟩ := Prod.mk.inj_iff.mp hpair
  subst hm
  subst hq
  have hcond := List.find?_some hq'
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcond
  obtain ⟨⟨hkg, hqn⟩, hlt⟩ := hcond
  have hkg : k < q' := of_decide_eq_true hkg
  have hqn : q' ≤ n := of_decide_eq_true hqn
  have hlt : n % q' < k := of_decide_eq_true hlt
  have hp : q'.Prime :=
    primesLE210_prime q' (List.mem_of_find?_eq_some hq')
  have hqpos : 0 < q' := by omega
  have hmodq : n % q' < q' := Nat.mod_lt _ hqpos
  have hdivpos : 1 ≤ n / q' := Nat.div_pos hqn hqpos
  have hmq : n - n % q' = q' * (n / q') := by
    have h1 := Nat.mod_add_div n q'
    omega
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩,
    Finset.mem_Icc.mpr ⟨by omega, ?_⟩, hp, ⟨n / q', hmq⟩⟩
  calc q' = q' * 1 := (Nat.mul_one q').symm
    _ ≤ q' * (n / q') := Nat.mul_le_mul_left q' hdivpos
    _ = n - n % q' := hmq.symm

set_option maxRecDepth 10000 in
/-- Finite check, `k ≤ 7`, `n ≤ 93`, proved by kernel `decide`. -/
theorem sylvesterSchur_check_small :
    ∀ n ∈ Finset.Icc 2 93, ∀ k ∈ Finset.Icc 1 7,
      2 * k ≤ n → ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q ∈ Finset.Icc (k + 1) m,
        q.Prime ∧ q ∣ m := by
  have key : ∀ n ∈ Finset.Icc 2 93, ∀ k ∈ Finset.Icc 1 7,
      2 * k ≤ n → (findWit n k).isSome := by
    decide
  intro n hn k hk h2k
  obtain ⟨⟨m, q⟩, hsome⟩ := Option.isSome_iff_exists.mp (key n hn k hk h2k)
  obtain ⟨hm, hq, hp, hd⟩ := findWit_spec hsome
  exact ⟨m, hm, q, hq, hp, hd⟩

set_option maxRecDepth 10000 in
/-- Finite check, `8 ≤ k ≤ 37`, `n ≤ 210`, proved by kernel `decide`. -/
theorem sylvesterSchur_check_mid :
    ∀ n ∈ Finset.Icc 16 210, ∀ k ∈ Finset.Icc 8 37,
      2 * k ≤ n → ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q ∈ Finset.Icc (k + 1) m,
        q.Prime ∧ q ∣ m := by
  have key : ∀ n ∈ Finset.Icc 16 210, ∀ k ∈ Finset.Icc 8 37,
      2 * k ≤ n → (findWit n k).isSome := by
    decide
  intro n hn k hk h2k
  obtain ⟨⟨m, q⟩, hsome⟩ := Option.isSome_iff_exists.mp (key n hn k hk h2k)
  obtain ⟨hm, hq, hp, hd⟩ := findWit_spec hsome
  exact ⟨m, hm, q, hq, hp, hd⟩

end SSCheck
