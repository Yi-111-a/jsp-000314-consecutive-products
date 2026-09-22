import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting

/-!
# JSP-000314 recon scratch — cardinality bound for smooth numbers in intervals

Recon findings used here (Mathlib v4.34.0):

* `Nat.smoothNumbers n` = positive naturals all of whose prime factors are
  **strictly less than** `n`  (`Mathlib/NumberTheory/SmoothNumbers.lean`).
  So "P-smooth" in the `≤` sense is `Nat.smoothNumbers (P + 1)`.
* `Nat.smoothNumbersUpTo N k : Finset ℕ` = `{n ∈ Finset.range (N+1) | n ∈ smoothNumbers k}`.
* `Nat.smoothNumbersUpTo_card_le : #(smoothNumbersUpTo N k) ≤ 2 ^ #k.primesBelow * N.sqrt`
  (squareful kernel trick: `n = m² · ∏ distinct primes`).
* `Nat.primesBelow_card_eq_primeCounting' : #n.primesBelow = π' n`, and
  `π k = π' (k + 1)` by definition.

Proved below: the number of `n ∈ [a, b]` all of whose prime divisors are `≤ k`
is at most `2 ^ π k * √ b`.  This is the *only* smooth-count bound in Mathlib;
note it is `≥ √b`, so it can never directly bound a *run* of length `≥ P`
below `P`-smooth density — the type-2 regime needs Tao's analytic input.
-/

open Nat Finset

namespace JSP314.Recon

/-- `k`-smoothness in the `≤` sense: membership in `Nat.smoothNumbers (k + 1)`
is equivalent to "every prime divisor is `≤ k`".  (`m = 0` is excluded
automatically, since every prime divides `0` and primes are unbounded.) -/
theorem mem_smoothNumbers_succ_iff_forall_prime_dvd_le {m k : ℕ} :
    m ∈ Nat.smoothNumbers (k + 1) ↔ ∀ p : ℕ, p.Prime → p ∣ m → p ≤ k := by
  rw [Nat.mem_smoothNumbers']
  exact forall_congr' fun p ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ Nat.lt_add_one_iff

/-- The `≤ k`-smooth numbers in `[a, b]` number at most `2 ^ π k * √ b`. -/
theorem card_Icc_smooth_le (a b k : ℕ) :
    ((Finset.Icc a b).filter fun n ↦ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ k).card
      ≤ 2 ^ Nat.primeCounting k * Nat.sqrt b := by
  have hsub : (Finset.Icc a b).filter (fun n ↦ ∀ p : ℕ, p.Prime → p ∣ n → p ≤ k)
      ⊆ Nat.smoothNumbersUpTo b (k + 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mem_smoothNumbersUpTo]
    exact ⟨(Finset.mem_Icc.mp hn.1).2,
      mem_smoothNumbers_succ_iff_forall_prime_dvd_le.mpr hn.2⟩
  refine (Finset.card_le_card hsub).trans <|
    (Nat.smoothNumbersUpTo_card_le b (k + 1)).trans ?_
  -- `#(k+1).primesBelow = π' (k+1) = π k` definitionally.
  rw [Nat.primesBelow_card_eq_primeCounting']

end JSP314.Recon
