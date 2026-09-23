import JSP314.QuadEasy

/-!
# The linear-range part of the quadratic regime

This file discharges the portion `n ≥ 3·k` (for `k ≥ 2^26`) of the residual
quadratic regime `QuadRegimeOpen n k` of the Sylvester–Schur theorem, narrowing
the open set to a thin band `2k + 2 ≤ n < 3k` (for `k ≥ 2^26`).

## The bound (Erdős's iterated primorial)

Write `∏_{p ∈ primesLE k} p^{⌊log_p n⌋}` — the sharp upper bound for `C(n,k)`
when all its prime factors are `≤ k` (`choose_le_prod_pow_log`) — as a product
over levels `m`: `p^{⌊log_p n⌋} = ∏_{m < ⌊log_p n⌋} p`, so

    ∏_{p ≤ k} p^{⌊log_p n⌋} = ∏_{m < ⌊log₂ n⌋}  ∏_{p ≤ k, p^{m+1} ≤ n} p.

Each level set is contained in `primesLE B` for a bound `B`, so its product is
at most `primorial B ≤ 4^B` (`primorial_le_four_pow`):

* `m = 0`: `B = k` (the primes are given to be `≤ k`);
* `m = 1`: `p² ≤ n` gives `B = Nat.sqrt n`;
* `m ≥ 2`: `p^{m+1} ≤ n` gives `p³ ≤ n`, hence `3·⌊log₂ p⌋ ≤ ⌊log₂ n⌋` and
  `p < 2^{⌊log₂ n⌋/3 + 1}`.

Therefore

    C(n,k) ≤ ∏ p^{⌊log_p n⌋} ≤ 4^{k + √n + ⌊log₂ n⌋·2^{⌊log₂ n⌋/3 + 1}}
                                     ⎵⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯
                                                  E(n)

(`prod_pow_log_le_iterated`).  Since `n ≤ k²` in the quadratic regime, `E(n)`
is `o(k)` and `√n` is at most `k`; combined with the binomial lower bound
`4^k·n^k ≤ (2k+1)·(2k)^k·C(n,k)` (`four_pow_mul_pow_le`), the Sylvester–Schur
conclusion follows as soon as `(2k+1)·(2k)^k·4^{k+√n+E} < 4^k·n^k`
(`exists_prime_dvd_choose_of_iterated`), i.e. roughly `n > 2k·4^{(√n+E)/k}`.

## What is proved

* `quadRegimeOpen_of_linear`: for `38 ≤ k` with `2^{26} ≤ k` and `3k ≤ n ≤ k²`
  (the open regime), `C(n,k)` has a prime divisor `> k`.  For `n` in this range
  but with `400k³ ≤ n²` the result is already covered by
  `quadRegimeOpen_of_large_cubic`; for `n² < 400k³` we bound `√n + E(n) ≤ k/4`
  using `k < 2^{j+1}` where `j = ⌊log₂ k⌋ ≥ 26`, and then
  `(2k+1)·(2k)^k·4^{k+k/4} < 4^k·(3k)^k` follows from `(2k+1)²·8^k < 9^k`.

## Remaining residual

    38 ≤ k < 2^26, 2k+2 ≤ n ≤ k², n² < 400k³      (finite, infeasible to check)
    2^{26} ≤ k,     2k+2 ≤ n < 3k                  (the thin band near `n = 2k`)

The band near `2k` is the genuinely hard core: the constant `3` approaches the
limit `2` of this method (the factor `4^k` in the bound cancels the `4^k` in
`C(n,k) ≥ 4^k·(n/2k)^k/(2k+1)`, and what remains is `n/2k > 4^{o(1)}`).

No placeholder tactics; kernel-checkable.
-/

namespace SylvesterSchur

open Finset
open scoped Nat

/-!
### Auxiliary elementary lemmas
-/

/-- If `a² < b²` then `a < b` (for naturals). -/
theorem lt_of_sq_lt_sq {a b : ℕ} (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hc
  exact absurd h (not_lt_of_ge (Nat.pow_le_pow_left (not_lt.mp hc) 2))

/-- For `j ≥ 26`, `(2j - 7)³ ≤ 2^{j-7}`.  Base case `45³ = 91125 ≤ 524288`;
the step uses `(2j-5)·4 ≤ (2j-7)·5` so the cube grows by a factor `≤ 2`. -/
theorem cube_growth_aux {j : ℕ} (hj : 26 ≤ j) : (2 * j - 7) ^ 3 ≤ 2 ^ (j - 7) := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      have h45 : 4 * (2 * (j + 1) - 7) ≤ 5 * (2 * j - 7) := by omega
      have hc : (2 * (j + 1) - 7) ^ 3 ≤ 2 * (2 * j - 7) ^ 3 := by
        have h := Nat.pow_le_pow_left h45 3
        rw [mul_pow, mul_pow] at h
        norm_num at h
        -- h : 64 * (2(j+1)-7)^3 ≤ 125 * (2j-7)^3
        have h2 : (125 : ℕ) * (2 * j - 7) ^ 3 ≤ 64 * (2 * (2 * j - 7) ^ 3) := by
          calc 125 * (2 * j - 7) ^ 3 ≤ 128 * (2 * j - 7) ^ 3 :=
                Nat.mul_le_mul (by norm_num) (le_refl _)
            _ = 64 * (2 * (2 * j - 7) ^ 3) := by ring
        exact Nat.le_of_mul_le_mul_left (h.trans h2) (by norm_num)
      calc (2 * (j + 1) - 7) ^ 3 ≤ 2 * (2 * j - 7) ^ 3 := hc
        _ ≤ 2 * 2 ^ (j - 7) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ ((j + 1) - 7) := by
            rw [show (j + 1) - 7 = 1 + (j - 7) by omega, pow_add]
            norm_num

/-- For `j ≥ 26`, `2j - 7 ≤ 2^{(j-5)/3}` (take cube roots of `cube_growth_aux`;
the floor in the exponent costs a factor `2^{j-7} ≥ (2^{(j-5)/3})³`). -/
theorem dyadic_log_aux {j : ℕ} (hj : 26 ≤ j) : 2 * j - 7 ≤ 2 ^ ((j - 5) / 3) := by
  have h1 := cube_growth_aux hj
  have h2 : (2 * j - 7) ^ 3 ≤ (2 ^ ((j - 5) / 3)) ^ 3 := by
    refine h1.trans ?_
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp h2

/-- `(2k+1)²·8^k < 9^k` for `k ≥ 100`.  Base case `201²·8^100 < 9^100`;
the step uses `8·(2k+3)² ≤ 9·(2k+1)²`, i.e. `60k + 63 ≤ 4k²` for `k ≥ 17`. -/
theorem pow_growth_aux {k : ℕ} (hk : 100 ≤ k) : (2 * k + 1) ^ 2 * 8 ^ k < 9 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h4 : 60 * k + 63 ≤ 4 * k ^ 2 := by
        have h1 : (68 : ℕ) ≤ 4 * k := by omega
        have h2 : 68 * k ≤ 4 * k * k := Nat.mul_le_mul h1 (le_refl k)
        have h3 : 4 * k ^ 2 = 4 * k * k := by ring
        omega
      have h8 : 8 * (2 * (k + 1) + 1) ^ 2 ≤ 9 * (2 * k + 1) ^ 2 := by
        have e1 : 8 * (2 * (k + 1) + 1) ^ 2 = 32 * k ^ 2 + 96 * k + 72 := by ring
        have e2 : 9 * (2 * k + 1) ^ 2 = 36 * k ^ 2 + 36 * k + 9 := by ring
        omega
      calc (2 * (k + 1) + 1) ^ 2 * 8 ^ (k + 1)
          = (8 * (2 * (k + 1) + 1) ^ 2) * 8 ^ k := by ring
        _ ≤ (9 * (2 * k + 1) ^ 2) * 8 ^ k := Nat.mul_le_mul h8 (le_refl _)
        _ = 9 * ((2 * k + 1) ^ 2 * 8 ^ k) := by ring
        _ < 9 * 9 ^ k := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 9 ^ (k + 1) := (pow_succ' 9 k).symm

/-!
### Erdős's iterated-primorial bound
-/

/-- Swapping a power product into a product over level sets:
`∏ p ∈ s, p^{f p} = ∏_{m < B} ∏_{p ∈ s, m < f p} p`, valid when `f p ≤ B` on `s`
(each `p` then appears in exactly `f p` of the inner products). -/
theorem prod_pow_eq_prod_range {s : Finset ℕ} {f : ℕ → ℕ} {B : ℕ}
    (hB : ∀ p ∈ s, f p ≤ B) :
    ∏ p ∈ s, p ^ f p = ∏ m ∈ Finset.range B, ∏ p ∈ s.filter (fun p ↦ m < f p), p := by
  have hprod : ∀ p ∈ s, (∏ m ∈ Finset.range B, (if m < f p then p else 1)) = p ^ f p := by
    intro p hp
    have hfp : f p ≤ B := hB p hp
    rw [← Finset.prod_filter, Finset.prod_const]
    have hset : (Finset.range B).filter (fun m ↦ m < f p) = Finset.range (f p) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hset, Finset.card_range]
  calc ∏ p ∈ s, p ^ f p
      = ∏ p ∈ s, ∏ m ∈ Finset.range B, (if m < f p then p else 1) :=
        Finset.prod_congr rfl fun p hp ↦ (hprod p hp).symm
    _ = ∏ m ∈ Finset.range B, ∏ p ∈ s, (if m < f p then p else 1) := Finset.prod_comm
    _ = ∏ m ∈ Finset.range B, ∏ p ∈ s.filter (fun p ↦ m < f p), p :=
        Finset.prod_congr rfl fun m _ ↦ by rw [Finset.prod_filter]

/-- Level `m = 0`: the level set is contained in `primesLE k`, whose product is
`primorial k ≤ 4^k`. -/
theorem prod_log_level_zero {n k : ℕ} :
    ∏ p ∈ k.primesLE.filter (fun p ↦ 0 < p.log n), p ≤ 4 ^ k := by
  refine (Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    fun p hp _ ↦ (Nat.mem_primesLE.mp hp).2.one_lt.le).trans ?_
  rw [← primorial_eq_prod_primesLE]
  exact primorial_le_four_pow k

/-- Level `m = 1`: `1 < log_p n` means `p² ≤ n`, so the level set is contained in
`primesLE √n`, whose product is `≤ 4^{√n}`. -/
theorem prod_log_level_one {n k : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ k.primesLE.filter (fun p ↦ 1 < p.log n), p ≤ 4 ^ (Nat.sqrt n) := by
  have hsub : k.primesLE.filter (fun p ↦ 1 < p.log n) ⊆ (Nat.sqrt n).primesLE := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpL, h1⟩ := hp
    have hpp := (Nat.mem_primesLE.mp hpL).2
    have hp2 : p ^ 2 ≤ n := (Nat.le_log_iff_pow_le hpp.one_lt hn).mp h1
    exact Nat.mem_primesLE.mpr ⟨Nat.le_sqrt'.mpr hp2, hpp⟩
  refine (Finset.prod_le_prod_of_subset_of_one_le hsub
    fun p hp _ ↦ (Nat.mem_primesLE.mp hp).2.one_lt.le).trans ?_
  rw [← primorial_eq_prod_primesLE]
  exact primorial_le_four_pow _

/-- Level `m ≥ 2`: `m < log_p n` gives `p^{m+1} ≤ n`, hence `p³ ≤ n`,
`3·⌊log₂ p⌋ ≤ ⌊log₂ n⌋`, and `p < 2^{⌊log₂ n⌋/3 + 1}`.  The level set is thus
contained in `primesLE (2^{⌊log₂ n⌋/3+1})`, whose product is `≤ 4^{2^{…}}`. -/
theorem prod_log_level_high {n k m : ℕ} (hn : n ≠ 0) (hm : 2 ≤ m) :
    ∏ p ∈ k.primesLE.filter (fun p ↦ m < p.log n), p ≤
      4 ^ (2 ^ (Nat.log 2 n / 3 + 1)) := by
  have hsub : k.primesLE.filter (fun p ↦ m < p.log n) ⊆
      (2 ^ (Nat.log 2 n / 3 + 1)).primesLE := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpL, h1⟩ := hp
    have hpp := (Nat.mem_primesLE.mp hpL).2
    have hpm : p ^ (m + 1) ≤ n :=
      (Nat.le_log_iff_pow_le hpp.one_lt hn).mp (by omega)
    have hp3 : p ^ 3 ≤ n :=
      (Nat.pow_le_pow_right hpp.pos (by omega)).trans hpm
    have h3log : 3 * Nat.log 2 p ≤ Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc (2 : ℕ) ^ (3 * Nat.log 2 p) = (2 ^ Nat.log 2 p) ^ 3 := by
            rw [mul_comm 3, pow_mul]
        _ ≤ p ^ 3 := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hpp.ne_zero) 3
        _ ≤ n := hp3
    have hlt : p < 2 ^ (Nat.log 2 n / 3 + 1) :=
      (Nat.lt_pow_succ_log_self (by norm_num) p).trans_le
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact Nat.mem_primesLE.mpr ⟨hlt.le, hpp⟩
  refine (Finset.prod_le_prod_of_subset_of_one_le hsub
    fun p hp _ ↦ (Nat.mem_primesLE.mp hp).2.one_lt.le).trans ?_
  rw [← primorial_eq_prod_primesLE]
  exact primorial_le_four_pow _

/-- **Erdős's iterated-primorial bound**:
`∏_{p ≤ k} p^{⌊log_p n⌋} ≤ 4^{k + √n + E}` with
`E = ⌊log₂ n⌋ · 2^{⌊log₂ n⌋/3 + 1}`. -/
theorem prod_pow_log_le_iterated {n k : ℕ} (hn : n ≠ 0) (hL2 : 2 ≤ Nat.log 2 n) :
    ∏ p ∈ k.primesLE, p ^ p.log n ≤
      4 ^ (k + Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1)) := by
  have hB : ∀ p ∈ k.primesLE, p.log n ≤ Nat.log 2 n := fun p hp ↦
    Nat.log_anti_left (by norm_num) (Nat.two_le_of_mem_primesLE hp)
  rw [prod_pow_eq_prod_range hB]
  -- split `range L = {0,1} ∪ Ico 2 L`
  have hIco : (Finset.Ico 0 2 : Finset ℕ) = {0, 1} := by decide
  have hsplit : Finset.range (Nat.log 2 n) = {0, 1} ∪ Finset.Ico 2 (Nat.log 2 n) := by
    rw [Finset.range_eq_Ico, ← hIco]
    exact (Finset.Ico_union_Ico_eq_Ico (by norm_num) hL2).symm
  have hdis : Disjoint ({0, 1} : Finset ℕ) (Finset.Ico 2 (Nat.log 2 n)) := by
    rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hx ⊢
    omega
  rw [hsplit, Finset.prod_union hdis]
  · rw [Finset.prod_pair (by norm_num : (0 : ℕ) ≠ 1)]
    calc (∏ p ∈ k.primesLE.filter (fun p ↦ 0 < p.log n), p) *
          (∏ p ∈ k.primesLE.filter (fun p ↦ 1 < p.log n), p) *
          ∏ m ∈ Finset.Ico 2 (Nat.log 2 n),
            ∏ p ∈ k.primesLE.filter (fun p ↦ m < p.log n), p
        ≤ (4 ^ k * 4 ^ Nat.sqrt n) *
            ∏ m ∈ Finset.Ico 2 (Nat.log 2 n), 4 ^ (2 ^ (Nat.log 2 n / 3 + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul prod_log_level_zero (prod_log_level_one hn))
            (Finset.prod_le_prod fun m hm ↦
              prod_log_level_high hn (Finset.mem_Ico.mp hm).1)
      _ = (4 ^ k * 4 ^ Nat.sqrt n) * (4 ^ (2 ^ (Nat.log 2 n / 3 + 1))) ^ (Nat.log 2 n - 2) := by
          rw [Finset.prod_const, Nat.card_Ico]
      _ = 4 ^ (k + Nat.sqrt n + 2 ^ (Nat.log 2 n / 3 + 1) * (Nat.log 2 n - 2)) := by
          rw [← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 4 ^ (k + Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1)) := by
          apply Nat.pow_le_pow_right (by norm_num)
          have hmul : 2 ^ (Nat.log 2 n / 3 + 1) * (Nat.log 2 n - 2) ≤
              Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1) := by
            rw [mul_comm (2 ^ _) (Nat.log 2 n - 2)]
            exact Nat.mul_le_mul (Nat.sub_le _ _) (le_refl _)
          omega

/-- **Conditional Sylvester–Schur, iterated-bound form.**  If
`(2k+1)·(2k)^k·4^{k+√n+E(n)} < 4^k·n^k` then `C(n,k)` has a prime divisor
`> k`. -/
theorem exists_prime_dvd_choose_of_iterated {n k : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (h4 : 4 ≤ n)
    (hlt : (2 * k + 1) * (2 * k) ^ k *
        4 ^ (k + Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1)) < 4 ^ k * n ^ k) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  apply exists_prime_dvd_choose_of_smooth_prod_lt hk h2k
  have hn0 : n ≠ 0 := by omega
  have hL2 : 2 ≤ Nat.log 2 n := by
    have e : (2 : ℕ) ^ 2 ≤ n := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4
    exact Nat.le_log_of_pow_le (by norm_num) e
  have hb := prod_pow_log_le_iterated (k := k) hn0 hL2
  calc (2 * k + 1) * (2 * k) ^ k * ∏ p ∈ k.primesLE, p ^ p.log n
      ≤ (2 * k + 1) * (2 * k) ^ k *
          4 ^ (k + Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1)) :=
        Nat.mul_le_mul_left _ hb
    _ < 4 ^ k * n ^ k := hlt

/-!
### The explicit linear range `n ≥ 3k`, `k ≥ 2^26`
-/

/-- **Linear-range quadratic regime.**  For `k ≥ 2^{26}` and `n ≥ 3k` in the
open quadratic regime, `C(n,k)` has a prime divisor `> k`. -/
theorem quadRegimeOpen_of_linear (n k : ℕ) (hq : QuadRegimeOpen n k)
    (hk : 2 ^ 26 ≤ k) (hn3 : 3 * k ≤ n) :
    ∃ q, q.Prime ∧ k < q ∧ q ∣ n.choose k := by
  obtain ⟨hk38, h2k2, hnk2⟩ := hq
  rcases le_or_gt (400 * k ^ 3) (n ^ 2) with hcub | hcub
  · exact quadRegimeOpen_of_large_cubic ⟨hk38, h2k2, hnk2⟩ hcub
  · have hn0 : n ≠ 0 := by omega
    have hk0 : k ≠ 0 := by omega
    obtain ⟨j, hj26, h2j, hkj⟩ : ∃ j, 26 ≤ j ∧ 2 ^ j ≤ k ∧ k < 2 ^ (j + 1) :=
      ⟨Nat.log 2 k, Nat.le_log_of_pow_le (by norm_num) hk,
        Nat.pow_log_le_self 2 hk0, Nat.lt_pow_succ_log_self (by norm_num) k⟩
    -- `n² < 400k³ < 2^{3j+12} ≤ (2^{2j-6})²`, so `n < 2^{2j-6}`.
    have hn2 : n ^ 2 < 2 ^ (3 * j + 12) := by
      have h4 : k ^ 3 < 2 ^ (3 * j + 3) := by
        calc k ^ 3 < (2 ^ (j + 1)) ^ 3 := Nat.pow_lt_pow_left hkj (by norm_num)
          _ = 2 ^ (3 * j + 3) := by rw [← pow_mul]; congr 1; ring
      calc n ^ 2 < 400 * k ^ 3 := hcub
        _ < 400 * 2 ^ (3 * j + 3) := Nat.mul_lt_mul_of_pos_left h4 (by norm_num)
        _ ≤ 512 * 2 ^ (3 * j + 3) := Nat.mul_le_mul (by norm_num) (le_refl _)
        _ = 2 ^ (3 * j + 12) := by
            rw [show (512 : ℕ) = 2 ^ 9 by norm_num, ← pow_add]; congr 1; ring
    have hnlt : n < 2 ^ (2 * j - 6) := by
      apply lt_of_sq_lt_sq
      calc n ^ 2 < 2 ^ (3 * j + 12) := hn2
        _ ≤ 2 ^ ((2 * j - 6) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ (2 * j - 6)) ^ 2 := by rw [← pow_mul]
    -- `√n < 2^{j-3}` since `n < (2^{j-3})²`.
    have hsqrt : Nat.sqrt n < 2 ^ (j - 3) := by
      rw [Nat.sqrt_lt']
      calc n < 2 ^ (2 * j - 6) := hnlt
        _ = (2 ^ (j - 3)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    -- `L = ⌊log₂ n⌋ ≤ 2j - 7`.
    have hL : Nat.log 2 n ≤ 2 * j - 7 := by
      have h := Nat.log_lt_of_lt_pow hn0 hnlt
      omega
    -- `E = L·2^{L/3+1} ≤ 2^{j-3}`.
    have hB : 2 ^ (Nat.log 2 n / 3 + 1) ≤ 2 ^ ((2 * j - 7) / 3 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hE : Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1) ≤ 2 ^ (j - 3) := by
      calc Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1)
          ≤ (2 * j - 7) * 2 ^ ((2 * j - 7) / 3 + 1) := Nat.mul_le_mul hL hB
        _ = 2 * ((2 * j - 7) * 2 ^ ((2 * j - 7) / 3)) := by rw [pow_succ']; ring
        _ ≤ 2 * (2 ^ ((j - 5) / 3) * 2 ^ ((2 * j - 7) / 3)) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul (dyadic_log_aux hj26) (le_refl _)
        _ = 2 * 2 ^ ((j - 5) / 3 + (2 * j - 7) / 3) := by rw [pow_add]
        _ ≤ 2 * 2 ^ (j - 4) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ = 2 ^ (j - 3) := by
            rw [show j - 3 = 1 + (j - 4) by omega, pow_add]; norm_num
    -- Hence `√n + E ≤ k/4`.
    have hsum : Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1) ≤ k / 4 := by
      have h83 : 8 * 2 ^ (j - 3) ≤ k := by
        calc 8 * 2 ^ (j - 3) = 2 ^ 3 * 2 ^ (j - 3) := by norm_num
          _ = 2 ^ j := by rw [← pow_add]; congr 1; omega
          _ ≤ k := h2j
      omega
    -- It remains to show `(2k+1)·(2k)^k·4^{k+√n+E} < 4^k·n^k`.
    refine exists_prime_dvd_choose_of_iterated (by omega) (by omega) (by omega) ?_
    have hexp : (2 * k + 1) * (2 * k) ^ k *
          4 ^ (k + Nat.sqrt n + Nat.log 2 n * 2 ^ (Nat.log 2 n / 3 + 1))
        ≤ (2 * k + 1) * (2 * k) ^ k * 4 ^ (k + k / 4) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine hexp.trans_lt ?_
    have h3k : (3 * k) ^ k ≤ n ^ k := Nat.pow_le_pow_left hn3 k
    suffices h : (2 * k + 1) * (2 * k) ^ k * 4 ^ (k + k / 4) < 4 ^ k * (3 * k) ^ k from
      h.trans_le (Nat.mul_le_mul_left _ h3k)
    -- reduce to the "core" inequality `(2k+1)·2^k·4^{k/4} < 3^k`
    have core : (2 * k + 1) * 2 ^ k * 4 ^ (k / 4) < 3 ^ k := by
      have h4 : (4 : ℕ) ^ (k / 4) ≤ 2 ^ (k / 2) := by
        have e : (4 : ℕ) ^ (k / 4) = 2 ^ (2 * (k / 4)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
        rw [e]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hle : (2 * k + 1) * 2 ^ k * 4 ^ (k / 4) ≤ (2 * k + 1) * 2 ^ (k + k / 2) := by
        calc (2 * k + 1) * 2 ^ k * 4 ^ (k / 4)
            ≤ (2 * k + 1) * 2 ^ k * 2 ^ (k / 2) := Nat.mul_le_mul_left _ h4
          _ = (2 * k + 1) * 2 ^ (k + k / 2) := by rw [mul_assoc, ← pow_add]
      refine hle.trans_lt ?_
      apply lt_of_sq_lt_sq
      calc ((2 * k + 1) * 2 ^ (k + k / 2)) ^ 2
          = (2 * k + 1) ^ 2 * 2 ^ (2 * (k + k / 2)) := by
            rw [mul_pow, ← pow_mul]; congr 1; congr 1; ring
        _ ≤ (2 * k + 1) ^ 2 * 8 ^ k := by
            rw [show (8 : ℕ) ^ k = 2 ^ (3 * k) by rw [pow_mul]; norm_num]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 9 ^ k := pow_growth_aux (by omega)
        _ = (3 ^ k) ^ 2 := by
            rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [pow_add, mul_pow, mul_pow]
    calc (2 * k + 1) * (2 ^ k * k ^ k) * (4 ^ k * 4 ^ (k / 4))
        = ((2 * k + 1) * 2 ^ k * 4 ^ (k / 4)) * (4 ^ k * k ^ k) := by ring
      _ < 3 ^ k * (4 ^ k * k ^ k) := by
          have hpos : (0 : ℕ) < 4 ^ k * k ^ k := by positivity
          exact (Nat.mul_lt_mul_right hpos).mpr core
      _ = 4 ^ k * (3 ^ k * k ^ k) := by ring

end SylvesterSchur
