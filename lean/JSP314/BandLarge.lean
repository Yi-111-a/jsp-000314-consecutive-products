import JSP314.BandSum
import Mathlib.Tactic

/-!
# JSP-000314 — the large-`p` band of `runCountSum`

This file bounds the part of `runCountSum x` coming from primes `p` with
`p^4 > 2x` (the "large" band, i.e. `p > (2x)^{1/4}`).  Writing
`T_k(p) = rightRunCount x p k + leftRunCount x p k`, the inner `k`-sum is
split at `H₀ = ⌈x^{1/5}⌉`:

* `k < H₀` (`bandLargeLo`): the trivial per-cell bound
  `T_k ≤ 2·(2x/p²)` (`rightRunCount_le_div`, `leftRunCount_le_div`) gives
  `≤ H₀ · 4x · ∑_{p > (2x)^{1/4}} p⁻² ≲ 16·x^{19/20}`
  (`bandLarge_lo_le`, an unconditional eventually bound);
* `k ≥ H₀` (`bandLargeHi`): monotonicity `T_k ≤ T_{H₀}`
  (`rightRunCount_anti`, `leftRunCount_anti`) reduces the sum to
  `2p·T_{H₀}` (`bandLargeHi_le`); the required smooth-run rarity bound is
  supplied as a hypothesis in `bandLargeCount_le_of_hi_le` and
  `bandLargeCount_le_of_run_bound`.

Also proved: the Bertrand cutoff `T_k = 0` whenever a prime lies in
`(p, k]` (`rightRunCount_eq_zero_of_prime_between`,
`leftRunCount_eq_zero_of_prime_between`), with the corollary
`rightRunCount_eq_zero_of_two_mul_le` / `leftRunCount_eq_zero_of_two_mul_le`
(`T_k = 0` for `k ≥ 2p`).
-/

namespace JSP314

open Filter

/-- Auxiliary: a number whose largest prime factor is the prime `p` is
at least `2`. -/
theorem two_le_of_largestPrimeFactor_eq_prime {p m : ℕ} (hp : p.Prime)
    (h : largestPrimeFactor m = p) : 2 ≤ m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have h1 : largestPrimeFactor m = 1 :=
      largestPrimeFactor_eq_one_iff.mpr (by omega)
    have h2 := hp.two_le
    omega
  · exact hm

/-! ## Monotonicity in the run length -/

theorem rightRunWitness_anti {x p k l : ℕ} (h : l ≤ k) :
    rightRunWitness x p k ⊆ rightRunWitness x p l := by
  intro m hm
  rw [mem_rightRunWitness] at hm ⊢
  obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
  refine ⟨hm2x, hpdvd, hlpf, ?_⟩
  intro j hj
  apply harc
  rw [Finset.mem_Icc] at hj ⊢
  omega

/-- A run of `k` consecutive `p`-smooth numbers contains its first `l`
for `l ≤ k`: `rightRunCount` is antitone in `k`. -/
theorem rightRunCount_anti {x p k l : ℕ} (h : l ≤ k) :
    rightRunCount x p k ≤ rightRunCount x p l :=
  Finset.card_le_card (rightRunWitness_anti h)

theorem leftRunWitness_anti {x p k l : ℕ} (h : l ≤ k) :
    leftRunWitness x p k ⊆ leftRunWitness x p l := by
  intro m hm
  rw [mem_leftRunWitness] at hm ⊢
  obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
  refine ⟨hm2x, hpdvd, hlpf, ?_⟩
  intro j hj
  apply harc
  rw [Finset.mem_Icc] at hj ⊢
  have hmk : m - k ≤ m - l := Nat.sub_le_sub_left h m
  omega

/-- `leftRunCount` is antitone in `k`. -/
theorem leftRunCount_anti {x p k l : ℕ} (h : l ≤ k) :
    leftRunCount x p k ≤ leftRunCount x p l :=
  Finset.card_le_card (leftRunWitness_anti h)

/-! ## Bertrand cutoff: `T_k = 0` when a prime lies in `(p, k]` -/

/-- If a prime `q` satisfies `p < q ≤ k`, there are no right run witnesses:
among `m + 1, …, m + q` some `m + j` is divisible by `q`, forcing
`largestPrimeFactor (m + j) ≥ q > p`. -/
theorem rightRunCount_eq_zero_of_prime_between {x p k q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hqk : q ≤ k) :
    rightRunCount x p k = 0 := by
  rw [rightRunCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
  have hq0 : 0 < q := hq.pos
  have hm2 : 2 ≤ m := two_le_of_largestPrimeFactor_eq_prime hp hlpf
  set j := q - m % q with hjdef
  have hmod : m % q < q := Nat.mod_lt m hq0
  have hj1 : 1 ≤ j := by omega
  have hjq : j ≤ q := by omega
  have hdvd : q ∣ m + j := by
    rcases eq_or_ne (m % q) 0 with hmz | hmz
    · have hjq : j = q := by rw [hjdef, hmz, Nat.sub_zero]
      rw [hjq]
      exact dvd_add (Nat.dvd_of_mod_eq_zero hmz) (dvd_refl q)
    · have hpos : 0 < m % q := Nat.pos_of_ne_zero hmz
      have hle : m % q ≤ m := Nat.mod_le m q
      have h1 : m + j = m - m % q + q := by omega
      rw [h1]
      apply dvd_add _ (dvd_refl q)
      refine ⟨m / q, ?_⟩
      have hdm := Nat.div_add_mod m q
      omega
  have hmem : m + j ∈ Finset.Icc (m + 1) (m + k) := by
    rw [Finset.mem_Icc]
    omega
  have hle := harc (m + j) hmem
  have hqle :=
    prime_dvd_le_largestPrimeFactor (by omega : 2 ≤ m + j) hq hdvd
  omega

/-- If a prime `q` satisfies `p < q ≤ k` and `q ≤ p²`, there are no left run
witnesses: `q ≤ p² ≤ m` and `m ≠ q` (`p² ∤ q`), so `q ≤ m - 1` and some
multiple `j` of `q` lies in `{m - q, …, m - 1} ⊆ {m - k, …, m - 1}` with
`j ≥ q ≥ 2`, forcing `largestPrimeFactor j ≥ q > p`. -/
theorem leftRunCount_eq_zero_of_prime_between {x p k q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hqk : q ≤ k) (hq2 : q ≤ p ^ 2) :
    leftRunCount x p k = 0 := by
  rw [leftRunCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hpdvd, hlpf, harc⟩ := hm
  have hq0 : 0 < q := hq.pos
  have hm2 : 2 ≤ m := two_le_of_largestPrimeFactor_eq_prime hp hlpf
  have hp2m : p ^ 2 ≤ m := Nat.le_of_dvd (by omega) hpdvd
  have hqm : q < m := by
    rcases lt_or_eq_of_le (hq2.trans hp2m) with h | h
    · exact h
    · subst h
      rcases (Nat.dvd_prime hq).mp hpdvd with h1 | h1
      · have h2 := hp.two_le
        nlinarith
      · have hd : p ∣ q := by
          rw [← h1]
          exact ⟨p, by ring⟩
        rcases (Nat.dvd_prime hq).mp hd with h2 | h2
        · have := hp.two_le
          omega
        · omega
  have hq1 : q ≤ m - 1 := by omega
  set j := q * ((m - 1) / q) with hjdef
  have hdiv1 : 1 ≤ (m - 1) / q := by
    rw [Nat.le_div_iff_mul_le hq0]
    omega
  have hjge : q ≤ j := by
    calc q = q * 1 := by ring
      _ ≤ q * ((m - 1) / q) := Nat.mul_le_mul_left q hdiv1
  have hjle : j ≤ m - 1 := Nat.mul_div_le _ _
  have hjlo : m - k ≤ j := by
    have hdm := Nat.div_add_mod (m - 1) q
    have hmod : (m - 1) % q < q := Nat.mod_lt _ hq0
    omega
  have hmem : j ∈ Finset.Icc (m - k) (m - 1) :=
    Finset.mem_Icc.mpr ⟨hjlo, hjle⟩
  have hle := harc j hmem
  have hqle := prime_dvd_le_largestPrimeFactor (hq.two_le.trans hjge) hq
    (dvd_mul_right q _)
  omega

/-- Bertrand corollary: `rightRunCount x p k = 0` for `k ≥ 2p`. -/
theorem rightRunCount_eq_zero_of_two_mul_le {x p k : ℕ} (hp : p.Prime)
    (hk : 2 * p ≤ k) : rightRunCount x p k = 0 := by
  obtain ⟨q, hq, hpq, hq2p⟩ := Nat.bertrand p hp.ne_zero
  exact rightRunCount_eq_zero_of_prime_between hp hq hpq (hq2p.trans hk)

/-- Bertrand corollary: `leftRunCount x p k = 0` for `k ≥ 2p`. -/
theorem leftRunCount_eq_zero_of_two_mul_le {x p k : ℕ} (hp : p.Prime)
    (hk : 2 * p ≤ k) : leftRunCount x p k = 0 := by
  obtain ⟨q, hq, hpq, hq2p⟩ := Nat.bertrand p hp.ne_zero
  have hq2 : q ≤ p ^ 2 := by
    have h2 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp.two_le
    have h3 : p * p = p ^ 2 := by ring
    omega
  exact leftRunCount_eq_zero_of_prime_between hp hq hpq (hq2p.trans hk) hq2

/-! ## Per-cell trivial bound -/

/-- `rightRunCount x p k ≤ 2x / p²`: witnesses `m` are nonzero multiples of
`p²` below `2x`, and `m ↦ m / p²` is injective on them. -/
theorem rightRunCount_le_div (x p k : ℕ) (hp : p.Prime) :
    rightRunCount x p k ≤ 2 * x / p ^ 2 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hmaps : Set.MapsTo (· / p ^ 2) (↑(rightRunWitness x p k) : Set ℕ)
      (↑(Finset.Icc 1 (2 * x / p ^ 2)) : Set ℕ) := by
    intro m hm
    rw [Finset.mem_coe, mem_rightRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, -⟩ := hm
    have hmpos : 0 < m := by
      have := two_le_of_largestPrimeFactor_eq_prime hp hlpf
      omega
    have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hpdvd
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hm2x⟩
    rw [Nat.le_div_iff_mul_le hp2]
    rwa [one_mul]
  have hinj : Set.InjOn (· / p ^ 2) (↑(rightRunWitness x p k) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_rightRunWitness] at ha hb
    have h1 := Nat.div_mul_cancel ha.2.1
    have h2 := Nat.div_mul_cancel hb.2.1
    calc a = a / p ^ 2 * p ^ 2 := h1.symm
      _ = b / p ^ 2 * p ^ 2 := by rw [hab]
      _ = b := h2
  calc rightRunCount x p k = (rightRunWitness x p k).card := rfl
    _ ≤ (Finset.Icc 1 (2 * x / p ^ 2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 * x / p ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-- `leftRunCount x p k ≤ 2x / p²`. -/
theorem leftRunCount_le_div (x p k : ℕ) (hp : p.Prime) :
    leftRunCount x p k ≤ 2 * x / p ^ 2 := by
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hmaps : Set.MapsTo (· / p ^ 2) (↑(leftRunWitness x p k) : Set ℕ)
      (↑(Finset.Icc 1 (2 * x / p ^ 2)) : Set ℕ) := by
    intro m hm
    rw [Finset.mem_coe, mem_leftRunWitness] at hm
    obtain ⟨hm2x, hpdvd, hlpf, -⟩ := hm
    have hmpos : 0 < m := by
      have := two_le_of_largestPrimeFactor_eq_prime hp hlpf
      omega
    have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hmpos hpdvd
    rw [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hm2x⟩
    rw [Nat.le_div_iff_mul_le hp2]
    rwa [one_mul]
  have hinj : Set.InjOn (· / p ^ 2) (↑(leftRunWitness x p k) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, mem_leftRunWitness] at ha hb
    have h1 := Nat.div_mul_cancel ha.2.1
    have h2 := Nat.div_mul_cancel hb.2.1
    calc a = a / p ^ 2 * p ^ 2 := h1.symm
      _ = b / p ^ 2 * p ^ 2 := by rw [hab]
      _ = b := h2
  calc leftRunCount x p k = (leftRunWitness x p k).card := rfl
    _ ≤ (Finset.Icc 1 (2 * x / p ^ 2)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = 2 * x / p ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-! ## The band split -/

/-- `H₀`, the run-length split point: `⌈x^{1/5}⌉`. -/
noncomputable def runSplitH (x : ℕ) : ℕ := ⌈(x : ℝ) ^ (1 / 5 : ℝ)⌉₊

/-- The large-`p` part of `runCountSum`: the sum over primes `p ≤ √(2x)`
with `p⁴ > 2x` of `∑_{k ≤ 2p} (rightRunCount + leftRunCount)`. -/
noncomputable def bandLargeCount (x : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
    ∑ k ∈ Finset.Icc 1 (2 * p), (rightRunCount x p k + leftRunCount x p k)

/-- The `k < H₀` part of `bandLargeCount`. -/
noncomputable def bandLargeLo (x : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
    ∑ k ∈ (Finset.Icc 1 (2 * p)).filter (· < runSplitH x),
      (rightRunCount x p k + leftRunCount x p k)

/-- The `k ≥ H₀` part of `bandLargeCount`. -/
noncomputable def bandLargeHi (x : ℕ) : ℕ :=
  ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
    ∑ k ∈ (Finset.Icc 1 (2 * p)).filter (fun k => runSplitH x ≤ k),
      (rightRunCount x p k + leftRunCount x p k)

/-- `bandLargeCount` splits at `H₀`. -/
theorem bandLargeCount_eq_lo_add_hi (x : ℕ) :
    bandLargeCount x = bandLargeLo x + bandLargeHi x := by
  classical
  unfold bandLargeCount bandLargeLo bandLargeHi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hge : (Finset.Icc 1 (2 * p)).filter (fun k => runSplitH x ≤ k) =
      (Finset.Icc 1 (2 * p)).filter (fun k => ¬ k < runSplitH x) :=
    Finset.filter_congr fun k _ => propext not_lt.symm
  rw [hge]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ## The `k < H₀` bound -/

/-- `bandLargeLo` is at most `H₀` times the per-cell bound summed over the
band primes. -/
theorem bandLargeLo_le_aux (x : ℕ) :
    bandLargeLo x ≤ runSplitH x *
      ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
        (2 * (2 * x / p ^ 2)) := by
  unfold bandLargeLo
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1
  have hcard :
      ((Finset.Icc 1 (2 * p)).filter (· < runSplitH x)).card ≤ runSplitH x := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_range _)
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range]
    exact hk.2
  calc ∑ k ∈ (Finset.Icc 1 (2 * p)).filter (· < runSplitH x),
        (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ _k ∈ (Finset.Icc 1 (2 * p)).filter (· < runSplitH x),
          2 * (2 * x / p ^ 2) := by
        apply Finset.sum_le_sum
        intro k _
        have h1 := rightRunCount_le_div x p k hpp
        have h2 := leftRunCount_le_div x p k hpp
        omega
    _ = ((Finset.Icc 1 (2 * p)).filter (· < runSplitH x)).card *
          (2 * (2 * x / p ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ runSplitH x * (2 * (2 * x / p ^ 2)) :=
        Nat.mul_le_mul hcard le_rfl

/-- The band primes `p` with `p⁴ > 2x` satisfy `√(√(2x)) < p ≤ √(2x)`. -/
theorem bandLargePrimes_subset_Ico (x : ℕ) :
    (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4)
      ⊆ Finset.Ico (Nat.sqrt (Nat.sqrt (2 * x)) + 1) (Nat.sqrt (2 * x) + 1) := by
  intro p hp
  rw [Finset.mem_filter, Nat.mem_primesLE] at hp
  obtain ⟨⟨hp2x, -⟩, hp4⟩ := hp
  rw [Finset.mem_Ico]
  refine ⟨?_, Nat.lt_succ_iff.mpr hp2x⟩
  have h1 : Nat.sqrt (Nat.sqrt (2 * x)) < p :=
    Nat.sqrt_lt.mpr (Nat.sqrt_lt.mpr (by
      have h : p * p * (p * p) = p ^ 4 := by ring
      rwa [h]))
  omega

/-- Telescoping: `∑_{n = B+1}^{N} 1/n² ≤ 1/B` for `B ≥ 1`. -/
theorem sum_one_div_sq_Ico_le {B : ℕ} (hB : 1 ≤ B) (N : ℕ) :
    ∑ n ∈ Finset.Ico (B + 1) (N + 1), (1 : ℝ) / n ^ 2 ≤ 1 / B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  calc ∑ n ∈ Finset.Ico (B + 1) (N + 1), (1 : ℝ) / n ^ 2
      = ∑ i ∈ Finset.range (N + 1 - (B + 1)),
          (1 : ℝ) / ((B + 1 + i : ℕ) : ℝ) ^ 2 :=
        Finset.sum_Ico_eq_sum_range _ _ _
    _ ≤ ∑ i ∈ Finset.range (N + 1 - (B + 1)),
          ((1 : ℝ) / ((B + i : ℕ) : ℝ) - 1 / ((B + (i + 1) : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        have ha : ((B + i : ℕ) : ℝ) = (B : ℝ) + i := Nat.cast_add B i
        have hc : ((B + (i + 1) : ℕ) : ℝ) = ((B + i : ℕ) : ℝ) + 1 := by
          rw [ha]
          push_cast
          ring
        have hc' : ((B + 1 + i : ℕ) : ℝ) = ((B + i : ℕ) : ℝ) + 1 := by
          rw [ha]
          push_cast
          ring
        rw [hc', hc]
        set a : ℝ := ((B + i : ℕ) : ℝ) with ha'
        have ha0 : (0 : ℝ) < a := by
          rw [ha']
          exact_mod_cast Nat.add_pos_left (by omega : 0 < B) i
        have ha1 : (0 : ℝ) < a + 1 := by linarith
        rw [show (1 : ℝ) / a - 1 / (a + 1) = 1 / (a * (a + 1)) by
          field_simp
          ring]
        apply one_div_le_one_div_of_le (mul_pos ha0 ha1)
        exact mul_le_mul (by linarith) le_rfl ha1.le ha1.le
    _ = (1 : ℝ) / ((B + 0 : ℕ) : ℝ) -
          1 / ((B + (N + 1 - (B + 1)) : ℕ) : ℝ) :=
        Finset.sum_range_sub' _ _
    _ ≤ 1 / B := by
        have h0 : ((B + 0 : ℕ) : ℝ) = B := by simp
        rw [h0]
        exact sub_le_self _ (by positivity)

/-- Summing `1/p²` over the band primes: `≤ 1/√(√(2x))`. -/
theorem sum_bandLargePrimes_inv_sq_le {x : ℕ}
    (hB : 1 ≤ Nat.sqrt (Nat.sqrt (2 * x))) :
    ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
      (1 : ℝ) / p ^ 2 ≤ 1 / Nat.sqrt (Nat.sqrt (2 * x)) :=
  calc ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
        (1 : ℝ) / p ^ 2
      ≤ ∑ n ∈ Finset.Ico (Nat.sqrt (Nat.sqrt (2 * x)) + 1)
            (Nat.sqrt (2 * x) + 1), (1 : ℝ) / n ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (bandLargePrimes_subset_Ico x)
          (fun n _ _ => by positivity)
    _ ≤ 1 / Nat.sqrt (Nat.sqrt (2 * x)) :=
        sum_one_div_sq_Ico_le hB (Nat.sqrt (2 * x))

/-- A constant times a smaller power is eventually dominated by a larger
power. -/
theorem eventually_const_mul_rpow_le_rpow {a b : ℝ} (C : ℝ) (h : a < b) :
    ∀ᶠ x : ℕ in atTop, C * (x : ℝ) ^ a ≤ (x : ℝ) ^ b := by
  have hT : Tendsto (fun x : ℕ => (x : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hT.eventually_ge_atTop C, eventually_gt_atTop 0]
    with x hxC hx0
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx0
  calc C * (x : ℝ) ^ a ≤ (x : ℝ) ^ (b - a) * (x : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hxC (Real.rpow_nonneg hxr.le _)
    _ = (x : ℝ) ^ b := by
      rw [← Real.rpow_add hxr, sub_add_cancel]

/-- **Unconditional `k < H₀` bound**:
`bandLargeLo x ≤ H₀ · 4x · ∑_{p} p⁻² ≤ 4·H₀·x/√(√(2x))`, and with
`H₀ ≤ 2·x^{1/5}` and `√(√(2x)) ≥ x^{1/4}/2` this is eventually
`≤ 16·x^{19/20}`. -/
theorem bandLarge_lo_le :
    ∀ᶠ x : ℕ in atTop,
      (bandLargeLo x : ℝ) ≤ 16 * (x : ℝ) ^ (19 / 20 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with x hx1
  set B := Nat.sqrt (Nat.sqrt (2 * x)) with hBdef
  have hxr : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hB1 : 1 ≤ B := by
    have h1 : (1 : ℕ) ≤ Nat.sqrt (2 * x) := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr h1
  -- `(B+1)⁴ > 2x` since `B + 1 > √(√(2x))`
  have hB4 : 2 * x < (B + 1) ^ 4 := by
    have h1 : Nat.sqrt (2 * x) < (B + 1) * (B + 1) :=
      Nat.sqrt_lt.mp (Nat.lt_succ_self B)
    have h2 : 2 * x < (B + 1) * (B + 1) * ((B + 1) * (B + 1)) :=
      Nat.sqrt_lt.mp h1
    have h3 : (B + 1) * (B + 1) * ((B + 1) * (B + 1)) = (B + 1) ^ 4 := by ring
    rwa [h3] at h2
  -- `(x:ℝ)^{1/4} ≤ 2B` from `x ≤ (2B)⁴`
  have hxB4 : (x : ℝ) ≤ (2 * (B : ℝ)) ^ 4 := by
    have h1 : (B + 1) ^ 4 ≤ (2 * B) ^ 4 :=
      Nat.pow_le_pow_left (by omega) 4
    have h2 : x ≤ (2 * B) ^ 4 := by
      have : (2 * B) ^ 4 = 16 * B ^ 4 := by ring
      omega
    exact_mod_cast h2
  have hrootB : (x : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * (B : ℝ) := by
    have hroot : ∀ a : ℝ, 0 ≤ a → ((a ^ 4) : ℝ) ^ (1 / 4 : ℝ) = a := by
      intro a ha
      rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha,
        show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]
    calc (x : ℝ) ^ (1 / 4 : ℝ) ≤ ((2 * (B : ℝ)) ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg x) hxB4 (by norm_num)
      _ = 2 * (B : ℝ) := hroot _ (by positivity)
  -- `x / B ≤ 2·x^{3/4}`
  have hBp : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB1
  have hxB : (x : ℝ) / B ≤ 2 * (x : ℝ) ^ (3 / 4 : ℝ) := by
    rw [div_le_iff₀ hBp]
    calc (x : ℝ) = (x : ℝ) ^ ((3 / 4 : ℝ) + 1 / 4) := by
          rw [show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num, Real.rpow_one]
      _ = (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_add hxr _ _
      _ ≤ (x : ℝ) ^ (3 / 4 : ℝ) * (2 * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hrootB (Real.rpow_nonneg hxr.le _)
      _ = 2 * (x : ℝ) ^ (3 / 4 : ℝ) * (B : ℝ) := by ring
  -- `H₀ ≤ 2·x^{1/5}` since `1 ≤ x^{1/5}`
  have hHle : (runSplitH x : ℝ) ≤ 2 * (x : ℝ) ^ (1 / 5 : ℝ) := by
    have h1 : (runSplitH x : ℝ) < (x : ℝ) ^ (1 / 5 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg x) _)
    have h2 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hx1) (by norm_num)
    linarith [h1.le]
  -- the chain
  have hnat := bandLargeLo_le_aux x
  have hsum : ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
        (fun p => 2 * x < p ^ 4), (2 * ((2 * x : ℝ) / p ^ 2))
      = 4 * (x : ℝ) * ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
        (fun p => 2 * x < p ^ 4), (1 : ℝ) / p ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hbound1 : (bandLargeLo x : ℝ) ≤ (runSplitH x : ℝ) *
      (4 * (x : ℝ) * ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
        (fun p => 2 * x < p ^ 4), (1 : ℝ) / p ^ 2) := by
    calc (bandLargeLo x : ℝ)
        ≤ (runSplitH x : ℝ) *
            ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
              (fun p => 2 * x < p ^ 4), (2 * ((2 * x / p ^ 2 : ℕ) : ℝ)) := by
          exact_mod_cast hnat
      _ ≤ (runSplitH x : ℝ) *
            ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
              (fun p => 2 * x < p ^ 4), (2 * ((2 * x : ℝ) / p ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply Finset.sum_le_sum
          intro p _
          exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by norm_num)
      _ = _ := by rw [hsum]
  have hbound2 : (bandLargeLo x : ℝ) ≤
      4 * (runSplitH x : ℝ) * (x : ℝ) / (B : ℝ) := by
    calc (bandLargeLo x : ℝ)
        ≤ (runSplitH x : ℝ) * (4 * (x : ℝ) *
            ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
              (fun p => 2 * x < p ^ 4), (1 : ℝ) / p ^ 2) := hbound1
      _ ≤ (runSplitH x : ℝ) * (4 * (x : ℝ) * (1 / (B : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (sum_bandLargePrimes_inv_sq_le hB1)
              (by positivity))
            (Nat.cast_nonneg _)
      _ = 4 * (runSplitH x : ℝ) * (x : ℝ) / (B : ℝ) := by ring
  calc (bandLargeLo x : ℝ)
      ≤ 4 * (runSplitH x : ℝ) * (x : ℝ) / (B : ℝ) := hbound2
    _ = 4 * (runSplitH x : ℝ) * ((x : ℝ) / (B : ℝ)) := by ring
    _ ≤ 4 * (runSplitH x : ℝ) * (2 * (x : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hxB (by positivity)
    _ ≤ 4 * (2 * (x : ℝ) ^ (1 / 5 : ℝ)) * (2 * (x : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hHle (by norm_num))
          (by positivity)
    _ = 16 * (x : ℝ) ^ (19 / 20 : ℝ) := by
        rw [show (4 : ℝ) * (2 * (x : ℝ) ^ (1 / 5 : ℝ)) *
              (2 * (x : ℝ) ^ (3 / 4 : ℝ))
            = 16 * ((x : ℝ) ^ (1 / 5 : ℝ) * (x : ℝ) ^ (3 / 4 : ℝ)) by ring]
        rw [← Real.rpow_add hxr, show (1 / 5 : ℝ) + 3 / 4 = 19 / 20 by norm_num]

/-! ## The `k ≥ H₀` reduction and conditional assembly -/

/-- `bandLargeHi x ≤ ∑_p 2p · T_{H₀}(p)`: there are at most `2p` indices
`k ∈ [H₀, 2p]` and each satisfies `T_k ≤ T_{H₀}` by antitonicity. -/
theorem bandLargeHi_le (x : ℕ) :
    bandLargeHi x ≤
      ∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter (fun p => 2 * x < p ^ 4),
        (2 * p) * (rightRunCount x p (runSplitH x) +
          leftRunCount x p (runSplitH x)) := by
  unfold bandLargeHi
  apply Finset.sum_le_sum
  intro p _
  have hcard : ((Finset.Icc 1 (2 * p)).filter
      (fun k => runSplitH x ≤ k)).card ≤ 2 * p := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Nat.card_Icc]
    omega
  calc ∑ k ∈ (Finset.Icc 1 (2 * p)).filter (fun k => runSplitH x ≤ k),
        (rightRunCount x p k + leftRunCount x p k)
      ≤ ∑ _k ∈ (Finset.Icc 1 (2 * p)).filter (fun k => runSplitH x ≤ k),
          (rightRunCount x p (runSplitH x) + leftRunCount x p (runSplitH x)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkH : runSplitH x ≤ k := (Finset.mem_filter.mp hk).2
        exact Nat.add_le_add (rightRunCount_anti hkH) (leftRunCount_anti hkH)
    _ = ((Finset.Icc 1 (2 * p)).filter (fun k => runSplitH x ≤ k)).card *
          (rightRunCount x p (runSplitH x) + leftRunCount x p (runSplitH x)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * p) * (rightRunCount x p (runSplitH x) +
          leftRunCount x p (runSplitH x)) :=
        Nat.mul_le_mul hcard le_rfl

/-- **Conditional assembly**: if `bandLargeHi x ≤ x^{9/10}` eventually,
then `bandLargeCount x ≤ x^{96/100}` eventually. -/
theorem bandLargeCount_le_of_hi_le
    (hhi : ∀ᶠ x : ℕ in atTop,
      (bandLargeHi x : ℝ) ≤ (x : ℝ) ^ (9 / 10 : ℝ)) :
    ∀ᶠ x : ℕ in atTop,
      (bandLargeCount x : ℝ) ≤ (x : ℝ) ^ (96 / 100 : ℝ) := by
  have hlo := bandLarge_lo_le
  have h32 := eventually_const_mul_rpow_le_rpow 32
    (show (19 / 20 : ℝ) < 96 / 100 by norm_num)
  have h2 := eventually_const_mul_rpow_le_rpow 2
    (show (9 / 10 : ℝ) < 96 / 100 by norm_num)
  filter_upwards [hlo, hhi, h32, h2] with x hlox hhix h32x h2x
  rw [bandLargeCount_eq_lo_add_hi x, Nat.cast_add]
  have h1 : (bandLargeLo x : ℝ) ≤ (x : ℝ) ^ (96 / 100 : ℝ) / 2 := by
    linarith
  have h2' : (bandLargeHi x : ℝ) ≤ (x : ℝ) ^ (96 / 100 : ℝ) / 2 := by
    linarith
  linarith

/-- **Hypothesis-parameterized assembly**: if the reduced count
`∑_p 2p·(rightRunCount x p H₀ + leftRunCount x p H₀)` is eventually
`≤ x^{9/10}`, then `bandLargeCount x ≤ x^{96/100}` eventually. -/
theorem bandLargeCount_le_of_run_bound
    (hhi : ∀ᶠ x : ℕ in atTop,
      ((∑ p ∈ (Nat.primesLE (Nat.sqrt (2 * x))).filter
          (fun p => 2 * x < p ^ 4),
        (2 * p) * (rightRunCount x p (runSplitH x) +
          leftRunCount x p (runSplitH x)) : ℕ) : ℝ)
        ≤ (x : ℝ) ^ (9 / 10 : ℝ)) :
    ∀ᶠ x : ℕ in atTop,
      (bandLargeCount x : ℝ) ≤ (x : ℝ) ^ (96 / 100 : ℝ) :=
  bandLargeCount_le_of_hi_le (hhi.mono fun x hx =>
    (Nat.cast_le.mpr (bandLargeHi_le x)).trans hx)

end JSP314
