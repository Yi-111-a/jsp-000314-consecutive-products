import JSP314.RunDecomp
import JSP314.Defs
import Mathlib.Tactic

/-!
# JSP-000314 — bridge from run witnesses to sifted sets

A run witness `m = p²·r` has `p²·r + j` `p`-smooth for `j ∈ [1, k]`, hence
`p²·r + j` is not divisible by any prime `q ∈ (p, w]` for any `w`.  So the
map `m ↦ m / p²` injects `rightRunWitness x p k` into the sifted set

  `runSiftedRight y p k w = {r ∈ [1, y] : ∀ q ∈ (p, w] prime, ∀ j ∈ [1, k],
                              q ∤ p²·r + j}`

and similarly `leftRunWitness` maps into `runSiftedLeft` (the `p²·r − j`
variant, guarded by `j < p²·r` so the difference is positive).  Any sieve
upper bound on the sifted sets bounds the run counts.
-/

namespace JSP314

open Classical

/-- Right sifted set: `r ∈ [1, y]` such that no prime `q ∈ (p, w]` divides
any of `p²·r + 1, …, p²·r + k`. -/
noncomputable def runSiftedRight (y p k w : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime,
      ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * r + j

/-- Left sifted set: `r ∈ [1, y]` such that no prime `q ∈ (p, w]` divides
any positive difference `p²·r − j` with `j ∈ [1, k]` and `j < p²·r`. -/
noncomputable def runSiftedLeft (y p k w : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime,
      ∀ j ∈ Finset.Icc 1 k, j < p ^ 2 * r → ¬ q ∣ p ^ 2 * r - j

theorem mem_runSiftedRight {y p k w r : ℕ} :
    r ∈ runSiftedRight y p k w ↔
      r ∈ Finset.Icc 1 y ∧
        ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime,
          ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * r + j := by
  simp only [runSiftedRight, Finset.mem_filter]

theorem mem_runSiftedLeft {y p k w r : ℕ} :
    r ∈ runSiftedLeft y p k w ↔
      r ∈ Finset.Icc 1 y ∧
        ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime,
          ∀ j ∈ Finset.Icc 1 k, j < p ^ 2 * r → ¬ q ∣ p ^ 2 * r - j := by
  simp only [runSiftedLeft, Finset.mem_filter]

/-- A prime `q > p` cannot divide a `p`-smooth `n ≥ 2`. -/
theorem not_prime_dvd_of_lpf_le {n p q : ℕ} (hn : 2 ≤ n)
    (hlpf : largestPrimeFactor n ≤ p) (hq : q.Prime) (hpq : p < q) :
    ¬ q ∣ n := by
  intro hdvd
  exact absurd ((prime_dvd_le_largestPrimeFactor hn hq hdvd).trans hlpf)
    (not_le.mpr hpq)

/-- `m ≥ 1` for a run witness (it has `p² ∣ m` and `lpf m = p` prime). -/
theorem witness_pos {p m : ℕ} (hp : Nat.Prime p)
    (hdvd : p ^ 2 ∣ m) (hlpf : largestPrimeFactor m = p) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · exfalso
    subst h
    rw [largestPrimeFactor_eq_one_iff.mpr (Nat.zero_le 1)] at hlpf
    have := hp.two_le
    omega
  · exact h

/-- The right-run witness map `m ↦ m / p²` lands in `runSiftedRight`. -/
theorem div_mem_runSiftedRight {x p k w m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ rightRunWitness x p k) :
    m / p ^ 2 ∈ runSiftedRight (2 * x / p ^ 2) p k w := by
  rw [mem_rightRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  rw [mem_runSiftedRight]
  refine ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hp2, Nat.div_le_div_right hm2x⟩,
    ?_⟩
  intro q hq j hj
  rw [Finset.mem_filter, Finset.mem_Ioc] at hq
  obtain ⟨⟨hpq, -⟩, hqprime⟩ := hq
  rw [Finset.mem_Icc] at hj
  have hrew : p ^ 2 * (m / p ^ 2) + j = m + j := by
    rw [Nat.mul_div_cancel' hdvd]
  rw [hrew]
  have hmj : m + j ∈ Finset.Icc (m + 1) (m + k) := by
    rw [Finset.mem_Icc]
    omega
  have h2 : 2 ≤ m + j := by
    have hpm : p ^ 2 ≤ m := Nat.le_of_dvd hm1 hdvd
    have hp4 : 4 ≤ p ^ 2 :=
      Nat.pow_le_pow_left hp.two_le 2
    omega
  exact not_prime_dvd_of_lpf_le h2 (hsmooth _ hmj) hqprime hpq

/-- The left-run witness map `m ↦ m / p²` lands in `runSiftedLeft`. -/
theorem div_mem_runSiftedLeft {x p k w m : ℕ} (hp : Nat.Prime p)
    (hm : m ∈ leftRunWitness x p k) :
    m / p ^ 2 ∈ runSiftedLeft (2 * x / p ^ 2) p k w := by
  rw [mem_leftRunWitness] at hm
  obtain ⟨hm2x, hdvd, hlpf, hsmooth⟩ := hm
  have hm1 : 1 ≤ m := witness_pos hp hdvd hlpf
  have hp2 : 0 < p ^ 2 := Nat.pow_pos hp.pos
  rw [mem_runSiftedLeft]
  refine ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hm1 hdvd) hp2, Nat.div_le_div_right hm2x⟩,
    ?_⟩
  intro q hq j hj hjlt
  rw [Finset.mem_filter, Finset.mem_Ioc] at hq
  obtain ⟨⟨hpq, -⟩, hqprime⟩ := hq
  rw [Finset.mem_Icc] at hj
  have hrew : p ^ 2 * (m / p ^ 2) = m := Nat.mul_div_cancel' hdvd
  rw [hrew] at hjlt ⊢
  have hmj : m - j ∈ Finset.Icc (m - k) (m - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hs := hsmooth _ hmj
  rcases Nat.lt_or_ge (m - j) 2 with hlt | hge
  · intro hd
    have hqle := Nat.le_of_dvd (by omega : 0 < m - j) hd
    have hq2 := hqprime.two_le
    omega
  · exact not_prime_dvd_of_lpf_le hge hs hqprime hpq

/-- `m ↦ m / p²` is injective on multiples of `p²` when `p > 0`. -/
theorem div_injOn {p : ℕ} (hp : 0 < p) :
    Set.InjOn (fun m => m / p ^ 2) {m : ℕ | p ^ 2 ∣ m} := by
  intro a ha b hb hab
  calc a = p ^ 2 * (a / p ^ 2) := (Nat.mul_div_cancel' ha).symm
    _ = p ^ 2 * (b / p ^ 2) := by
        have hab' : a / p ^ 2 = b / p ^ 2 := hab
        rw [hab']
    _ = b := Nat.mul_div_cancel' hb

/-- Right run count is bounded by the sifted set cardinality. -/
theorem rightRunCount_le_runSiftedRight {x p k w : ℕ} (hp : Nat.Prime p) :
    rightRunCount x p k ≤ (runSiftedRight (2 * x / p ^ 2) p k w).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe]
    exact div_mem_runSiftedRight hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_rightRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_rightRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

/-- Left run count is bounded by the sifted set cardinality. -/
theorem leftRunCount_le_runSiftedLeft {x p k w : ℕ} (hp : Nat.Prime p) :
    leftRunCount x p k ≤ (runSiftedLeft (2 * x / p ^ 2) p k w).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun m => m / p ^ 2)
  · intro m hm
    rw [Finset.mem_coe]
    exact div_mem_runSiftedLeft hp (Finset.mem_coe.mp hm)
  · intro a ha b hb hab
    exact div_injOn hp.pos
      (mem_leftRunWitness.mp (Finset.mem_coe.mp ha)).2.1
      (mem_leftRunWitness.mp (Finset.mem_coe.mp hb)).2.1 hab

end JSP314
