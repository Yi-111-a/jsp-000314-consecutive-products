import JSP314.SmoothLB2
import Mathlib.Tactic

/-!
# A still stronger lower bound for `badSingletonCount`: `x^{9/10}/(log x)^9`

We prove that `S(x) = badSingletonCount x` satisfies the eventual lower bound

  `S(x) ≥ (1/17592186044416) · x^{9/10} / (log x)^9`,

improving the `x^{7/8}` bound of `SmoothLB2.lean` (the exponent `9/10 = 0.9`
exceeds `7/8 = 0.875`).  The construction is identical in shape, with nine free
prime parameters instead of seven.

## Proof outline

Consider `n = p²·q₁·q₂·q₃·q₄·q₅·q₆·q₇·q₈`, where `p` is a prime in `(P0, 2P0]`
with `P0 ≈ 2·x^{1/10}` and each `qᵢ` is a prime in the disjoint dyadic shell
`(2^{i-1}Q0, 2^iQ0]` with `Q0 ≈ x^{1/10}/256`.

* Since `qᵢ ≤ 256·Q0 ≤ P0 < p`, the largest prime factor of `n` is `p`,
  so `p² ∣ n` and `n` is a bad singleton.
* `n ≤ (2P0)²·(2Q0)(4Q0)⋯(256Q0) ≤ (9/262144)·t^10 < x` for `t = x^{1/10}`.
* The tuple map is injective: `p = P(n)`, and the `qᵢ` are recovered by
  repeatedly taking the least prime factor (`Nat.minFac`), because the
  disjoint shells force `q₁ < q₂ < … < q₈`.
* Each shell contributes `≥ shell/(8·log shell)` primes
  (`SmoothLB.eventually_dyadicPrimes_card_ge`), giving
  `S(x) ≥ t^9/(2^{44}·(log x)^9) = x^{9/10}/(2^{44}·(log x)^9)`.
-/

namespace JSP314

namespace SmoothLB3

open Finset Filter SmoothLB SmoothLB2

open scoped Topology

open Asymptotics

/-- A prime divisor of a product of seven primes is one of them. -/
theorem prime_dvd_prime_mul_seven {r a b c d e f g : ℕ} (hr : r.Prime)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime)
    (hf : f.Prime) (hg : g.Prime)
    (h : r ∣ a * (b * (c * (d * (e * (f * g)))))) :
    r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g := by
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases ha.eq_one_or_self_of_dvd _ h' with e' | e'
    · exact absurd e' hr.ne_one
    · exact Or.inl e'
  · rcases prime_dvd_prime_mul_six hr hb hc hd he hf hg h' with
      e' | e' | e' | e' | e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr (Or.inl e'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e')))))

/-- A prime divisor of a product of eight primes is one of them. -/
theorem prime_dvd_prime_mul_eight {r a b c d e f g i : ℕ} (hr : r.Prime)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime)
    (hf : f.Prime) (hg : g.Prime) (hi : i.Prime)
    (h : r ∣ a * (b * (c * (d * (e * (f * (g * i))))))) :
    r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g ∨ r = i := by
  rcases hr.dvd_mul.mp h with h' | h'
  · rcases ha.eq_one_or_self_of_dvd _ h' with e' | e'
    · exact absurd e' hr.ne_one
    · exact Or.inl e'
  · rcases prime_dvd_prime_mul_seven hr hb hc hd he hf hg hi h' with
      e' | e' | e' | e' | e' | e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr (Or.inl e'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e'))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e'))))))

/-- The map `(p, q₁, …, q₈) ↦ p²·q₁·q₂·q₃·q₄·q₅·q₆·q₇·q₈`. -/
def nonaMap : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → ℕ
  | (p, q1, q2, q3, q4, q5, q6, q7, q8) =>
      p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))))

/-- The finset of tuples `(p, q₁, …, q₈)` of primes in nine consecutive
dyadic shells: `p ∈ (P0, 2P0]`, `qᵢ ∈ (2^{i-1}Q0, 2^iQ0]`. -/
def nonaSet (P0 Q0 : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  dyadicPrimes P0 ×ˢ (dyadicPrimes Q0 ×ˢ (dyadicPrimes (2 * Q0) ×ˢ
    (dyadicPrimes (4 * Q0) ×ˢ (dyadicPrimes (8 * Q0) ×ˢ
      (dyadicPrimes (16 * Q0) ×ˢ (dyadicPrimes (32 * Q0) ×ˢ
        (dyadicPrimes (64 * Q0) ×ˢ dyadicPrimes (128 * Q0))))))))

theorem mem_nonaSet {P0 Q0 p q1 q2 q3 q4 q5 q6 q7 q8 : ℕ} :
    (p, q1, q2, q3, q4, q5, q6, q7, q8) ∈ nonaSet P0 Q0 ↔
      (p ∈ dyadicPrimes P0 ∧ q1 ∈ dyadicPrimes Q0 ∧ q2 ∈ dyadicPrimes (2 * Q0) ∧
        q3 ∈ dyadicPrimes (4 * Q0) ∧ q4 ∈ dyadicPrimes (8 * Q0) ∧
          q5 ∈ dyadicPrimes (16 * Q0) ∧ q6 ∈ dyadicPrimes (32 * Q0) ∧
            q7 ∈ dyadicPrimes (64 * Q0) ∧ q8 ∈ dyadicPrimes (128 * Q0)) := by
  simp [nonaSet, Finset.mem_product]

theorem card_nonaSet (P0 Q0 : ℕ) :
    (nonaSet P0 Q0).card = (dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
      ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
        ((dyadicPrimes (8 * Q0)).card * ((dyadicPrimes (16 * Q0)).card *
          ((dyadicPrimes (32 * Q0)).card * ((dyadicPrimes (64 * Q0)).card *
            (dyadicPrimes (128 * Q0)).card))))))) := by
  simp [nonaSet, Finset.card_product]

set_option maxHeartbeats 1600000 in
/-- `badSingletonCount x` is at least the number of 9-tuples; the conditions
`256·Q0 ≤ P0` (so every `qᵢ < p`) and the displayed bound (so `n ≤ x`)
make the tuple map a valid injection into the bad set. -/
theorem card_nonaSet_le_badSingletonCount (x P0 Q0 : ℕ) (hQP : 256 * Q0 ≤ P0)
    (hx : (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) *
      ((16 * Q0) * ((32 * Q0) * ((64 * Q0) * ((128 * Q0) * (256 * Q0)))))))) ≤ x) :
    (nonaSet P0 Q0).card ≤ badSingletonCount x := by
  classical
  have hbad : (nonaSet P0 Q0).image nonaMap ⊆
      (Finset.range (x + 1)).filter
        (fun m => 1 < m ∧ (largestPrimeFactor m) ^ 2 ∣ m) := by
    rw [Finset.image_subset_iff]
    rintro ⟨p, q1, q2, q3, q4, q5, q6, q7, q8⟩ ht
    rw [mem_nonaSet] at ht
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ht
    obtain ⟨hp, hpP, hp2⟩ := mem_dyadicPrimes.mp h1
    obtain ⟨hq1, -, hq1b⟩ := mem_dyadicPrimes.mp h2
    obtain ⟨hq2, -, hq2b⟩ := mem_dyadicPrimes.mp h3
    obtain ⟨hq3, -, hq3b⟩ := mem_dyadicPrimes.mp h4
    obtain ⟨hq4, -, hq4b⟩ := mem_dyadicPrimes.mp h5
    obtain ⟨hq5, -, hq5b⟩ := mem_dyadicPrimes.mp h6
    obtain ⟨hq6, -, hq6b⟩ := mem_dyadicPrimes.mp h7
    obtain ⟨hq7, -, hq7b⟩ := mem_dyadicPrimes.mp h8
    obtain ⟨hq8, -, hq8b⟩ := mem_dyadicPrimes.mp h9
    have hm : 1 ≤ q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) :=
      Nat.succ_le_of_lt (mul_pos hq1.pos (mul_pos hq2.pos (mul_pos hq3.pos
        (mul_pos hq4.pos (mul_pos hq5.pos (mul_pos hq6.pos
          (mul_pos hq7.pos hq8.pos)))))))
    have hsmooth : ∀ t : ℕ, t.Prime →
        t ∣ q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) → t ≤ p := by
      intro t ht' htd
      rcases prime_dvd_prime_mul_eight ht' hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 htd with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hlpf : largestPrimeFactor
        (p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))))) = p :=
      largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hm hsmooth
    have hle : p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8))))))) ≤ x := by
      calc p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))))
          ≤ (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) *
              ((16 * Q0) * ((32 * Q0) * ((64 * Q0) * ((128 * Q0) *
                (256 * Q0)))))))) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left hp2 2)
              (Nat.mul_le_mul hq1b (Nat.mul_le_mul (by omega)
                (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
                  (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega)
                    (Nat.mul_le_mul (by omega) (by omega))))))))
        _ ≤ x := hx
    have h2 : 2 ≤ p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8))))))) := by
      calc 2 ≤ 2 ^ 2 * 1 := by norm_num
        _ ≤ p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8))))))) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hp.two_le 2) hm
    simp only [Finset.mem_filter, nonaMap]
    refine ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩
    rw [hlpf]
    exact ⟨q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))), rfl⟩
  have hinj : Set.InjOn nonaMap (nonaSet P0 Q0) := by
    rintro ⟨p, q1, q2, q3, q4, q5, q6, q7, q8⟩ ht
      ⟨r, s1, s2, s3, s4, s5, s6, s7, s8⟩ hs h
    rw [Finset.mem_coe, mem_nonaSet] at ht
    rw [Finset.mem_coe, mem_nonaSet] at hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ht
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hs
    obtain ⟨hp, hpP, -⟩ := mem_dyadicPrimes.mp h1
    obtain ⟨hq1, -, hq1b⟩ := mem_dyadicPrimes.mp h2
    obtain ⟨hq2, hQ2, hq2b⟩ := mem_dyadicPrimes.mp h3
    obtain ⟨hq3, hQ3, hq3b⟩ := mem_dyadicPrimes.mp h4
    obtain ⟨hq4, hQ4, hq4b⟩ := mem_dyadicPrimes.mp h5
    obtain ⟨hq5, hQ5, hq5b⟩ := mem_dyadicPrimes.mp h6
    obtain ⟨hq6, hQ6, hq6b⟩ := mem_dyadicPrimes.mp h7
    obtain ⟨hq7, hQ7, hq7b⟩ := mem_dyadicPrimes.mp h8
    obtain ⟨hq8, hQ8, hq8b⟩ := mem_dyadicPrimes.mp h9
    obtain ⟨hrp, hrP, -⟩ := mem_dyadicPrimes.mp g1
    obtain ⟨hs1, -, hs1b⟩ := mem_dyadicPrimes.mp g2
    obtain ⟨hs2, hS2, hs2b⟩ := mem_dyadicPrimes.mp g3
    obtain ⟨hs3, hS3, hs3b⟩ := mem_dyadicPrimes.mp g4
    obtain ⟨hs4, hS4, hs4b⟩ := mem_dyadicPrimes.mp g5
    obtain ⟨hs5, hS5, hs5b⟩ := mem_dyadicPrimes.mp g6
    obtain ⟨hs6, hS6, hs6b⟩ := mem_dyadicPrimes.mp g7
    obtain ⟨hs7, hS7, hs7b⟩ := mem_dyadicPrimes.mp g8
    obtain ⟨hs8, hS8, hs8b⟩ := mem_dyadicPrimes.mp g9
    have h' : p ^ 2 * (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8))))))) =
        r ^ 2 * (s1 * (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8))))))) := h
    have hq_s : ∀ t : ℕ, t.Prime →
        t ∣ q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) → t ≤ p := by
      intro t ht' htd
      rcases prime_dvd_prime_mul_eight ht' hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 htd with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hs_s : ∀ t : ℕ, t.Prime →
        t ∣ s1 * (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8)))))) → t ≤ r := by
      intro t ht' htd
      rcases prime_dvd_prime_mul_eight ht' hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 htd with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hmq : 1 ≤ q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) :=
      Nat.succ_le_of_lt (mul_pos hq1.pos (mul_pos hq2.pos (mul_pos hq3.pos
        (mul_pos hq4.pos (mul_pos hq5.pos (mul_pos hq6.pos
          (mul_pos hq7.pos hq8.pos)))))))
    have hms : 1 ≤ s1 * (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8)))))) :=
      Nat.succ_le_of_lt (mul_pos hs1.pos (mul_pos hs2.pos (mul_pos hs3.pos
        (mul_pos hs4.pos (mul_pos hs5.pos (mul_pos hs6.pos
          (mul_pos hs7.pos hs8.pos)))))))
    have hpr : p = r := by
      have e1 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hp hmq hq_s
      have e2 := largestPrimeFactor_sq_mul_of_forall_prime_dvd_le hrp hms hs_s
      rw [← e1, h', e2]
    subst hpr
    have hw1 : q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) =
        s1 * (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8)))))) :=
      Nat.mul_left_cancel (pow_pos hp.pos 2) h'
    have hq1s1 : q1 = s1 := by
      have e1 : Nat.minFac (q1 * (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))))
          = q1 := by
        apply minFac_eq_of_forall_le hq1 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_eight ht' hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8 htd
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s1 * (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8)))))))
          = s1 := by
        apply minFac_eq_of_forall_le hs1 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_eight ht' hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 htd
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hw1] at e1
      exact e1.symm.trans e2
    subst hq1s1
    have hw2 : q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8))))) =
        s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8))))) :=
      Nat.mul_left_cancel hq1.pos hw1
    have hq2s2 : q2 = s2 := by
      have e1 : Nat.minFac (q2 * (q3 * (q4 * (q5 * (q6 * (q7 * q8)))))) = q2 := by
        apply minFac_eq_of_forall_le hq2 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_seven ht' hq2 hq3 hq4 hq5 hq6 hq7 hq8 htd with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s2 * (s3 * (s4 * (s5 * (s6 * (s7 * s8)))))) = s2 := by
        apply minFac_eq_of_forall_le hs2 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_seven ht' hs2 hs3 hs4 hs5 hs6 hs7 hs8 htd with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hw2] at e1
      exact e1.symm.trans e2
    subst hq2s2
    have hw3 : q3 * (q4 * (q5 * (q6 * (q7 * q8)))) =
        s3 * (s4 * (s5 * (s6 * (s7 * s8)))) :=
      Nat.mul_left_cancel hq2.pos hw2
    have hq3s3 : q3 = s3 := by
      have e1 : Nat.minFac (q3 * (q4 * (q5 * (q6 * (q7 * q8))))) = q3 := by
        apply minFac_eq_of_forall_le hq3 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_six ht' hq3 hq4 hq5 hq6 hq7 hq8 htd with
          rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s3 * (s4 * (s5 * (s6 * (s7 * s8))))) = s3 := by
        apply minFac_eq_of_forall_le hs3 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_six ht' hs3 hs4 hs5 hs6 hs7 hs8 htd with
          rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hw3] at e1
      exact e1.symm.trans e2
    subst hq3s3
    have hw4 : q4 * (q5 * (q6 * (q7 * q8))) = s4 * (s5 * (s6 * (s7 * s8))) :=
      Nat.mul_left_cancel hq3.pos hw3
    have hq4s4 : q4 = s4 := by
      have e1 : Nat.minFac (q4 * (q5 * (q6 * (q7 * q8)))) = q4 := by
        apply minFac_eq_of_forall_le hq4 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_five ht' hq4 hq5 hq6 hq7 hq8 htd with
          rfl | rfl | rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s4 * (s5 * (s6 * (s7 * s8)))) = s4 := by
        apply minFac_eq_of_forall_le hs4 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_five ht' hs4 hs5 hs6 hs7 hs8 htd with
          rfl | rfl | rfl | rfl | rfl <;> omega
      rw [hw4] at e1
      exact e1.symm.trans e2
    subst hq4s4
    have hw5 : q5 * (q6 * (q7 * q8)) = s5 * (s6 * (s7 * s8)) :=
      Nat.mul_left_cancel hq4.pos hw4
    have hq5s5 : q5 = s5 := by
      have e1 : Nat.minFac (q5 * (q6 * (q7 * q8))) = q5 := by
        apply minFac_eq_of_forall_le hq5 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_four ht' hq5 hq6 hq7 hq8 htd with
          rfl | rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s5 * (s6 * (s7 * s8))) = s5 := by
        apply minFac_eq_of_forall_le hs5 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_four ht' hs5 hs6 hs7 hs8 htd with
          rfl | rfl | rfl | rfl <;> omega
      rw [hw5] at e1
      exact e1.symm.trans e2
    subst hq5s5
    have hw6 : q6 * (q7 * q8) = s6 * (s7 * s8) := Nat.mul_left_cancel hq5.pos hw5
    have hq6s6 : q6 = s6 := by
      have e1 : Nat.minFac (q6 * (q7 * q8)) = q6 := by
        apply minFac_eq_of_forall_le hq6 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_three ht' hq6 hq7 hq8 htd with
          rfl | rfl | rfl <;> omega
      have e2 : Nat.minFac (s6 * (s7 * s8)) = s6 := by
        apply minFac_eq_of_forall_le hs6 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_three ht' hs6 hs7 hs8 htd with
          rfl | rfl | rfl <;> omega
      rw [hw6] at e1
      exact e1.symm.trans e2
    subst hq6s6
    have hw7 : q7 * q8 = s7 * s8 := Nat.mul_left_cancel hq6.pos hw6
    have hq7s7 : q7 = s7 := by
      have e1 : Nat.minFac (q7 * q8) = q7 := by
        apply minFac_eq_of_forall_le hq7 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_two ht' hq7 hq8 htd with rfl | rfl <;> omega
      have e2 : Nat.minFac (s7 * s8) = s7 := by
        apply minFac_eq_of_forall_le hs7 (dvd_mul_right _ _)
        intro t ht' htd
        rcases prime_dvd_prime_mul_two ht' hs7 hs8 htd with rfl | rfl <;> omega
      rw [hw7] at e1
      exact e1.symm.trans e2
    subst hq7s7
    have hq8s8 : q8 = s8 := Nat.mul_left_cancel hq7.pos hw7
    rw [hq8s8]
  calc (nonaSet P0 Q0).card
      = ((nonaSet P0 Q0).image nonaMap).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ badSingletonCount x := Finset.card_le_card hbad

/-!
### Assembly of the final bound
-/

set_option maxHeartbeats 3200000 in
theorem badSingletonCount_eventually_ge_9_10 :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in Filter.atTop,
      c * (x : ℝ) ^ (9 / 10 : ℝ) / Real.log x ^ 9 ≤ (badSingletonCount x : ℝ) := by
  -- `t = x^{1/10} → ∞`
  have htt : Filter.Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 10 : ℝ)) Filter.atTop
      Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  -- the nine shells tend to infinity as naturals
  have hQ0t : Filter.Tendsto (fun x : ℕ => ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono (fun x => Nat.le_ceil _)
        (htt.atTop_div_const (by norm_num)))
  have hP0t : Filter.Tendsto (fun x : ℕ => ⌈2 * (x : ℝ) ^ (1 / 10 : ℝ)⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_iff.mp
      (tendsto_atTop_mono (fun x => Nat.le_ceil _)
        (htt.const_mul_atTop' (by norm_num)))
  have h2Q0t : Filter.Tendsto
      (fun x : ℕ => 2 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h4Q0t : Filter.Tendsto
      (fun x : ℕ => 4 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h8Q0t : Filter.Tendsto
      (fun x : ℕ => 8 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h16Q0t : Filter.Tendsto
      (fun x : ℕ => 16 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h32Q0t : Filter.Tendsto
      (fun x : ℕ => 32 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h64Q0t : Filter.Tendsto
      (fun x : ℕ => 64 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  have h128Q0t : Filter.Tendsto
      (fun x : ℕ => 128 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
      Filter.atTop Filter.atTop :=
    tendsto_atTop_mono
      (fun x => le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)) hQ0t
  -- dyadic Chebyshev bounds on each shell
  have hC0 : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈2 * (x : ℝ) ^ (1 / 10 : ℝ)⌉₊ : ℝ) /
          (8 * Real.log ⌈2 * (x : ℝ) ^ (1 / 10 : ℝ)⌉₊)
        ≤ (dyadicPrimes ⌈2 * (x : ℝ) ^ (1 / 10 : ℝ)⌉₊).card :=
    hP0t.eventually eventually_dyadicPrimes_card_ge
  have hC1 : ∀ᶠ x : ℕ in Filter.atTop,
      (⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℝ) /
          (8 * Real.log ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)
        ≤ (dyadicPrimes ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊).card :=
    hQ0t.eventually eventually_dyadicPrimes_card_ge
  have hC2 : ∀ᶠ x : ℕ in Filter.atTop,
      ((2 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (2 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (2 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h2Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC3 : ∀ᶠ x : ℕ in Filter.atTop,
      ((4 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (4 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (4 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h4Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC4 : ∀ᶠ x : ℕ in Filter.atTop,
      ((8 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (8 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (8 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h8Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC5 : ∀ᶠ x : ℕ in Filter.atTop,
      ((16 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (16 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (16 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h16Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC6 : ∀ᶠ x : ℕ in Filter.atTop,
      ((32 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (32 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (32 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h32Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC7 : ∀ᶠ x : ℕ in Filter.atTop,
      ((64 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (64 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (64 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h64Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  have hC8 : ∀ᶠ x : ℕ in Filter.atTop,
      ((128 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊ : ℕ) : ℝ) /
          (8 * Real.log (128 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊))
        ≤ (dyadicPrimes (128 * ⌈(x : ℝ) ^ (1 / 10 : ℝ) / 256⌉₊)).card := by
    filter_upwards [h128Q0t.eventually eventually_dyadicPrimes_card_ge] with x hx
    push_cast at hx ⊢
    exact hx
  -- `t ≥ 512` eventually
  have ht512 : ∀ᶠ x : ℕ in Filter.atTop, (512 : ℝ) ≤ (x : ℝ) ^ (1 / 10 : ℝ) :=
    htt.eventually_ge_atTop 512
  refine ⟨1 / 17592186044416, by norm_num, ?_⟩
  filter_upwards [hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, ht512,
    eventually_ge_atTop 6561]
    with x hC0 hC1 hC2 hC3 hC4 hC5 hC6 hC7 hC8 ht512 hxN
  -- abbreviations
  set t : ℝ := (x : ℝ) ^ (1 / 10 : ℝ) with ht
  set P0 : ℕ := ⌈2 * t⌉₊ with hP0
  set Q0 : ℕ := ⌈t / 256⌉₊ with hQ0
  push_cast at hC2 hC3 hC4 hC5 hC6 hC7 hC8
  -- basic positivity facts
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hLnn : (0 : ℝ) ≤ Real.log x := hLpos.le
  have hLne : Real.log (x : ℝ) ≠ 0 := hLpos.ne'
  have ht_pos : (0 : ℝ) < t := by rw [ht]; exact Real.rpow_pos_of_pos hx0 _
  have ht_ge : (256 : ℝ) ≤ t := by linarith [ht512]
  have hlogt : Real.log t = 1 / 10 * Real.log (x : ℝ) := by
    rw [ht, Real.log_rpow hx0]
  have ht10 : t ^ 10 = (x : ℝ) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 / 10 : ℝ) * ((10 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have ht9 : t ^ 9 = (x : ℝ) ^ (9 / 10 : ℝ) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 / 10 : ℝ) * ((9 : ℕ) : ℝ) = 9 / 10 by norm_num]
  -- `log x ≥ 8·log 3` (since `x ≥ 6561 = 3^8`)
  have hlogx_ge : 8 * Real.log 3 ≤ Real.log (x : ℝ) := by
    have h6561 : ((6561 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxN
    have e : Real.log (6561 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) h6561
    have e2 : Real.log (6561 : ℝ) = 8 * Real.log 3 := by
      rw [show (6561 : ℝ) = (3 : ℝ) ^ (8 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith [e, e2]
  -- bounds on `P0`, `Q0`
  have hP0_ge : 2 * t ≤ (P0 : ℝ) := by
    rw [hP0]; exact Nat.le_ceil _
  have hP0_le : (P0 : ℝ) ≤ 3 * t := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * t by positivity)).le
    rw [← hP0] at h
    linarith [ht_ge]
  have hQ0_ge : t / 256 ≤ (Q0 : ℝ) := by
    rw [hQ0]; exact Nat.le_ceil _
  have hQ0_le : (Q0 : ℝ) ≤ t / 128 := by
    have h := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t / 256 by positivity)).le
    rw [← hQ0] at h
    linarith [ht_ge]
  -- `256·Q0 ≤ P0` (so that every `qᵢ < p`)
  have hQP : 256 * Q0 ≤ P0 := by
    have hr : (256 : ℝ) * Q0 ≤ (P0 : ℝ) := by linarith [hQ0_le, hP0_ge]
    exact_mod_cast hr
  -- `n ≤ x`
  have hxn : (2 * P0) ^ 2 * ((2 * Q0) * ((4 * Q0) * ((8 * Q0) *
      ((16 * Q0) * ((32 * Q0) * ((64 * Q0) * ((128 * Q0) * (256 * Q0)))))))) ≤ x := by
    have hreal : (2 * (P0 : ℝ)) ^ 2 * ((2 * (Q0 : ℝ)) * ((4 * (Q0 : ℝ)) *
        ((8 * (Q0 : ℝ)) * ((16 * (Q0 : ℝ)) * ((32 * (Q0 : ℝ)) *
          ((64 * (Q0 : ℝ)) * ((128 * (Q0 : ℝ)) * (256 * (Q0 : ℝ)))))))))
        ≤ (x : ℝ) := by
      have h1 : (2 : ℝ) * P0 ≤ 6 * t := by linarith [hP0_le]
      have h2 : (2 : ℝ) * Q0 ≤ t / 64 := by linarith [hQ0_le]
      have h3 : (4 : ℝ) * Q0 ≤ t / 32 := by linarith [hQ0_le]
      have h4 : (8 : ℝ) * Q0 ≤ t / 16 := by linarith [hQ0_le]
      have h5 : (16 : ℝ) * Q0 ≤ t / 8 := by linarith [hQ0_le]
      have h6 : (32 : ℝ) * Q0 ≤ t / 4 := by linarith [hQ0_le]
      have h7 : (64 : ℝ) * Q0 ≤ t / 2 := by linarith [hQ0_le]
      have h8 : (128 : ℝ) * Q0 ≤ t := by linarith [hQ0_le]
      have h9 : (256 : ℝ) * Q0 ≤ 2 * t := by linarith [hQ0_le]
      calc (2 * (P0 : ℝ)) ^ 2 * ((2 * (Q0 : ℝ)) * ((4 * (Q0 : ℝ)) *
              ((8 * (Q0 : ℝ)) * ((16 * (Q0 : ℝ)) * ((32 * (Q0 : ℝ)) *
                ((64 * (Q0 : ℝ)) * ((128 * (Q0 : ℝ)) * (256 * (Q0 : ℝ)))))))))
          ≤ (6 * t) ^ 2 * ((t / 64) * ((t / 32) * ((t / 16) * ((t / 8) *
              ((t / 4) * ((t / 2) * (t * (2 * t)))))))) := by
            refine mul_le_mul (pow_le_pow_left₀ (by positivity) h1 2) ?_
              (by positivity) (by positivity)
            exact mul_le_mul h2 (mul_le_mul h3 (mul_le_mul h4
              (mul_le_mul h5 (mul_le_mul h6 (mul_le_mul h7
                (mul_le_mul h8 h9 (by positivity) (by positivity))
                  (by positivity) (by positivity)) (by positivity) (by positivity))
                (by positivity) (by positivity)) (by positivity) (by positivity))
              (by positivity) (by positivity)) (by positivity) (by positivity)
        _ = (9 / 262144) * t ^ 10 := by ring
        _ ≤ t ^ 10 := by
            have hnn : (0 : ℝ) ≤ t ^ 10 := pow_nonneg ht_pos.le 10
            linarith
        _ = x := ht10
    exact_mod_cast hreal
  -- nat count bound
  have hnat : (dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
      ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
        ((dyadicPrimes (8 * Q0)).card * ((dyadicPrimes (16 * Q0)).card *
          ((dyadicPrimes (32 * Q0)).card * ((dyadicPrimes (64 * Q0)).card *
            (dyadicPrimes (128 * Q0)).card))))))) ≤ badSingletonCount x := by
    rw [← card_nonaSet]
    exact card_nonaSet_le_badSingletonCount x P0 Q0 hQP hxn
  -- `A/(2·log x) ≤ B/(8·log B)` whenever `A ≤ B`, `1 < B`, `8·log B ≤ 2·log x`
  have hstep : ∀ A B : ℝ, 1 < B → A ≤ B → 8 * Real.log B ≤ 2 * Real.log x →
      A / (2 * Real.log x) ≤ B / (8 * Real.log B) := by
    intro A B h1 hab hlog
    exact div_le_div₀ (by linarith) hab
      (mul_pos (by norm_num) (Real.log_pos h1)) hlog
  -- per-shell denominator bound `8·log(m·Q0) ≤ 2·log x` for `2 ≤ m ≤ 128`
  have hshell : ∀ m : ℝ, 2 ≤ m → m ≤ 128 → ∀ C : ℝ,
      (m * (Q0 : ℝ) / (8 * Real.log (m * (Q0 : ℝ))) ≤ C) →
        m * t / (512 * Real.log x) ≤ C := by
    intro m hm2 hm128 C hC
    have hQ0nn : (0 : ℝ) ≤ (Q0 : ℝ) := by linarith [hQ0_ge, ht_ge]
    have hge : m * (t / 256) ≤ m * (Q0 : ℝ) :=
      mul_le_mul_of_nonneg_left hQ0_ge (by linarith)
    have hle : m * (Q0 : ℝ) ≤ t := by
      calc m * (Q0 : ℝ) ≤ 128 * (t / 128) :=
            mul_le_mul hm128 hQ0_le hQ0nn (by norm_num)
        _ = t := by ring
    have hgt : (1 : ℝ) < m * (Q0 : ℝ) := by
      have h2 : (2 : ℝ) ≤ (Q0 : ℝ) := by linarith [hQ0_ge, ht512]
      calc (1 : ℝ) < 2 * 2 := by norm_num
        _ ≤ m * Q0 := mul_le_mul hm2 h2 (by norm_num) (by linarith)
    have hlog : 8 * Real.log (m * (Q0 : ℝ)) ≤ 2 * Real.log x := by
      have hpos : (0 : ℝ) < m * (Q0 : ℝ) := by linarith
      have e := Real.log_le_log hpos hle
      linarith [hlogt, hLpos]
    calc m * t / (512 * Real.log x)
        = (m * (t / 256)) / (2 * Real.log x) := by
          rw [div_eq_div_iff (mul_ne_zero (by norm_num) hLne)
              (mul_ne_zero (by norm_num) hLne)]
          ring
      _ ≤ m * (Q0 : ℝ) / (8 * Real.log (m * (Q0 : ℝ))) := hstep _ _ hgt hge hlog
      _ ≤ C := hC
  -- lower bounds for each dyadic cardinal
  have hD0 : t / Real.log x ≤ ((dyadicPrimes P0).card : ℝ) := by
    have hgt : (1 : ℝ) < (P0 : ℝ) := by linarith [hP0_ge, ht_ge]
    have hlog : 8 * Real.log (P0 : ℝ) ≤ 2 * Real.log x := by
      have e : Real.log (P0 : ℝ) ≤ Real.log (3 * t) :=
        Real.log_le_log (by positivity) hP0_le
      rw [Real.log_mul (by norm_num) ht_pos.ne'] at e
      linarith [hlogt, hlogx_ge, hLnn]
    calc t / Real.log x
        = (2 * t) / (2 * Real.log x) := by
          rw [div_eq_div_iff hLne (mul_ne_zero (by norm_num) hLne)]
          ring
      _ ≤ (P0 : ℝ) / (8 * Real.log (P0 : ℝ)) := hstep _ _ hgt hP0_ge hlog
      _ ≤ _ := hC0
  have hD1 : t / (512 * Real.log x) ≤ ((dyadicPrimes Q0).card : ℝ) := by
    have hle : (Q0 : ℝ) ≤ t := by linarith [hQ0_le, ht_pos]
    have hgt : (1 : ℝ) < (Q0 : ℝ) := by linarith [hQ0_ge, ht512]
    have hlog : 8 * Real.log (Q0 : ℝ) ≤ 2 * Real.log x := by
      have e := Real.log_le_log (by linarith : (0 : ℝ) < (Q0 : ℝ)) hle
      linarith [hlogt, hLpos]
    calc t / (512 * Real.log x)
        = (t / 256) / (2 * Real.log x) := by
          rw [div_eq_div_iff (mul_ne_zero (by norm_num) hLne)
              (mul_ne_zero (by norm_num) hLne)]
          ring
      _ ≤ (Q0 : ℝ) / (8 * Real.log (Q0 : ℝ)) := hstep _ _ hgt hQ0_ge hlog
      _ ≤ _ := hC1
  have hD2 : (2 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (2 * Q0)).card : ℝ) :=
    hshell 2 (by norm_num) (by norm_num) _ hC2
  have hD3 : (4 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (4 * Q0)).card : ℝ) :=
    hshell 4 (by norm_num) (by norm_num) _ hC3
  have hD4 : (8 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (8 * Q0)).card : ℝ) :=
    hshell 8 (by norm_num) (by norm_num) _ hC4
  have hD5 : (16 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (16 * Q0)).card : ℝ) :=
    hshell 16 (by norm_num) (by norm_num) _ hC5
  have hD6 : (32 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (32 * Q0)).card : ℝ) :=
    hshell 32 (by norm_num) (by norm_num) _ hC6
  have hD7 : (64 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (64 * Q0)).card : ℝ) :=
    hshell 64 (by norm_num) (by norm_num) _ hC7
  have hD8 : (128 : ℝ) * t / (512 * Real.log x) ≤
      ((dyadicPrimes (128 * Q0)).card : ℝ) :=
    hshell 128 (by norm_num) (by norm_num) _ hC8
  -- product bound
  have hn0 : (0 : ℝ) ≤ t / Real.log x := div_nonneg ht_pos.le hLnn
  have hn1 : (0 : ℝ) ≤ t / (512 * Real.log x) :=
    div_nonneg ht_pos.le (by positivity)
  have hn2 : (0 : ℝ) ≤ (2 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn3 : (0 : ℝ) ≤ (4 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn4 : (0 : ℝ) ≤ (8 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn5 : (0 : ℝ) ≤ (16 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn6 : (0 : ℝ) ≤ (32 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn7 : (0 : ℝ) ≤ (64 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hn8 : (0 : ℝ) ≤ (128 : ℝ) * t / (512 * Real.log x) :=
    div_nonneg (by positivity) (by positivity)
  have hprod : t / Real.log x * (t / (512 * Real.log x) *
      ((2 : ℝ) * t / (512 * Real.log x) * ((4 : ℝ) * t / (512 * Real.log x) *
        ((8 : ℝ) * t / (512 * Real.log x) * ((16 : ℝ) * t / (512 * Real.log x) *
          ((32 : ℝ) * t / (512 * Real.log x) * ((64 : ℝ) * t / (512 * Real.log x) *
            ((128 : ℝ) * t / (512 * Real.log x)))))))))
      ≤ ((dyadicPrimes P0).card * ((dyadicPrimes Q0).card *
          ((dyadicPrimes (2 * Q0)).card * ((dyadicPrimes (4 * Q0)).card *
            ((dyadicPrimes (8 * Q0)).card * ((dyadicPrimes (16 * Q0)).card *
              ((dyadicPrimes (32 * Q0)).card * ((dyadicPrimes (64 * Q0)).card *
                (dyadicPrimes (128 * Q0)).card))))))) : ℝ) :=
    mul_le_mul hD0
      (mul_le_mul hD1
        (mul_le_mul hD2
          (mul_le_mul hD3
            (mul_le_mul hD4
              (mul_le_mul hD5
                (mul_le_mul hD6
                  (mul_le_mul hD7 hD8 hn8 (by positivity))
                  (mul_nonneg hn7 hn8) (by positivity))
                (mul_nonneg hn6 (mul_nonneg hn7 hn8)) (by positivity))
              (mul_nonneg hn5 (mul_nonneg hn6 (mul_nonneg hn7 hn8)))
              (by positivity))
            (mul_nonneg hn4 (mul_nonneg hn5 (mul_nonneg hn6
              (mul_nonneg hn7 hn8)))) (by positivity))
          (mul_nonneg hn3 (mul_nonneg hn4 (mul_nonneg hn5 (mul_nonneg hn6
            (mul_nonneg hn7 hn8))))) (by positivity))
        (mul_nonneg hn2 (mul_nonneg hn3 (mul_nonneg hn4 (mul_nonneg hn5
          (mul_nonneg hn6 (mul_nonneg hn7 hn8)))))) (by positivity))
      (mul_nonneg hn1 (mul_nonneg hn2 (mul_nonneg hn3 (mul_nonneg hn4
        (mul_nonneg hn5 (mul_nonneg hn6 (mul_nonneg hn7 hn8)))))))
      (by positivity)
  -- final real inequality
  have key : t / Real.log x * (t / (512 * Real.log x) *
      ((2 : ℝ) * t / (512 * Real.log x) * ((4 : ℝ) * t / (512 * Real.log x) *
        ((8 : ℝ) * t / (512 * Real.log x) * ((16 : ℝ) * t / (512 * Real.log x) *
          ((32 : ℝ) * t / (512 * Real.log x) * ((64 : ℝ) * t / (512 * Real.log x) *
            ((128 : ℝ) * t / (512 * Real.log x)))))))))
      = t ^ 9 / (17592186044416 * Real.log x ^ 9) := by
    field_simp [hLne]
    ring
  calc (1 / 17592186044416 : ℝ) * (x : ℝ) ^ (9 / 10 : ℝ) / Real.log x ^ 9
      = t ^ 9 / (17592186044416 * Real.log x ^ 9) := by
        rw [← ht9, div_eq_div_iff (pow_pos hLpos 9).ne'
          (mul_pos (by norm_num) (pow_pos hLpos 9)).ne']
        ring
    _ = t / Real.log x * (t / (512 * Real.log x) *
          ((2 : ℝ) * t / (512 * Real.log x) * ((4 : ℝ) * t / (512 * Real.log x) *
            ((8 : ℝ) * t / (512 * Real.log x) * ((16 : ℝ) * t / (512 * Real.log x) *
              ((32 : ℝ) * t / (512 * Real.log x) * ((64 : ℝ) * t / (512 * Real.log x) *
                ((128 : ℝ) * t / (512 * Real.log x))))))))) := key.symm
    _ ≤ _ := hprod
    _ ≤ (badSingletonCount x : ℝ) := by exact_mod_cast hnat

end SmoothLB3

end JSP314
