import Mathlib

/-!
# JSP-000314 — joint sieve upper bound (CRT period counting)

This file bounds the number of `r ∈ [1, y]` such that the `k` consecutive
translates `p²·r + 1, …, p²·r + k` all avoid prime divisors in `(p, w]`:

  `siftedSet y p k w := (Icc 1 y).filter fun r =>
    ∀ q ∈ (Ioc p w).filter Nat.Prime, ∀ j ∈ Icc 1 k, ¬ q ∣ p^2 * r + j`.

## Proof route

We do **not** use inclusion–exclusion.  Instead, the sifted condition on `r`
depends only on the residue `r mod P`, where `P = ∏ q` over the sifted primes.
Over a full period `range P` the number of surviving residue classes factors,
by the Chinese remainder theorem (`Nat.chineseRemainder`), as a product over
the primes `q` of the number of allowed residues mod `q`, which is at most
`q - min k q` (the residues `-j·(p²)⁻¹ mod q`, `j = 1, …, k`, hit at least
`min k q` distinct classes, using a modular inverse of `p²` in `ZMod q`).

Splitting `[1, y]` into `⌊y/P⌋` full periods plus a partial one gives

  `#siftedSet ≤ (y / P + 1) · ∏_{q ∈ S} (q - min k q)`,

and hence over `ℝ`

  `#siftedSet ≤ y · ∏_{q ∈ S} (1 - min k q / q) + ∏_{q ∈ S} (q - min k q)`.

The main term is `~ y·∏_{p<q≤w}(1 - k/q)` (the `min k q` factor is exact:
once `k ≥ q` every residue is forbidden and the product vanishes), and the
error term `∏(q - min k q) ≤ ∏ q ≤ w^{#S}` is `w^{O(π(w))}` — fine for
`w = O(log y)`.

## Main results

* `dvd_sq_mul_add_iff_dvd_mod` — `q ∣ p²r + j ↔ q ∣ p²(r % m) + j` for `q ∣ m`.
* `sifted_count_mod_prime_le` — per-prime count `≤ q - min k q`.
* `card_filter_range_mul` — CRT factorization of a two-modulus count.
* `sifted_count_period_le` — `∏(q - min k q)` bound over a full period.
* `siftedSet_card_le_mul` — the `ℕ` bound `(y / P + 1) · ∏(q - min k q)`.
* `siftedSet_card_le` — the `ℝ` bound `y·∏(1 - min k q/q) + ∏(q - min k q)`.
* `siftedSet_card_le_pow` — same with error `w^{#S}`.

No `sorry`; kernel-checkable.
-/

namespace JSP314

open Finset

/-- The jointly sifted set: `r ∈ [1, y]` such that for every prime `q` with
`p < q ≤ w`, none of `p²·r + 1, …, p²·r + k` is divisible by `q`. -/
def siftedSet (y p k w : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    ∀ q ∈ (Finset.Ioc p w).filter Nat.Prime, ∀ j ∈ Finset.Icc 1 k,
      ¬ q ∣ p ^ 2 * r + j

/-- If `q ∣ m`, divisibility of `p²·r + j` by `q` depends only on `r mod m`. -/
theorem dvd_sq_mul_add_iff_dvd_mod {p q m r j : ℕ} (h : q ∣ m) :
    q ∣ p ^ 2 * r + j ↔ q ∣ p ^ 2 * (r % m) + j := by
  have hrm : r % m ≡ r [MOD q] := (Nat.mod_modEq r m).of_dvd h
  have h2 : p ^ 2 * (r % m) + j ≡ p ^ 2 * r + j [MOD q] :=
    (hrm.mul_left (p ^ 2)).add_right j
  constructor
  · intro hd
    rw [← Nat.modEq_zero_iff_dvd] at hd ⊢
    exact h2.trans hd
  · intro hd
    rw [← Nat.modEq_zero_iff_dvd] at hd ⊢
    exact h2.symm.trans hd

/-- Two elements of `Icc 1 q` congruent mod `q` are equal. -/
theorem eq_of_mod_eq_of_Icc {a b q : ℕ} (ha : a ∈ Finset.Icc 1 q)
    (hb : b ∈ Finset.Icc 1 q) (h : a % q = b % q) : a = b := by
  rw [Finset.mem_Icc] at ha hb
  rcases lt_or_eq_of_le ha.2 with hlt | rfl
  · rcases lt_or_eq_of_le hb.2 with hlt' | rfl
    · rwa [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at h
    · rw [Nat.mod_eq_of_lt hlt, Nat.mod_self] at h; omega
  · rcases lt_or_eq_of_le hb.2 with hlt' | rfl
    · rw [Nat.mod_self, Nat.mod_eq_of_lt hlt'] at h; omega
    · rfl

/-- **One-prime bound**: at most `q - min k q` residues `b mod q` keep all of
`p²·b + 1, …, p²·b + k` indivisible by `q`.  The forbidden residues
`-j·(p²)⁻¹ mod q` for `j = 1, …, k` hit at least `min k q` distinct classes. -/
theorem sifted_count_mod_prime_le {p k q : ℕ} (hq : 0 < q)
    (hco : Nat.Coprime (p ^ 2) q) :
    ((Finset.range q).filter
        (fun b => ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)).card
      ≤ q - min k q := by
  have : NeZero q := ⟨Nat.pos_iff_ne_zero.mp hq⟩
  -- a multiplicative inverse of `p²` in `ZMod q`
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime (p ^ 2) q).mpr hco
  have hi : ((p : ZMod q) ^ 2) * (↑u⁻¹ : ZMod q) = 1 := by
    rw [← Nat.cast_pow]; exact Units.mul_inv_of_eq hu
  -- the forbidden residues contain `j ↦ (-(u⁻¹·j)).val` for `j ∈ Icc 1 (min k q)`
  have hb : min k q ≤
      ((Finset.range q).filter
        (fun b => ¬ ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)).card := by
    have hmaps : Set.MapsTo (fun j : ℕ => (-(↑u⁻¹ * (j : ZMod q))).val)
        (↑(Finset.Icc 1 (min k q)) : Set ℕ)
        (↑((Finset.range q).filter
          (fun b => ¬ ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)) : Set ℕ) := by
      intro j hj
      rw [Finset.mem_coe, Finset.mem_Icc] at hj
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, ?_⟩
      intro hall
      have hjk : j ∈ Finset.Icc 1 k :=
        Finset.mem_Icc.mpr ⟨hj.1, hj.2.trans (min_le_left k q)⟩
      have hdvd : q ∣ p ^ 2 * (-(↑u⁻¹ * (j : ZMod q))).val + j := by
        rw [← ZMod.natCast_eq_zero_iff]
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
        rw [mul_neg, ← mul_assoc, hi, one_mul, neg_add_cancel]
      exact hall j hjk hdvd
    have hinj : Set.InjOn (fun j : ℕ => (-(↑u⁻¹ * (j : ZMod q))).val)
        (↑(Finset.Icc 1 (min k q)) : Set ℕ) := by
      intro a ha b hb' hab
      rw [Finset.mem_coe, Finset.mem_Icc] at ha hb'
      have h1 : (-(↑u⁻¹ * (a : ZMod q)) : ZMod q) = -(↑u⁻¹ * (b : ZMod q)) :=
        ZMod.val_injective q hab
      have h2 : (↑u⁻¹ : ZMod q) * a = ↑u⁻¹ * b := neg_injective h1
      have h3 : (a : ZMod q) = b := by
        have h4 := congrArg ((p ^ 2 : ZMod q) * ·) h2
        rwa [← mul_assoc, hi, one_mul, ← mul_assoc, hi, one_mul] at h4
      have hmod : a % q = b % q := (ZMod.natCast_eq_natCast_iff' a b q).mp h3
      exact eq_of_mod_eq_of_Icc
        (Finset.mem_Icc.mpr ⟨ha.1, ha.2.trans (min_le_right k q)⟩)
        (Finset.mem_Icc.mpr ⟨hb'.1, hb'.2.trans (min_le_right k q)⟩) hmod
    have hle := Finset.card_le_card_of_injOn
      (fun j : ℕ => (-(↑u⁻¹ * (j : ZMod q))).val) hmaps hinj
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at hle
  have hsum := Finset.card_filter_add_card_filter_not
    (p := fun b => ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)
    (s := Finset.range q)
  rw [Finset.card_range] at hsum
  omega

/-- **CRT factorization**: for coprime `P`, `Q`, the number of `r < P·Q` with
`A (r % P)` and `B (r % Q)` factors as the product of the separate counts. -/
theorem card_filter_range_mul {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q)
    (hco : Nat.Coprime P Q) {A B : ℕ → Prop} [DecidablePred A]
    [DecidablePred B] :
    ((Finset.range (P * Q)).filter (fun r => A (r % P) ∧ B (r % Q))).card
      = (((Finset.range P).filter A) ×ˢ ((Finset.range Q).filter B)).card := by
  apply Finset.card_bij' (fun r _ => (r % P, r % Q))
    (fun c _ => (Nat.chineseRemainder hco c.1 c.2 : ℕ))
  · intro r hr
    obtain ⟨hrlt, hrA, hrB⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_range, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt _ hP, hrA⟩, ⟨Nat.mod_lt _ hQ, hrB⟩⟩
  · intro c hc
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hc
    obtain ⟨haP, hA⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbQ, hB⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at haP hbQ
    have hclt : (Nat.chineseRemainder hco c.1 c.2 : ℕ) < P * Q :=
      Nat.chineseRemainder_lt_mul hco c.1 c.2
        (Nat.pos_iff_ne_zero.mp hP) (Nat.pos_iff_ne_zero.mp hQ)
    have hmodP : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % P = c.1 := by
      have h1 : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % P = c.1 % P :=
        (Nat.chineseRemainder hco c.1 c.2).prop.1
      rwa [Nat.mod_eq_of_lt haP] at h1
    have hmodQ : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % Q = c.2 := by
      have h1 : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % Q = c.2 % Q :=
        (Nat.chineseRemainder hco c.1 c.2).prop.2
      rwa [Nat.mod_eq_of_lt hbQ] at h1
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hclt, ?_, ?_⟩
    · rw [hmodP]; exact hA
    · rw [hmodQ]; exact hB
  · intro r hr
    obtain ⟨hrlt, -, -⟩ := Finset.mem_filter.mp hr
    rw [Finset.mem_range] at hrlt
    have hP1 : (Nat.chineseRemainder hco (r % P) (r % Q) : ℕ) ≡ r [MOD P] :=
      ((Nat.chineseRemainder hco _ _).prop.1).trans (Nat.mod_modEq r P)
    have hQ1 : (Nat.chineseRemainder hco (r % P) (r % Q) : ℕ) ≡ r [MOD Q] :=
      ((Nat.chineseRemainder hco _ _).prop.2).trans (Nat.mod_modEq r Q)
    have hPQ : (Nat.chineseRemainder hco (r % P) (r % Q) : ℕ) ≡ r [MOD P * Q] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨hP1, hQ1⟩
    have hclt : (Nat.chineseRemainder hco (r % P) (r % Q) : ℕ) < P * Q :=
      Nat.chineseRemainder_lt_mul hco _ _
        (Nat.pos_iff_ne_zero.mp hP) (Nat.pos_iff_ne_zero.mp hQ)
    have hmod : (Nat.chineseRemainder hco (r % P) (r % Q) : ℕ) % (P * Q)
        = r % (P * Q) := hPQ
    rwa [Nat.mod_eq_of_lt hclt, Nat.mod_eq_of_lt hrlt] at hmod
  · intro c hc
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hc
    obtain ⟨haP, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbQ, -⟩ := Finset.mem_filter.mp hb
    rw [Finset.mem_range] at haP hbQ
    have hmodP : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % P = c.1 := by
      have h1 : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % P = c.1 % P :=
        (Nat.chineseRemainder hco c.1 c.2).prop.1
      rwa [Nat.mod_eq_of_lt haP] at h1
    have hmodQ : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % Q = c.2 := by
      have h1 : (Nat.chineseRemainder hco c.1 c.2 : ℕ) % Q = c.2 % Q :=
        (Nat.chineseRemainder hco c.1 c.2).prop.2
      rwa [Nat.mod_eq_of_lt hbQ] at h1
    exact Prod.ext hmodP hmodQ

/-- **Period bound**: over a full period `range (∏_{q ∈ S} q)`, the number of
`r` with all translates `p²r + j` (`j = 1,…,k`) indivisible by every `q ∈ S`
is at most `∏_{q ∈ S} (q - min k q)`, for `S` a pairwise-coprime set of moduli
each coprime to `p`. -/
theorem sifted_count_period_le {p k : ℕ} :
    ∀ S : Finset ℕ,
      (∀ q ∈ S, Nat.Coprime p q) →
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b) →
      (∀ q ∈ S, 0 < q) →
      ((Finset.range (∏ q ∈ S, q)).filter
          (fun r => ∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
            ¬ q' ∣ p ^ 2 * r + j)).card
        ≤ ∏ q ∈ S, (q - min k q) := by
  intro S
  induction S using Finset.induction with
  | empty =>
      intro _ _ _
      simp only [Finset.prod_empty]
      exact Finset.card_le_card (Finset.filter_subset _ _)
        |>.trans_eq (Finset.card_range 1)
  | insert q S hqS ih =>
      intro hco hpw hpos
      have hq : 0 < q := hpos q (Finset.mem_insert_self q S)
      have hP : 0 < ∏ q' ∈ S, q' :=
        Finset.prod_pos fun q' hq' => hpos q' (Finset.mem_insert_of_mem hq')
      have hcoPq : Nat.Coprime (∏ q' ∈ S, q') q := by
        rw [Nat.coprime_prod_left_iff]
        intro q' hq'
        exact hpw q' (Finset.mem_insert_of_mem hq') q (Finset.mem_insert_self q S)
          (fun h => hqS (h ▸ hq'))
      have hcoq : Nat.Coprime (p ^ 2) q :=
        (Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2) p q).mpr
          (hco q (Finset.mem_insert_self q S))
      have hfilt :
          (Finset.range (∏ x ∈ insert q S, x)).filter
              (fun r => ∀ q' ∈ insert q S, ∀ j ∈ Finset.Icc 1 k,
                ¬ q' ∣ p ^ 2 * r + j)
            =
          (Finset.range ((∏ q' ∈ S, q') * q)).filter
              (fun r =>
                (∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
                  ¬ q' ∣ p ^ 2 * (r % (∏ q' ∈ S, q')) + j)
                ∧ ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * (r % q) + j) := by
        rw [Finset.prod_insert hqS, mul_comm q]
        apply Finset.filter_congr
        intro r _
        rw [Finset.forall_mem_insert]
        constructor
        · rintro ⟨hq, hS'⟩
          refine ⟨fun q' hq' j hj => ?_, fun j hj => ?_⟩
          · have hdP : q' ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem _ hq'
            rw [← dvd_sq_mul_add_iff_dvd_mod hdP]
            exact hS' q' hq' j hj
          · rw [← dvd_sq_mul_add_iff_dvd_mod (dvd_refl q)]
            exact hq j hj
        · rintro ⟨hS', hq⟩
          refine ⟨fun j hj => ?_, fun q' hq' j hj => ?_⟩
          · rw [dvd_sq_mul_add_iff_dvd_mod (dvd_refl q)]
            exact hq j hj
          · have hdP : q' ∣ ∏ x ∈ S, x := Finset.dvd_prod_of_mem _ hq'
            rw [dvd_sq_mul_add_iff_dvd_mod hdP]
            exact hS' q' hq' j hj
      rw [hfilt, Finset.prod_insert hqS]
      have hmul :
          ((Finset.range ((∏ q' ∈ S, q') * q)).filter
              (fun r =>
                (∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
                  ¬ q' ∣ p ^ 2 * (r % (∏ q' ∈ S, q')) + j)
                ∧ ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * (r % q) + j)).card
            =
          ((Finset.range (∏ q' ∈ S, q')).filter
              (fun a => ∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
                ¬ q' ∣ p ^ 2 * a + j)).card
            * ((Finset.range q).filter
              (fun b => ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)).card := by
        have h := card_filter_range_mul hP hq hcoPq
          (A := fun a => ∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
            ¬ q' ∣ p ^ 2 * a + j)
          (B := fun b => ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)
        rwa [Finset.card_product] at h
      rw [hmul]
      refine le_trans (Nat.mul_le_mul ?_ ?_) (le_of_eq (mul_comm _ _))
      · exact ih (fun q' hq' => hco q' (Finset.mem_insert_of_mem hq'))
          (fun a ha b hb hne =>
            hpw a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
              hne)
          (fun q' hq' => hpos q' (Finset.mem_insert_of_mem hq'))
      · exact sifted_count_mod_prime_le hq hcoq

/-- **Main ℕ bound**: the sifted set has at most
`(y / ∏S + 1) · ∏_{q ∈ S} (q - min k q)` elements, where `S` is the set of
primes in `(p, w]`. -/
theorem siftedSet_card_le_mul {p : ℕ} (hp : p.Prime) (y k w : ℕ) :
    (siftedSet y p k w).card
      ≤ (y / ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, q + 1)
          * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, (q - min k q) := by
  set S := (Finset.Ioc p w).filter Nat.Prime with hS
  set P := ∏ q ∈ S, q with hP
  have hprime : ∀ q ∈ S, q.Prime := fun q hq => (Finset.mem_filter.mp hq).2
  have hplt : ∀ q ∈ S, p < q :=
    fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  have hposS : ∀ q ∈ S, 0 < q := fun q hq => (hprime q hq).pos
  have hP0 : 0 < P := Finset.prod_pos hposS
  have hcard : (siftedSet y p k w).card ≤
      ((Finset.range (y / P + 1)) ×ˢ
        ((Finset.range P).filter
          (fun a => ∀ q' ∈ S, ∀ j ∈ Finset.Icc 1 k,
            ¬ q' ∣ p ^ 2 * a + j))).card := by
    apply Finset.card_le_card_of_injOn (fun r => (r / P, r % P))
    · intro r hr
      rw [Finset.mem_coe] at hr
      obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
      rw [Finset.mem_Icc] at hr1
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range,
        Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ⟨Nat.mod_lt _ hP0, ?_⟩⟩
      · exact Nat.lt_succ_iff.mpr (Nat.div_le_div_right hr1.2)
      · intro q' hq' j hj
        show ¬ q' ∣ p ^ 2 * (r % P) + j
        have hdP : q' ∣ P := by
          rw [hP]; exact Finset.dvd_prod_of_mem _ hq'
        rw [← dvd_sq_mul_add_iff_dvd_mod hdP]
        exact hr2 q' hq' j hj
    · intro a _ b _ hab
      injection hab with h1 h2
      rw [← Nat.mod_add_div a P, ← Nat.mod_add_div b P, h1, h2]
  rw [Finset.card_product, Finset.card_range] at hcard
  refine hcard.trans (Nat.mul_le_mul le_rfl ?_)
  exact sifted_count_period_le S
    (fun q hq =>
      (Nat.coprime_primes hp (hprime q hq)).mpr (ne_of_lt (hplt q hq)))
    (fun a ha b hb hne =>
      (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hne)
    hposS

/-- **Main bound (real form)**: with `S = {q prime : p < q ≤ w}` and
`P = ∏_{q ∈ S} q`,

    `#siftedSet ≤ y · ∏_{q ∈ S} (1 - min k q / q) + ∏_{q ∈ S} (q - min k q)`.

The first term is the sieve main term `~ y·∏_{p < q ≤ w} (1 - k/q)`; the
second is the period error `≤ P ≤ w^{#S}`. -/
theorem siftedSet_card_le {p : ℕ} (hp : p.Prime) (y k w : ℕ) :
    ((siftedSet y p k w).card : ℝ)
      ≤ y * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, (1 - ((min k q : ℕ) : ℝ) / q)
          + ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime,
              ((q : ℝ) - min k q) := by
  set S := (Finset.Ioc p w).filter Nat.Prime with hS
  set P := ∏ q ∈ S, q with hP
  set M := ∏ q ∈ S, (q - min k q) with hM
  have hprime : ∀ q ∈ S, q.Prime := fun q hq => (Finset.mem_filter.mp hq).2
  have hposS : ∀ q ∈ S, 0 < q := fun q hq => (hprime q hq).pos
  have hnat := siftedSet_card_le_mul hp y k w
  -- cast the pieces
  have hPcast : ((P : ℕ) : ℝ) = ∏ q ∈ S, (q : ℝ) := Nat.cast_prod _ _
  have hMcast : ((M : ℕ) : ℝ) = ∏ q ∈ S, ((q : ℝ) - min k q) := by
    rw [hM, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q hq
    rw [Nat.cast_sub (min_le_right k q)]
  have hPpos : (0 : ℝ) < P := by
    rw [← Nat.cast_zero, Nat.cast_lt]
    exact Finset.prod_pos hposS
  -- main-term product identity
  have hprod : (∏ q ∈ S, ((q : ℝ) - min k q)) / ∏ q ∈ S, (q : ℝ)
      = ∏ q ∈ S, (1 - ((min k q : ℕ) : ℝ) / q) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (hposS q hq))
    rw [sub_div, div_self hq0]
  calc ((siftedSet y p k w).card : ℝ)
      ≤ (((y / P + 1) * M : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    _ = ((y / P : ℕ) : ℝ) * (M : ℝ) + (M : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_one_mul]
    _ ≤ ((y : ℝ) / P) * (M : ℝ) + (M : ℝ) := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right Nat.cast_div_le (Nat.cast_nonneg _)) _
    _ = y * ((M : ℝ) / P) + (M : ℝ) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
    _ = y * ∏ q ∈ S, (1 - ((min k q : ℕ) : ℝ) / q)
          + ∏ q ∈ S, ((q : ℝ) - min k q) := by
        rw [hMcast, hPcast, ← hprod]

/-- **Explicit error bound**: `#siftedSet ≤ y·∏(1 - min k q/q) + w^{#S}` —
the period error is at most `w` raised to the number of sifted primes. -/
theorem siftedSet_card_le_pow {p : ℕ} (hp : p.Prime) (y k w : ℕ) :
    ((siftedSet y p k w).card : ℝ)
      ≤ y * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime, (1 - ((min k q : ℕ) : ℝ) / q)
          + (w : ℝ) ^ ((Finset.Ioc p w).filter Nat.Prime).card := by
  refine (siftedSet_card_le hp y k w).trans ?_
  apply add_le_add_right
  set S := (Finset.Ioc p w).filter Nat.Prime with hS
  have hw : ∀ q ∈ S, q ≤ w := fun q hq =>
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
  have hle : (∏ q ∈ S, (q - min k q) : ℕ) ≤ w ^ S.card := by
    calc (∏ q ∈ S, (q - min k q) : ℕ) ≤ ∏ q ∈ S, q :=
        Finset.prod_le_prod fun q _ => Nat.sub_le _ _
      _ ≤ ∏ _q ∈ S, w := Finset.prod_le_prod fun q hq => hw q hq
      _ = w ^ S.card := by rw [Finset.prod_const, Finset.card]
  have hcast : ((∏ q ∈ S, (q - min k q) : ℕ) : ℝ)
      = ∏ q ∈ S, ((q : ℝ) - min k q) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q hq
    rw [Nat.cast_sub (min_le_right k q)]
  rw [← hcast]
  exact_mod_cast hle

end JSP314
