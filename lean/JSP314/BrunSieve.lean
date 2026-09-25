import JSP314.JointSieve
import JSP314.FundamentalLemma

/-!
# JSP-000314 — Brun's pure sieve applied to the joint sifted set

We upgrade the crude period bound `siftedSet_card_le_pow` (whose error term
`w^{#S}` explodes) to a Brun-type truncated inclusion–exclusion bound: for any
finset `T` of primes, all `> p`, and any truncation parameter `t`,

  `#siftedOver y p k T
     ≤ y · ∏_{q ∈ T} (1 - min k q / q)
       + y · ∑_{s ⊆ T, #s > 2t} ∏_{q ∈ s} k / q
       + (1 + #T · k)^{2t}`.

The point is that the error `(1 + #T·k)^{2t}` is polynomial in the sieve data
for fixed `t`, while the tail `∑_{#s > 2t} ∏ k/q` is `o(1)` once
`2t ≫ e·k·∑_{q∈T} q⁻¹` by the Rankin bound `powerset_tail_le_exp`
(`tail ≤ z^{-2t} · exp(z·k·∑ q⁻¹)` for any `z ≥ 1`).

## Proof route

Write `N(r) = ∏_{j=1}^{k} (p²r + j)` and `P = ∏_{q ∈ T} q`.  Survival of `r`
is equivalent to `Coprime (N r) P`.  Brun's pure sieve (`brunNu`, proved in
`FundamentalLemma.lean`) gives `ν n ≥ [gcd n P = 1]`, so

  `#sifted ≤ ∑_{r ≤ y} ν(N r) = ∑_{d ∣ P} λ_d · #{r ≤ y : d ∣ N r}`.

For `d ∣ P` squarefree, `d ∣ N r` is a condition on `r mod d` with exactly
`ν_d = ∏_{q ∣ d} min k q` bad residue classes (CRT, `bad_count_period_eq`),
whence `|#{r ≤ y : d ∣ N r} - y·ν_d/d| ≤ ν_d`.  The truncated Möbius sum
`∑ λ_d ν_d/d` expands, over subsets of `T` of size `≤ 2t`, to
`∏_{q ∈ T} (1 - min k q / q)` minus a tail controlled by Rankin's trick, and
`∑ |λ_d| ν_d ≤ (1 + #T·k)^{2t}`.

## Main results

* `siftedOver_card_le_brun` — the bound above.
* `siftedOver_card_le_brun_exp` — same with the tail replaced by
  `z^{-2t}·exp(z·k·∑_{q∈T} q⁻¹)`.
* `siftedSet_card_le_brun` — specialization to `T =` primes of `(p, w]`.
* `siftedSet_card_le_brun_subset` — same over any prime subset `T ⊆ (p,w]`.

No placeholders; kernel-checkable.
-/

namespace JSP314

open Finset
open scoped ArithmeticFunction.Moebius

/-- The sifted set over an arbitrary finset `T` of sieve primes:
`r ∈ [1, y]` such that no `q ∈ T` divides any of `p²r + 1, …, p²r + k`. -/
def siftedOver (y p k : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter fun r =>
    ∀ q ∈ T, ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * r + j

/-- `siftedSet` is `siftedOver` at the primes of `(p, w]`. -/
theorem siftedSet_eq_siftedOver (y p k w : ℕ) :
    siftedSet y p k w = siftedOver y p k ((Finset.Ioc p w).filter Nat.Prime) :=
  rfl

/-- Enlarging the prime set shrinks the sifted set. -/
theorem siftedOver_subset {y p k : ℕ} {S T : Finset ℕ} (h : T ⊆ S) :
    siftedOver y p k S ⊆ siftedOver y p k T := by
  intro r hr
  rw [siftedOver, Finset.mem_filter] at hr ⊢
  exact ⟨hr.1, fun q hq j hj => hr.2 q (h hq) j hj⟩

/-- `N(r) = ∏_{j=1}^{k} (p²r + j)`; a prime divides `N r` iff it divides one
of the translates. -/
def Nprod (p k r : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 k, (p ^ 2 * r + j)

theorem Nprod_ne_zero (p k r : ℕ) : Nprod p k r ≠ 0 := by
  rw [Nprod, Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_Icc] at hj
  have : 0 < p ^ 2 * r + j := by omega
  exact this.ne'

/-- The bad residues mod `q`: those `b` for which `q` divides some
`p²b + j`, `j ∈ [1, k]`. -/
def badResidues (p k q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun b => ∃ j ∈ Finset.Icc 1 k, q ∣ p ^ 2 * b + j

/-- The bad residues are covered by the `k` classes `-j·(p²)⁻¹ mod q`,
so there are at most `min k q` of them (and at most `q`). -/
theorem badResidues_card_le {p k q : ℕ} (hq : 0 < q)
    (hco : Nat.Coprime (p ^ 2) q) :
    (badResidues p k q).card ≤ min k q := by
  have : NeZero q := ⟨Nat.pos_iff_ne_zero.mp hq⟩
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime (p ^ 2) q).mpr hco
  have hi : ((p : ZMod q) ^ 2) * (↑u⁻¹ : ZMod q) = 1 := by
    rw [← Nat.cast_pow]; exact Units.mul_inv_of_eq hu
  have hsub : badResidues p k q ⊆
      (Finset.Icc 1 k).image (fun j : ℕ => (-(↑u⁻¹ * (j : ZMod q))).val) := by
    intro b hb
    rw [badResidues, Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨hblt, j, hj, hdvd⟩ := hb
    rw [Finset.mem_image]
    refine ⟨j, hj, ?_⟩
    have hz : (b : ZMod q) = -(↑u⁻¹ * (j : ZMod q)) := by
      have h0 : ((p ^ 2 * b + j : ℕ) : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h0
      have hpb : (p : ZMod q) ^ 2 * (b : ZMod q) = -(j : ZMod q) :=
        eq_neg_of_add_eq_zero_left h0
      calc (b : ZMod q) = ↑u⁻¹ * ((p : ZMod q) ^ 2 * (b : ZMod q)) := by
            rw [← mul_assoc, mul_comm (↑u⁻¹ : ZMod q) ((p : ZMod q) ^ 2), hi,
              one_mul]
        _ = ↑u⁻¹ * -(j : ZMod q) := by rw [hpb]
        _ = -(↑u⁻¹ * (j : ZMod q)) := by rw [mul_neg]
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hblt] at hv
    exact hv.symm
  refine le_min ?_ ?_
  · calc (badResidues p k q).card
        ≤ ((Finset.Icc 1 k).image _).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 k).card := Finset.card_image_le
      _ = k := by rw [Nat.card_Icc]; omega
  · calc (badResidues p k q).card
        ≤ (Finset.range q).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = q := Finset.card_range q

/-- The bad count is exactly `min k q`: the upper bound above together with
`sifted_count_mod_prime_le` (which says at most `q - min k q` residues are
*good*). -/
theorem badResidues_card_eq {p k q : ℕ} (hq : 0 < q)
    (hco : Nat.Coprime (p ^ 2) q) :
    (badResidues p k q).card = min k q := by
  have hneg : badResidues p k q = (Finset.range q).filter
      (fun b => ¬ ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j) := by
    apply Finset.filter_congr
    intro b _
    constructor
    · rintro ⟨j, hj, hd⟩ hall
      exact hall j hj hd
    · intro hall
      by_contra h
      exact hall fun j hj hd => h ⟨j, hj, hd⟩
  have hsum := Finset.card_filter_add_card_filter_not
    (p := fun b => ∀ j ∈ Finset.Icc 1 k, ¬ q ∣ p ^ 2 * b + j)
    (s := Finset.range q)
  rw [Finset.card_range] at hsum
  rw [← hneg] at hsum
  have hle := sifted_count_mod_prime_le (k := k) hq hco
  have hge : min k q ≤ (badResidues p k q).card := by omega
  exact le_antisymm (badResidues_card_le hq hco) hge

/-- **CRT factorization (equality)**: over a full period `∏_{q ∈ S} q`, the
number of `r` that are bad for every `q' ∈ S` is the product of the
per-modulus bad counts.  Mirror of `sifted_count_period_le`. -/
theorem bad_count_period_eq {p k : ℕ} :
    ∀ S : Finset ℕ,
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b) →
      (∀ q ∈ S, 0 < q) →
      ((Finset.range (∏ q ∈ S, q)).filter
          (fun r => ∀ q' ∈ S, ∃ j ∈ Finset.Icc 1 k, q' ∣ p ^ 2 * r + j)).card
        = ∏ q ∈ S, (badResidues p k q).card := by
  intro S
  induction S using Finset.induction with
  | empty =>
    intro _ _
    rw [Finset.prod_empty]
    have htrue : (Finset.range 1).filter
        (fun r => ∀ q' ∈ (∅ : Finset ℕ), ∃ j ∈ Finset.Icc 1 k,
          q' ∣ p ^ 2 * r + j)
        = Finset.range 1 :=
      Finset.filter_true_of_mem fun r _ q' hq' =>
        absurd hq' (Finset.notMem_empty q')
    rw [htrue, Finset.card_range, Finset.prod_empty]
  | insert q S hqS ih =>
    intro hpw hpos
    have hq : 0 < q := hpos q (Finset.mem_insert_self q S)
    have hP : 0 < ∏ q' ∈ S, q' :=
      Finset.prod_pos fun q' hq' => hpos q' (Finset.mem_insert_of_mem hq')
    have hcoPq : Nat.Coprime (∏ q' ∈ S, q') q := by
      rw [Nat.coprime_prod_left_iff]
      intro q' hq'
      exact hpw q' (Finset.mem_insert_of_mem hq') q (Finset.mem_insert_self q S)
        (fun h => hqS (h ▸ hq'))
    have hfilt :
        (Finset.range (∏ x ∈ insert q S, x)).filter
            (fun r => ∀ q' ∈ insert q S, ∃ j ∈ Finset.Icc 1 k,
              q' ∣ p ^ 2 * r + j)
          =
        (Finset.range ((∏ q' ∈ S, q') * q)).filter
            (fun r =>
              (∀ q' ∈ S, ∃ j ∈ Finset.Icc 1 k,
                q' ∣ p ^ 2 * (r % (∏ q' ∈ S, q')) + j)
              ∧ ∃ j ∈ Finset.Icc 1 k, q ∣ p ^ 2 * (r % q) + j) := by
      rw [Finset.prod_insert hqS, mul_comm q]
      apply Finset.filter_congr
      intro r _
      rw [Finset.forall_mem_insert]
      constructor
      · rintro ⟨hq', hS'⟩
        refine ⟨fun q' hq'' => ?_, ?_⟩
        · obtain ⟨j, hj, hd⟩ := hS' q' hq''
          exact ⟨j, hj, (dvd_sq_mul_add_iff_dvd_mod
            (Finset.dvd_prod_of_mem _ hq'')).mp hd⟩
        · obtain ⟨j, hj, hd⟩ := hq'
          exact ⟨j, hj, (dvd_sq_mul_add_iff_dvd_mod (dvd_refl q)).mp hd⟩
      · rintro ⟨hS', hq'⟩
        obtain ⟨j, hj, hd⟩ := hq'
        refine ⟨⟨j, hj, (dvd_sq_mul_add_iff_dvd_mod (dvd_refl q)).mpr hd⟩,
          fun q' hq'' => ?_⟩
        obtain ⟨j', hj', hd'⟩ := hS' q' hq''
        exact ⟨j', hj', (dvd_sq_mul_add_iff_dvd_mod
          (Finset.dvd_prod_of_mem _ hq'')).mpr hd'⟩
    rw [hfilt, Finset.prod_insert hqS]
    have hmul := card_filter_range_mul hP hq hcoPq
      (A := fun a => ∀ q' ∈ S, ∃ j ∈ Finset.Icc 1 k,
        q' ∣ p ^ 2 * a + j)
      (B := fun b => ∃ j ∈ Finset.Icc 1 k, q ∣ p ^ 2 * b + j)
    rw [Finset.card_product] at hmul
    rw [hmul, ih (fun a ha b hb hne =>
          hpw a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hne)
        (fun q' hq' => hpos q' (Finset.mem_insert_of_mem hq'))]
    have hbeq : (Finset.range q).filter
        (fun b => ∃ j ∈ Finset.Icc 1 k, q ∣ p ^ 2 * b + j)
        = badResidues p k q := rfl
    rw [hbeq]

/-- The number of `b ∈ [0, d)` which are bad for every prime factor of the
squarefree `d` is `∏_{q ∣ d} min k q`. -/
theorem badSet_card_eq {p k d : ℕ} (hd : Squarefree d)
    (hco : ∀ q ∈ d.primeFactors, Nat.Coprime (p ^ 2) q) :
    ((Finset.range d).filter
        (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
          q ∣ p ^ 2 * r + j)).card
      = ∏ q ∈ d.primeFactors, min k q := by
  have h1 : ((Finset.range d).filter
      (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
        q ∣ p ^ 2 * r + j)).card
      = ∏ q ∈ d.primeFactors, (badResidues p k q).card := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
    rw [Nat.primeFactors_prod_primeFactors]
    exact bad_count_period_eq d.primeFactors
      (fun a ha b hb hne => (Nat.coprime_primes
        (Nat.prime_of_mem_primeFactors ha)
        (Nat.prime_of_mem_primeFactors hb)).mpr hne)
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).pos)
  rw [h1]
  exact Finset.prod_congr rfl fun q hq =>
    badResidues_card_eq (Nat.prime_of_mem_primeFactors hq).pos (hco q hq)

/-- Upper bound on the bad counts in `[1, y]`: at most `⌊y/d⌋ + 1` partial
periods. -/
theorem card_Icc_bad_le {p k y d : ℕ} (hd : Squarefree d)
    (hco : ∀ q ∈ d.primeFactors, Nat.Coprime (p ^ 2) q) :
    ((Finset.Icc 1 y).filter
        (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
          q ∣ p ^ 2 * r + j)).card
      ≤ (y / d + 1) * ∏ q ∈ d.primeFactors, min k q := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hcard : ((Finset.Icc 1 y).filter
      (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
        q ∣ p ^ 2 * r + j)).card
      ≤ ((Finset.range (y / d + 1)) ×ˢ
          (Finset.range d).filter
            (fun b => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
              q ∣ p ^ 2 * b + j)).card := by
    apply Finset.card_le_card_of_injOn (fun r => (r / d, r % d))
    · intro r hr
      obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
      rw [Finset.mem_Icc] at hr1
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range,
        Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ⟨Nat.mod_lt _ hd0, ?_⟩⟩
      · exact Nat.lt_succ_iff.mpr (Nat.div_le_div_right hr1.2)
      · intro q hq
        obtain ⟨j, hj, hdvd⟩ := hr2 q hq
        exact ⟨j, hj, (dvd_sq_mul_add_iff_dvd_mod
          (Nat.dvd_of_mem_primeFactors hq)).mp hdvd⟩
    · intro a _ b _ hab
      injection hab with h1 h2
      rw [← Nat.mod_add_div a d, ← Nat.mod_add_div b d, h1, h2]
  rw [Finset.card_product, Finset.card_range, badSet_card_eq hd hco] at hcard
  exact hcard

/-- Lower bound: the `⌊y/d⌋` complete periods inside `[1, y]` each contain
`∏ min k q` bad elements. -/
theorem card_Icc_bad_ge {p k y d : ℕ} (hd : Squarefree d)
    (hco : ∀ q ∈ d.primeFactors, Nat.Coprime (p ^ 2) q) :
    (y / d) * ∏ q ∈ d.primeFactors, min k q
      ≤ ((Finset.Icc 1 y).filter
          (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
            q ∣ p ^ 2 * r + j)).card := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  -- representative `g b ∈ [1, d]` of the class `b mod d`
  set g : ℕ → ℕ := fun b => if b = 0 then d else b with hg
  have hgmem : ∀ b ∈ Finset.range d, 1 ≤ g b ∧ g b ≤ d := by
    intro b hb
    rw [Finset.mem_range] at hb
    by_cases hb0 : b = 0
    · simp only [hg, hb0, ite_true]
      exact ⟨hd0, le_refl d⟩
    · simp only [hg, hb0, ite_false]
      omega
  have hkey : ∀ i b, b ∈ Finset.range d → (i * d + g b - 1) / d = i := by
    intro i b hb
    obtain ⟨hg1, hg2⟩ := hgmem b hb
    have hrew : i * d + g b - 1 = d * i + (g b - 1) := by
      rw [mul_comm i d]
      exact Nat.add_sub_assoc hg1 _
    rw [hrew, Nat.mul_add_div hd0]
    have : (g b - 1) / d = 0 := Nat.div_eq_zero_iff.mpr (Or.inr (by omega))
    omega
  have hcard : ((Finset.range (y / d)) ×ˢ
      (Finset.range d).filter
        (fun b => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
          q ∣ p ^ 2 * b + j)).card
      ≤ ((Finset.Icc 1 y).filter
          (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
            q ∣ p ^ 2 * r + j)).card := by
    apply Finset.card_le_card_of_injOn (fun pib => pib.1 * d + g pib.2)
    · rintro ⟨i, b⟩ hb'
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hb'
      obtain ⟨hi, hb⟩ := hb'
      obtain ⟨hbd, hbbad⟩ := Finset.mem_filter.mp hb
      rw [Finset.mem_range] at hbd
      obtain ⟨hg1, hg2⟩ := hgmem b (Finset.mem_range.mpr hbd)
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · omega
      · have h1 : (i + 1) * d ≤ (y / d) * d :=
          Nat.mul_le_mul (Nat.succ_le_of_lt hi) le_rfl
        have h2 : (y / d) * d ≤ y := Nat.div_mul_le_self y d
        calc i * d + g b ≤ i * d + d := Nat.add_le_add_left hg2 _
          _ = (i + 1) * d := (add_one_mul i d).symm
          _ ≤ y := h1.trans h2
      · intro q hq
        obtain ⟨j, hj, hdvd⟩ := hbbad q hq
        refine ⟨j, hj, ?_⟩
        have hxm : (i * d + g b) % d = b := by
          rcases eq_or_ne b 0 with hb0 | hb0
          · simp only [hg, hb0, ite_true]
            rw [show i * d + d = (i + 1) * d from (add_one_mul i d).symm,
              Nat.mul_mod_right, hb0]
          · simp only [hg, hb0, ite_false]
            rw [add_comm (i * d) b, Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt hbd]
        rw [dvd_sq_mul_add_iff_dvd_mod (Nat.dvd_of_mem_primeFactors hq), hxm]
        exact hdvd
    · rintro ⟨i₁, b₁⟩ h1 ⟨i₂, b₂⟩ h2 heq
      rw [Finset.mem_coe, Finset.mem_product] at h1 h2
      have hb1 := (Finset.mem_filter.mp h1.2).1
      have hb2 := (Finset.mem_filter.mp h2.2).1
      have h1' : (i₁ * d + g b₁ - 1) / d = i₁ := hkey i₁ b₁ hb1
      have h2' : (i₂ * d + g b₂ - 1) / d = i₂ := hkey i₂ b₂ hb2
      have hii : i₁ = i₂ := by
        have := congrArg (fun x => (x - 1) / d) heq
        rwa [h1', h2'] at this
      have hgg : g b₁ = g b₂ := by
        have := heq
        rw [hii] at this
        exact Nat.add_left_cancel this
      have hbb : b₁ = b₂ := by
        rw [Finset.mem_range] at hb1 hb2
        by_cases h10 : b₁ = 0 <;> by_cases h20 : b₂ = 0 <;>
          simp only [hg, h10, h20, ite_true, ite_false] at hgg <;> omega
      exact Prod.ext hii hbb
  rw [Finset.card_product, Finset.card_range, badSet_card_eq hd hco] at hcard
  exact hcard

/-- For squarefree `d`, `d ∣ N r` iff every prime factor of `d` divides some
translate `p²r + j`. -/
theorem dvd_Nprod_iff {p k r d : ℕ} (hd : Squarefree d) :
    d ∣ Nprod p k r
      ↔ ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k, q ∣ p ^ 2 * r + j := by
  have hNr : Nprod p k r ≠ 0 := Nprod_ne_zero _ _ _
  constructor
  · intro hdvd q hq
    have hqN : q ∣ Nprod p k r := (Nat.dvd_of_mem_primeFactors hq).trans hdvd
    exact ((Nat.prime_of_mem_primeFactors hq).prime.dvd_finsetProd_iff _).mp hqN
  · intro hall
    rw [← Nat.prod_primeFactors_of_squarefree hd,
      Nat.prod_primeFactors_dvd_iff hNr]
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    obtain ⟨j, hj, hjd⟩ := hall q hq
    have hqN : q ∣ Nprod p k r := hjd.trans (Finset.dvd_prod_of_mem _ hj)
    exact Nat.mem_primeFactors.mpr ⟨hqp, hqN, hNr⟩

/-- Generic powerset identity `∑_{s ⊆ S} (-1)^{#s} ∏_{q ∈ s} f q
= ∏_{q ∈ S} (1 - f q)` over `ℝ`. -/
theorem sum_powerset_neg_one_pow_mul_prod {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) :
    ∑ s ∈ S.powerset, (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q
      = ∏ q ∈ S, (1 - f q) := by
  have e : ∏ q ∈ S, (1 - f q) = ∏ q ∈ S, (-f q + 1) :=
    Finset.prod_congr rfl fun q _ => by ring
  rw [e, Finset.prod_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.prod_neg]
  simp [mul_comm]

/-- The truncated alternating powerset sum equals the full product minus the
high-degree tail. -/
theorem sum_powerset_card_le_eq {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ) (m : ℕ) :
    ∑ s ∈ S.powerset with s.card ≤ m, (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q
      = ∏ q ∈ S, (1 - f q)
        - ∑ s ∈ S.powerset with m < s.card, (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q := by
  have hdisj : Disjoint (S.powerset.filter fun s => s.card ≤ m)
      (S.powerset.filter fun s => ¬ s.card ≤ m) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hunion : S.powerset.filter (fun s => s.card ≤ m)
      ∪ S.powerset.filter (fun s => ¬ s.card ≤ m)
      = S.powerset := Finset.filter_union_filter_not_eq _ _
  have hsplit : ∑ s ∈ S.powerset, (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q
      = ∑ s ∈ S.powerset with s.card ≤ m, (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q
        + ∑ s ∈ S.powerset with ¬ s.card ≤ m,
            (-1 : ℝ) ^ s.card * ∏ q ∈ s, f q := by
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union hdisj]
  rw [sum_powerset_neg_one_pow_mul_prod S f] at hsplit
  have hflt : S.powerset.filter (fun s => ¬ s.card ≤ m)
      = S.powerset.filter fun s => m < s.card :=
    Finset.filter_congr fun s _ => not_le
  rw [hflt] at hsplit
  rw [← hsplit]
  ring

/-- Divisor sums over a squarefree `P` of a function of `d.primeFactors`
supported on `#d.primeFactors ≤ m` become sums over the powerset of
`P.primeFactors`. -/
theorem sum_divisors_card_le_eq {P : ℕ} (hP : Squarefree P) {m : ℕ}
    (g : Finset ℕ → ℝ) :
    ∑ d ∈ P.divisors,
        (if d.primeFactors.card ≤ m then g d.primeFactors else 0)
      = ∑ s ∈ P.primeFactors.powerset with s.card ≤ m, g s := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (i := fun d : ℕ => d.primeFactors)
    (j := fun s : Finset ℕ => ∏ q ∈ s, q) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Nat.primeFactors_mono (Nat.mem_divisors.mp hd.1).1 hP.ne_zero), hd.2⟩
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    have hdvd : ∏ q ∈ s, q ∣ P := by
      rw [← Nat.prod_primeFactors_of_squarefree hP]
      exact Finset.prod_dvd_prod_of_subset s P.primeFactors _ hs.1
    have hpfs : (∏ q ∈ s, q).primeFactors = s :=
      Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors (hs.1 hq)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdvd, hP.ne_zero⟩, by rw [hpfs]; exact hs.2⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd.1).1 hP)
  · intro s hs
    exact Nat.primeFactors_prod fun q hq =>
      Nat.prime_of_mem_primeFactors
        ((Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1) hq)
  · intro d hd
    rfl

/-- **Rankin bound**: for `z ≥ 1` and pointwise nonnegative `f`,
`z^{2t} · ∑_{s ⊆ S, #s > 2t} ∏_{q ∈ s} f q ≤ ∏_{q ∈ S} (1 + z f q)
≤ exp(z · ∑ f q)`. -/
theorem powerset_tail_le_exp {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ) (hf : ∀ q, 0 ≤ f q) (t : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    z ^ (2 * t) * ∑ s ∈ S.powerset with 2 * t < s.card, ∏ q ∈ s, f q
      ≤ Real.exp (z * ∑ q ∈ S, f q) := by
  have hprod : ∏ q ∈ S, (1 + z * f q)
      = ∑ s ∈ S.powerset, (∏ q ∈ s, f q) * z ^ s.card := by
    have e : ∏ q ∈ S, (1 + z * f q) = ∏ q ∈ S, (f q * z + 1) :=
      Finset.prod_congr rfl fun q _ => by ring
    rw [e, Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.prod_mul_pow_card]
    simp
  calc z ^ (2 * t) * ∑ s ∈ S.powerset with 2 * t < s.card, ∏ q ∈ s, f q
      = ∑ s ∈ S.powerset with 2 * t < s.card,
          (∏ q ∈ s, f q) * z ^ (2 * t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
    _ ≤ ∑ s ∈ S.powerset with 2 * t < s.card,
          (∏ q ∈ s, f q) * z ^ s.card := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_filter] at hs
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hz (Nat.le_of_lt hs.2))
          (Finset.prod_nonneg fun q _ => hf q)
    _ ≤ ∑ s ∈ S.powerset, (∏ q ∈ s, f q) * z ^ s.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun s _ _ => mul_nonneg
            (Finset.prod_nonneg fun q _ => hf q)
            (pow_nonneg (by linarith) _)
    _ = ∏ q ∈ S, (1 + z * f q) := hprod.symm
    _ ≤ Real.exp (∑ q ∈ S, z * f q) :=
        Real.prod_one_add_le_exp_sum _ fun q =>
          mul_nonneg (by linarith) (hf q)
    _ = Real.exp (z * ∑ q ∈ S, f q) := by rw [← Finset.mul_sum]

/-- For squarefree `d` whose prime factors are primes `> p`, the count
`A_d = #{r ∈ [1,y] : d ∣ N r}` satisfies `|A_d - y·ν_d/d| ≤ ν_d` where
`ν_d = ∏_{q ∣ d} min k q`. -/
theorem abs_card_dvd_Nprod_sub {p k y d : ℕ} (hd : Squarefree d)
    (hco : ∀ q ∈ d.primeFactors, Nat.Coprime (p ^ 2) q) :
    |(((Finset.Icc 1 y).filter fun r => d ∣ Nprod p k r).card : ℝ)
        - (y : ℝ) / d * (∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ))| ≤
      ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) := by
  set B := ∏ q ∈ d.primeFactors, min k q with hB
  have hBcast : ((B : ℕ) : ℝ) = ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) :=
    Nat.cast_prod _ _
  rw [← hBcast]
  have hAeq : ((Finset.Icc 1 y).filter fun r => d ∣ Nprod p k r)
      = (Finset.Icc 1 y).filter
          (fun r => ∀ q ∈ d.primeFactors, ∃ j ∈ Finset.Icc 1 k,
            q ∣ p ^ 2 * r + j) :=
    Finset.filter_congr fun r _ => dvd_Nprod_iff hd
  have hd0 : (0 : ℝ) < d := by
    have h1 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
    exact_mod_cast h1
  have hBnn : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
  have hfl1 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
  have hfl2 : (y : ℝ) / d ≤ ((y / d : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hd0]
    have h1 : y ≤ (y / d + 1) * d := by
      calc y = d * (y / d) + y % d := (Nat.div_add_mod y d).symm
        _ ≤ d * (y / d) + d :=
            Nat.add_le_add_left
              (Nat.mod_lt y (Nat.pos_of_ne_zero hd.ne_zero)).le _
        _ = (y / d + 1) * d := by rw [add_mul, one_mul]
    have h2 : (y : ℝ) ≤ ((y / d + 1) * d : ℕ) := by exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  have hAup : (((Finset.Icc 1 y).filter fun r => d ∣ Nprod p k r).card : ℝ)
      ≤ ((y / d : ℕ) : ℝ) * B + B := by
    have h := hAeq ▸ card_Icc_bad_le hd hco
    calc (((Finset.Icc 1 y).filter fun r => d ∣ Nprod p k r).card : ℝ)
        ≤ (((y / d + 1) * B : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((y / d : ℕ) : ℝ) * B + B := by
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, add_one_mul]
  have hAlo : ((y / d : ℕ) : ℝ) * B
      ≤ (((Finset.Icc 1 y).filter fun r => d ∣ Nprod p k r).card : ℝ) := by
    have h := hAeq ▸ card_Icc_bad_ge hd hco
    exact_mod_cast h
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-B ≤ A - y/d·B`: from `A ≥ fl·B` and `y/d·B ≤ (fl+1)·B`
    have h3 : (y : ℝ) / d * B ≤ ((y / d : ℕ) : ℝ) * B + B := by
      have := mul_le_mul_of_nonneg_right hfl2 hBnn
      rw [add_mul, one_mul] at this
      exact this
    linarith
  · -- `A - y/d·B ≤ B`: from `A ≤ (fl+1)·B` and `fl·B ≤ y/d·B`
    have h3 : ((y / d : ℕ) : ℝ) * B ≤ (y : ℝ) / d * B :=
      mul_le_mul_of_nonneg_right hfl1 hBnn
    linarith

/-- **Main bound**: `#{r ∈ [1,y] sifted over T} ≤` Brun main term plus the
truncation error. -/
theorem siftedOver_card_le_brun {p : ℕ} (hp : p.Prime) (y k : ℕ) (t : ℕ)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hpT : ∀ q ∈ T, p < q) :
    ((siftedOver y p k T).card : ℝ)
      ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
          + y * ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
          + (1 + T.card * k) ^ (2 * t) := by
  set P := ∏ q ∈ T, q with hPdef
  have hPs : Squarefree P := by
    rw [hPdef]
    apply Finset.squarefree_prod_of_pairwise_isCoprime _ fun q hq =>
      (hT q hq).squarefree
    intro a ha b hb hab
    simp only [Function.onFun]
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hT a ha) (hT b hb)).mpr hab)
  have hP0 : P ≠ 0 := hPs.ne_zero
  have hPpf : P.primeFactors = T := by
    rw [hPdef]; exact Nat.primeFactors_prod hT
  -- per-divisor facts
  have hd_sq : ∀ d ∈ P.divisors, Squarefree d := fun d hd =>
    Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hPs
  have hpf_sub : ∀ d ∈ P.divisors, d.primeFactors ⊆ T := fun d hd => by
    rw [← hPpf]
    exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hP0
  have hco : ∀ d ∈ P.divisors, ∀ q ∈ d.primeFactors,
      Nat.Coprime (p ^ 2) q := by
    intro d hd q hq
    have hqT : q ∈ T := hpf_sub d hd hq
    have hqp : q.Prime := hT q hqT
    exact (Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2) _ _).mpr
      ((Nat.coprime_primes hp hqp).mpr (ne_of_lt (hpT q hqT)))
  -- (a) sifted ⇒ coprime ⇒ ν = 1
  have hcop : ∀ r ∈ siftedOver y p k T, Nat.Coprime (Nprod p k r) P := by
    intro r hr
    rw [siftedOver, Finset.mem_filter] at hr
    apply Nat.coprime_of_dvd
    intro q hqp hqN hqP
    have hqT : q ∈ T := by
      rw [← hPpf]
      exact Nat.mem_primeFactors.mpr ⟨hqp, hqP, hP0⟩
    obtain ⟨j, hj, hjd⟩ := (hqp.prime.dvd_finsetProd_iff _).mp hqN
    exact hr.2 q hqT j hj hjd
  -- (b) card ≤ ∑ ν(N r)
  have hcard_le : ((siftedOver y p k T).card : ℤ)
      ≤ ∑ r ∈ Finset.Icc 1 y, brunNu P t (Nprod p k r) := by
    calc ((siftedOver y p k T).card : ℤ)
        = ∑ r ∈ siftedOver y p k T, (1 : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ r ∈ siftedOver y p k T, brunNu P t (Nprod p k r) :=
          Finset.sum_congr rfl fun r hr =>
            (brunNu_eq_one_of_coprime hPs (Nprod_ne_zero _ _ _)
              (hcop r hr)).symm
      _ ≤ ∑ r ∈ Finset.Icc 1 y, brunNu P t (Nprod p k r) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun r hr _ => brunNu_nonneg hPs (Nprod_ne_zero _ _ _)
  -- (c) interchange ∑_r ∑_{d | N r} = ∑_{d | P} λ_d · A_d
  have hswap : ∑ r ∈ Finset.Icc 1 y, brunNu P t (Nprod p k r)
      = ∑ d ∈ P.divisors, brunLambda P t d
          * (((Finset.Icc 1 y).filter fun r =>
              d ∣ Nprod p k r).card : ℤ) := by
    have step : ∀ r ∈ Finset.Icc 1 y, brunNu P t (Nprod p k r)
        = ∑ d ∈ P.divisors,
            (if d ∣ Nprod p k r then brunLambda P t d else 0) := by
      intro r _
      have hNr : Nprod p k r ≠ 0 := Nprod_ne_zero _ _ _
      rw [brunNu]
      have hset : (Nprod p k r).divisors ∩ P.divisors
          = P.divisors.filter (· ∣ Nprod p k r) := by
        ext d
        simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd1, -⟩, hd2, -⟩
          exact ⟨⟨hd2, hP0⟩, hd1⟩
        · rintro ⟨⟨hd2, -⟩, hd1⟩
          exact ⟨⟨hd1, hNr⟩, ⟨hd2, hP0⟩⟩
      have hsub : ∑ d ∈ (Nprod p k r).divisors, brunLambda P t d
          = ∑ d ∈ (Nprod p k r).divisors ∩ P.divisors,
              brunLambda P t d := by
        refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
        intro d hd hdnot
        rw [Finset.mem_inter] at hdnot
        exact brunLambda_of_not_dvd
          fun h => hdnot ⟨hd, Nat.mem_divisors.mpr ⟨h, hP0⟩⟩
      rw [hsub, hset]
      exact Finset.sum_filter _ _
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- (d) cast to ℝ and insert the per-level error bound
  have hcardR : ((siftedOver y p k T).card : ℝ)
      ≤ ∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
          * (((Finset.Icc 1 y).filter fun r =>
              d ∣ Nprod p k r).card : ℝ) := by
    have h1 : ((siftedOver y p k T).card : ℤ)
        ≤ ∑ d ∈ P.divisors, brunLambda P t d
            * (((Finset.Icc 1 y).filter fun r =>
                d ∣ Nprod p k r).card : ℤ) :=
      hcard_le.trans_eq hswap
    have h2 : ((siftedOver y p k T).card : ℝ)
        ≤ ((∑ d ∈ P.divisors, brunLambda P t d
            * (((Finset.Icc 1 y).filter fun r =>
                d ∣ Nprod p k r).card : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast h1
    rw [Int.cast_sum] at h2
    refine h2.trans_eq ?_
    apply Finset.sum_congr rfl
    intro d _
    push_cast
    ring
  -- per-level bound `λ_d · A_d ≤ λ_d · yν_d/d + |λ_d| ν_d`
  have hterm : ∀ d ∈ P.divisors,
      (brunLambda P t d : ℝ)
          * (((Finset.Icc 1 y).filter fun r =>
              d ∣ Nprod p k r).card : ℝ)
        ≤ (brunLambda P t d : ℝ)
            * ((y : ℝ) / d * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ))
          + |(brunLambda P t d : ℝ)|
            * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) := by
    intro d hd
    have habs := abs_card_dvd_Nprod_sub (hd_sq d hd) (hco d hd)
    have h2 := abs_le.mp habs
    have heq : (brunLambda P t d : ℝ)
          * (((Finset.Icc 1 y).filter fun r =>
              d ∣ Nprod p k r).card : ℝ)
        = (brunLambda P t d : ℝ)
            * ((y : ℝ) / d * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ))
          + (brunLambda P t d : ℝ)
            * ((((Finset.Icc 1 y).filter fun r =>
                  d ∣ Nprod p k r).card : ℝ)
                - (y : ℝ) / d * ∏ q ∈ d.primeFactors,
                    ((min k q : ℕ) : ℝ)) := by ring
    rw [heq]
    apply add_le_add_left
    calc (brunLambda P t d : ℝ)
          * ((((Finset.Icc 1 y).filter fun r =>
                d ∣ Nprod p k r).card : ℝ)
              - (y : ℝ) / d * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ))
        ≤ |(brunLambda P t d : ℝ)
            * ((((Finset.Icc 1 y).filter fun r =>
                  d ∣ Nprod p k r).card : ℝ)
                - (y : ℝ) / d * ∏ q ∈ d.primeFactors,
                    ((min k q : ℕ) : ℝ))| := le_abs_self _
      _ = |(brunLambda P t d : ℝ)|
            * |(((Finset.Icc 1 y).filter fun r =>
                  d ∣ Nprod p k r).card : ℝ)
                - (y : ℝ) / d * ∏ q ∈ d.primeFactors,
                    ((min k q : ℕ) : ℝ)| := abs_mul _ _
      _ ≤ |(brunLambda P t d : ℝ)|
            * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  -- (e) assemble: card ≤ y·(main sum) + (error sum)
  have hbound : ((siftedOver y p k T).card : ℝ)
      ≤ y * (∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
              * (∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)) / d)
          + ∑ d ∈ P.divisors, |(brunLambda P t d : ℝ)|
              * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) := by
    refine hcardR.trans ?_
    calc ∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
            * (((Finset.Icc 1 y).filter fun r =>
                d ∣ Nprod p k r).card : ℝ)
        ≤ ∑ d ∈ P.divisors, ((brunLambda P t d : ℝ)
              * ((y : ℝ) / d * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ))
            + |(brunLambda P t d : ℝ)|
              * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)) :=
          Finset.sum_le_sum fun d hd => hterm d hd
      _ = (∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
              * ((y : ℝ) / d * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)))
            + ∑ d ∈ P.divisors, |(brunLambda P t d : ℝ)|
                * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) :=
          Finset.sum_add_distrib
      _ = y * (∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
              * (∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)) / d)
            + ∑ d ∈ P.divisors, |(brunLambda P t d : ℝ)|
                * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          ring
  -- (f) divisor sums → powerset sums
  have hmain : ∑ d ∈ P.divisors, (brunLambda P t d : ℝ)
        * (∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)) / d
      = ∑ s ∈ T.powerset with s.card ≤ 2 * t,
          (-1 : ℝ) ^ s.card
            * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q := by
    have hstep : ∀ d ∈ P.divisors, (brunLambda P t d : ℝ)
          * (∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)) / d
        = if d.primeFactors.card ≤ 2 * t then
            (-1 : ℝ) ^ d.primeFactors.card
              * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ) / q
          else 0 := by
      intro d hd
      have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
      have hdsq := hd_sq d hd
      by_cases hω : d.primeFactors.card ≤ 2 * t
      · rw [brunLambda_of_dvd hdvd hω, if_pos hω]
        have hμ : (μ d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
          have hμ' : (μ d : ℤ) = (-1 : ℤ) ^ d.primeFactors.card := by
            conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
            exact moebius_prod_primeFactors subset_rfl
          exact_mod_cast hμ'
        have hdd : (d : ℝ) = ∏ q ∈ d.primeFactors, (q : ℝ) := by
          conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
          rw [Nat.cast_prod]
        rw [hμ, hdd, mul_div_assoc, ← Finset.prod_div_distrib]
      · rw [if_neg hω,
          show brunLambda P t d = 0 from if_neg fun h => hω h.2]
        simp
    rw [Finset.sum_congr rfl hstep,
      sum_divisors_card_le_eq hPs
        (g := fun s => (-1 : ℝ) ^ s.card
          * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q),
      hPpf]
  have herr : ∑ d ∈ P.divisors, |(brunLambda P t d : ℝ)|
        * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)
      = ∑ s ∈ T.powerset with s.card ≤ 2 * t,
          ∏ q ∈ s, ((min k q : ℕ) : ℝ) := by
    have hstep : ∀ d ∈ P.divisors, |(brunLambda P t d : ℝ)|
          * ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)
        = if d.primeFactors.card ≤ 2 * t then
            ∏ q ∈ d.primeFactors, ((min k q : ℕ) : ℝ)
          else 0 := by
      intro d hd
      have hdvd : d ∣ P := Nat.dvd_of_mem_divisors hd
      have hdsq := hd_sq d hd
      by_cases hω : d.primeFactors.card ≤ 2 * t
      · rw [brunLambda_of_dvd hdvd hω, if_pos hω]
        have hμabs : |(μ d : ℝ)| = 1 := by
          have hμz : (μ d : ℤ) ≠ 0 :=
            ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdsq
          have hμ1 : |μ d| ≤ 1 := ArithmeticFunction.abs_moebius_le_one d
          have hμz' : (μ d : ℤ) = 1 ∨ μ d = -1 := by
            rcases eq_or_ne (μ d) 1 with h | h
            · exact Or.inl h
            · rcases eq_or_ne (μ d) (-1) with h | h
              · exact Or.inr h
              · exfalso
                rw [abs_le] at hμ1
                omega
          rcases hμz' with h | h <;> rw [h] <;> norm_num
        rw [hμabs, one_mul]
      · rw [if_neg hω,
          show brunLambda P t d = 0 from if_neg fun h => hω h.2]
        simp
    rw [Finset.sum_congr rfl hstep,
      sum_divisors_card_le_eq hPs
        (g := fun s => ∏ q ∈ s, ((min k q : ℕ) : ℝ)),
      hPpf]
  -- (g) evaluate the truncated main sum and bound the error sum
  have hsplit := sum_powerset_card_le_eq T
    (fun q => ((min k q : ℕ) : ℝ) / q) (2 * t)
  have htailabs :
      |∑ s ∈ T.powerset with 2 * t < s.card,
          (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q|
        ≤ ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q := by
    calc |∑ s ∈ T.powerset with 2 * t < s.card,
            (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q|
        ≤ ∑ s ∈ T.powerset with 2 * t < s.card,
            |(-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ T.powerset with 2 * t < s.card,
            ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q := by
          apply Finset.sum_congr rfl
          intro s _
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_nonneg (Finset.prod_nonneg fun q _ =>
              div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      _ ≤ ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_filter, Finset.mem_powerset] at hs
          apply Finset.prod_le_prod₀
          · intro q _
            exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          · intro q hq
            have hqpos : (0 : ℝ) < q :=
              Nat.cast_pos.mpr (hT q (hs.1 hq)).pos
            rw [div_le_div_iff₀ hqpos hqpos]
            exact Nat.cast_le.mpr (min_le_left k q)
  have herrbd : ∑ s ∈ T.powerset with s.card ≤ 2 * t,
        ∏ q ∈ s, ((min k q : ℕ) : ℝ)
      ≤ (1 + T.card * k : ℝ) ^ (2 * t) := by
    calc ∑ s ∈ T.powerset with s.card ≤ 2 * t,
            ∏ q ∈ s, ((min k q : ℕ) : ℝ)
        ≤ ∑ s ∈ T.powerset with s.card ≤ 2 * t, (k : ℝ) ^ s.card := by
          apply Finset.sum_le_sum
          intro s _
          calc ∏ q ∈ s, ((min k q : ℕ) : ℝ)
              ≤ ∏ _q ∈ s, (k : ℝ) :=
                Finset.prod_le_prod₀ (fun q _ => Nat.cast_nonneg _)
                  fun q _ => Nat.cast_le.mpr (min_le_left k q)
            _ = (k : ℝ) ^ s.card := Finset.prod_const
      _ = ∑ s ∈ T.powerset,
            (if s.card ≤ 2 * t then (k : ℝ) ^ s.card else 0) :=
          Finset.sum_filter _ _
      _ = ∑ j ∈ Finset.range (T.card + 1),
            (T.card.choose j : ℝ)
              * (if j ≤ 2 * t then (k : ℝ) ^ j else 0) := by
          have h := Finset.sum_powerset_apply_card
            (f := fun j => if j ≤ 2 * t then (k : ℝ) ^ j else 0) (x := T)
          refine h.trans ?_
          apply Finset.sum_congr rfl
          intro j _
          simp only [nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range (T.card + 1),
            (if j ≤ 2 * t then ((T.card : ℝ) * k) ^ j else 0) := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j ≤ 2 * t
          · rw [if_pos hj, if_pos hj]
            calc (T.card.choose j : ℝ) * (k : ℝ) ^ j
                ≤ (T.card : ℝ) ^ j * (k : ℝ) ^ j :=
                  mul_le_mul_of_nonneg_right
                    (Nat.cast_le.mpr (Nat.choose_le_pow _ _))
                    (pow_nonneg (Nat.cast_nonneg _) _)
              _ = ((T.card : ℝ) * k) ^ j := (mul_pow _ _ _).symm
          · rw [if_neg hj, if_neg hj]
      _ = ∑ j ∈ (Finset.range (T.card + 1)).filter (fun j => j ≤ 2 * t),
            ((T.card : ℝ) * k) ^ j := by
          rw [Finset.sum_filter]
      _ ≤ ∑ j ∈ Finset.range (2 * t + 1), ((T.card : ℝ) * k) ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            rw [Finset.mem_filter, Finset.mem_range] at hj
            rw [Finset.mem_range]
            omega
          · intro j _ _
            exact pow_nonneg (by positivity) _
      _ ≤ (1 + T.card * k : ℝ) ^ (2 * t) := by
          have hx : (0 : ℝ) ≤ (T.card : ℝ) * k := by positivity
          rw [add_comm (1 : ℝ) ((T.card : ℝ) * k), add_pow]
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_range] at hj
          have hc1 : (1 : ℝ) ≤ ((2 * t).choose j : ℝ) := by
            exact_mod_cast Nat.choose_pos (by omega : j ≤ 2 * t)
          have h1 : ((T.card : ℝ) * k) ^ j * (1 : ℝ) ^ (2 * t - j)
              = ((T.card : ℝ) * k) ^ j := by rw [one_pow, mul_one]
          rw [h1]
          exact le_mul_of_one_le_right (pow_nonneg hx _) hc1
  -- (h) combine
  rw [hmain, hsplit] at hbound
  rw [herr] at hbound
  refine hbound.trans ?_
  rw [mul_sub]
  have ht0 : 0 ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
      - y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q) := sub_self _ ▸ le_refl _
  have hmain_nn : 0 ≤ (y : ℝ) := Nat.cast_nonneg _
  calc y * (∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
          - ∑ s ∈ T.powerset with 2 * t < s.card,
              (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q)
        + ∑ s ∈ T.powerset with s.card ≤ 2 * t,
            ∏ q ∈ s, ((min k q : ℕ) : ℝ)
      = y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
        - y * ∑ s ∈ T.powerset with 2 * t < s.card,
            (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q
        + ∑ s ∈ T.powerset with s.card ≤ 2 * t,
            ∏ q ∈ s, ((min k q : ℕ) : ℝ) := by ring
    _ ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
        + y * ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
        + (1 + T.card * k : ℝ) ^ (2 * t) := by
        have hneg :
            - y * ∑ s ∈ T.powerset with 2 * t < s.card,
                (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q
              ≤ y * ∑ s ∈ T.powerset with 2 * t < s.card,
                  ∏ q ∈ s, (k : ℝ) / q := by
          have h1 := mul_le_mul_of_nonneg_left htailabs hmain_nn
          -- −y·X ≤ y·|X| ≤ y·tail
          calc - y * ∑ s ∈ T.powerset with 2 * t < s.card,
                  (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q
              ≤ y * |∑ s ∈ T.powerset with 2 * t < s.card,
                  (-1 : ℝ) ^ s.card * ∏ q ∈ s, ((min k q : ℕ) : ℝ) / q| := by
                rw [← mul_neg]
                apply mul_le_mul_of_nonneg_left _ hmain_nn
                exact neg_le_abs _
            _ ≤ y * ∑ s ∈ T.powerset with 2 * t < s.card,
                    ∏ q ∈ s, (k : ℝ) / q := h1
        linarith [herrbd]

/-- **Brun bound, exponential tail form**: for any `z ≥ 1`,
`#sifted ≤ y·∏(1 − min k q/q) + y·exp(z·k·∑ q⁻¹)/z^{2t} + (1 + #T·k)^{2t}`.
Choosing `z = 2t / (k·∑ q⁻¹)` (when ≥ 1) gives the classical
`tail ≤ (e·k·σ / 2t)^{2t}` shape. -/
theorem siftedOver_card_le_brun_exp {p : ℕ} (hp : p.Prime) (y k : ℕ) (t : ℕ)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hpT : ∀ q ∈ T, p < q)
    {z : ℝ} (hz : 1 ≤ z) :
    ((siftedOver y p k T).card : ℝ)
      ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
          + y * Real.exp (z * k * ∑ q ∈ T, (q : ℝ)⁻¹) / z ^ (2 * t)
          + (1 + T.card * k : ℝ) ^ (2 * t) := by
  have hmain := siftedOver_card_le_brun hp y k t T hT hpT
  have htail := powerset_tail_le_exp T (fun q => (k : ℝ) / q)
    (fun q => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) t hz
  have hsum : ∑ q ∈ T, (k : ℝ) / q = k * ∑ q ∈ T, (q : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [div_eq_mul_inv]
  rw [hsum, ← mul_assoc] at htail
  have hzpos : (0 : ℝ) < z := by linarith
  have htail' : ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
      ≤ Real.exp (z * k * ∑ q ∈ T, (q : ℝ)⁻¹) / z ^ (2 * t) := by
    rw [le_div_iff₀ (pow_pos hzpos _), mul_comm]
    exact htail
  refine hmain.trans ?_
  apply add_le_add_right
  apply add_le_add_left
  rw [← mul_div_assoc]
  exact mul_le_mul_of_nonneg_left htail' (Nat.cast_nonneg _)

/-- **Brun bound for `siftedSet`** over the full prime set `S` of `(p, w]`. -/
theorem siftedSet_card_le_brun {p : ℕ} (hp : p.Prime) (y k w t : ℕ) :
    ((siftedSet y p k w).card : ℝ)
      ≤ y * ∏ q ∈ (Finset.Ioc p w).filter Nat.Prime,
            (1 - ((min k q : ℕ) : ℝ) / q)
          + y * ∑ s ∈ ((Finset.Ioc p w).filter Nat.Prime).powerset
                with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
          + (1 + ((Finset.Ioc p w).filter Nat.Prime).card * k : ℝ)
              ^ (2 * t) := by
  rw [siftedSet_eq_siftedOver]
  exact siftedOver_card_le_brun hp y k t _
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1)

/-- **Brun bound for `siftedSet`, restricted to a prime subset** `T ⊆ (p,w]`:
this is the form intended for band estimates — take `T` small. -/
theorem siftedSet_card_le_brun_subset {p : ℕ} (hp : p.Prime) (y k w t : ℕ)
    (T : Finset ℕ) (hT : T ⊆ (Finset.Ioc p w).filter Nat.Prime) :
    ((siftedSet y p k w).card : ℝ)
      ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
          + y * ∑ s ∈ T.powerset with 2 * t < s.card, ∏ q ∈ s, (k : ℝ) / q
          + (1 + T.card * k : ℝ) ^ (2 * t) := by
  rw [siftedSet_eq_siftedOver]
  refine (Nat.cast_le.mpr
    (Finset.card_le_card (siftedOver_subset hT))).trans ?_
  exact siftedOver_card_le_brun hp y k t T
    (fun q hq => (Finset.mem_filter.mp (hT hq)).2)
    (fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hT hq)).1).1)

/-- Exponential-tail variant of `siftedSet_card_le_brun_subset`. -/
theorem siftedSet_card_le_brun_subset_exp {p : ℕ} (hp : p.Prime)
    (y k w t : ℕ) (T : Finset ℕ)
    (hT : T ⊆ (Finset.Ioc p w).filter Nat.Prime) {z : ℝ} (hz : 1 ≤ z) :
    ((siftedSet y p k w).card : ℝ)
      ≤ y * ∏ q ∈ T, (1 - ((min k q : ℕ) : ℝ) / q)
          + y * Real.exp (z * k * ∑ q ∈ T, (q : ℝ)⁻¹) / z ^ (2 * t)
          + (1 + T.card * k : ℝ) ^ (2 * t) := by
  rw [siftedSet_eq_siftedOver]
  refine (Nat.cast_le.mpr
    (Finset.card_le_card (siftedOver_subset hT))).trans ?_
  exact siftedOver_card_le_brun_exp hp y k t T
    (fun q hq => (Finset.mem_filter.mp (hT hq)).2)
    (fun q hq => (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hT hq)).1).1) hz

end JSP314
