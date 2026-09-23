import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# The Pólya–Vinogradov inequality for primitive Dirichlet characters

We prove the classical Pólya–Vinogradov bound for Dirichlet character sums:
for a *primitive* Dirichlet character `χ` modulo `q ≥ 2`,

    ‖∑ n ∈ Finset.range N, χ n‖ ≤ √q · (1 + log q) ≤ 4·√q·log q.

The proof is the standard one via Gauss sums:

* `gaussSum_mulShift_of_isPrimitive` gives the Fourier expansion
  `χ(n)·τ(χ̄) = ∑_a χ̄(a)·e(na)` for the standard additive character `e`.
* `norm_gaussSum_eq_sqrt`: Parseval gives `‖τ(χ)‖ = √q` for primitive `χ`
  (this works for composite `q` too, via `AddChar.sum_mulShift`).
* `norm_sum_stdAddChar_le`: the inner geometric sum `∑_{n<N} e(na)` is bounded
  by `q / (2·min(a.val, (−a).val))`, using `‖1 − e^{iθ}‖ = 2·sin(θ/2)` and
  Jordan's inequality `Real.mul_le_sin`.
* `sum_geom_bound`: summing over `a` gives `q·(1 + log q)` via
  `harmonic_le_one_add_log`.

Only the primitive case is treated here; the general (imprimitive) case follows
by factoring through the conductor, at the cost of an extra `d(q)` factor.
-/

namespace JSP314

open Finset

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The exponential `ζ_q = e^{2πi/q}`, a primitive `q`-th root of unity. -/
noncomputable def zetaQ (q : ℕ) [NeZero q] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / q)

lemma zetaQ_isPrimitiveRoot : IsPrimitiveRoot (zetaQ q) q :=
  Complex.isPrimitiveRoot_exp q (NeZero.ne q)

lemma zetaQ_pow : zetaQ q ^ q = 1 := zetaQ_isPrimitiveRoot.pow_eq_one

/-- The standard additive character `ZMod q → ℂ` sending `a` to `ζ_q^{a.val}`. -/
noncomputable def stdAddChar (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ :=
  AddChar.zmodChar q zetaQ_pow

lemma stdAddChar_isPrimitive : (stdAddChar q).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root q zetaQ_isPrimitiveRoot

lemma stdAddChar_apply (a : ZMod q) : stdAddChar q a = zetaQ q ^ a.val :=
  AddChar.zmodChar_apply _ a

lemma stdAddChar_apply_nat (m : ℕ) : stdAddChar q (m : ZMod q) = zetaQ q ^ m :=
  AddChar.zmodChar_apply' _ m

lemma stdAddChar_star (x : ZMod q) : star (stdAddChar q x) = stdAddChar q (-x) := by
  have hrc : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q
  rw [← starRingEnd_apply, AddChar.starComp_apply hrc, AddChar.inv_apply]

/-- For any Dirichlet character `χ` mod `q`, `∑ a, χ a * star (χ a) = φ(q)`. -/
lemma sum_mul_star_eq_totient (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, χ a * star (χ a)) = (q.totient : ℂ) := by
  classical
  have h1 : ∀ a : ZMod q, χ a * star (χ a) = (1 : MulChar (ZMod q) ℂ) a := by
    intro a
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  rw [Finset.sum_congr rfl fun a _ => h1 a, MulChar.sum_one_eq_card_units,
    ZMod.card_units_eq_totient]

/-- Parseval for the Gauss sum: for primitive `χ`, `‖τ(χ)‖ = √q`. -/
theorem norm_gaussSum_eq_sqrt (χ : DirichletCharacter ℂ q)
    (hχ : DirichletCharacter.IsPrimitive χ) :
    ‖gaussSum χ (stdAddChar q)‖ = Real.sqrt q := by
  classical
  set e := stdAddChar q
  have he : e.IsPrimitive := stdAddChar_isPrimitive
  have hrc : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q
  have star_e : ∀ x : ZMod q, star (e x) = e (-x) := fun x => stdAddChar_star x
  have key : ∀ t : ZMod q, gaussSum χ (e.mulShift t) = χ⁻¹ t * gaussSum χ e :=
    fun t => gaussSum_mulShift_of_isPrimitive e hχ t
  have S1 : (∑ t : ZMod q, gaussSum χ (e.mulShift t) * star (gaussSum χ (e.mulShift t)))
      = (q.totient : ℂ) * (gaussSum χ e * star (gaussSum χ e)) := by
    have step : ∀ t : ZMod q,
        gaussSum χ (e.mulShift t) * star (gaussSum χ (e.mulShift t))
          = (χ⁻¹ t * star (χ⁻¹ t)) * (gaussSum χ e * star (gaussSum χ e)) := by
      intro t
      rw [key t, star_mul]
      ring
    rw [Finset.sum_congr rfl (fun t _ => step t), ← Finset.sum_mul,
      sum_mul_star_eq_totient]
  have S2 : (∑ t : ZMod q, gaussSum χ (e.mulShift t) * star (gaussSum χ (e.mulShift t)))
      = (q.totient : ℂ) * q := by
    have hexp : ∀ t : ZMod q,
        gaussSum χ (e.mulShift t) * star (gaussSum χ (e.mulShift t))
          = ∑ a : ZMod q, ∑ b : ZMod q, χ a * star (χ b) * e (t * (a - b)) := by
      intro t
      unfold gaussSum
      simp only [AddChar.mulShift_apply]
      rw [star_sum]
      simp_rw [star_mul, star_e]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have hE : e (t * a) * e (-(t * b)) = e (t * (a - b)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      rw [← hE]
      ring
    calc _ = ∑ t : ZMod q, ∑ a : ZMod q, ∑ b : ZMod q,
            χ a * star (χ b) * e (t * (a - b)) :=
          Finset.sum_congr rfl fun t _ => hexp t
      _ = ∑ a : ZMod q, ∑ t : ZMod q, ∑ b : ZMod q,
            χ a * star (χ b) * e (t * (a - b)) := Finset.sum_comm
      _ = ∑ a : ZMod q, ∑ b : ZMod q, ∑ t : ZMod q,
            χ a * star (χ b) * e (t * (a - b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a : ZMod q, ∑ b : ZMod q,
            χ a * star (χ b) * ∑ t : ZMod q, e (t * (a - b)) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.mul_sum]
      _ = ∑ a : ZMod q, ∑ b : ZMod q,
            χ a * star (χ b) * (if a - b = 0 then (q : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [AddChar.sum_mulShift _ he, ZMod.card, Nat.cast_ite, Nat.cast_zero]
      _ = ∑ a : ZMod q, χ a * star (χ a) * q := by
          refine Finset.sum_congr rfl fun a _ => ?_
          have hb : ∀ b : ZMod q,
              χ a * star (χ b) * (if a - b = 0 then (q : ℂ) else 0)
                = if b = a then χ a * star (χ a) * q else 0 := by
            intro b
            by_cases hab : a = b
            · subst hab
              rw [sub_self, ite_eq_left rfl, ite_eq_left rfl]
            · have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
              have h2 : b ≠ a := fun h => hab h.symm
              simp [h1, h2]
          rw [Finset.sum_congr rfl (fun b _ => hb b), Finset.sum_ite_eq']
          simp
      _ = (q.totient : ℂ) * q := by
          rw [← Finset.sum_mul, sum_mul_star_eq_totient]
  have hφ : (q.totient : ℂ) ≠ 0 := by
    norm_cast
    exact (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hmain : gaussSum χ e * star (gaussSum χ e) = (q : ℂ) :=
    mul_left_cancel₀ hφ (S1.symm.trans S2)
  have hnorm2 : ‖gaussSum χ e‖ ^ 2 = (q : ℝ) := by
    have h := congr_arg Complex.re hmain
    -- `h : (τ * star τ).re = (↑q : ℂ).re`
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
      Complex.natCast_re] at h
    -- `h : normSq τ = (q : ℝ)`
    rwa [Complex.normSq_eq_norm_sq] at h
  rw [← hnorm2]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- Geometric-series bound: for `a ≠ 0` in `ZMod q`,
`‖∑_{n<N} e(n·a)‖ ≤ q / (2·min(a.val, (−a).val))`. -/
lemma norm_sum_stdAddChar_le (a : ZMod q) (ha : a ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, stdAddChar q (↑n * a)‖
      ≤ (q : ℝ) / (2 * (min a.val (-a).val : ℕ)) := by
  classical
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hζpow : zetaQ q ^ q = 1 := zetaQ_pow
  have hζprim : IsPrimitiveRoot (zetaQ q) q := zetaQ_isPrimitiveRoot
  -- Each summand is a power of `u := ζ^{a.val}`.
  have hterm : ∀ n : ℕ, stdAddChar q (↑n * a) = (zetaQ q ^ a.val) ^ n := by
    intro n
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Nat.cast_mul]
    rw [stdAddChar_apply_nat, mul_comm n a.val, pow_mul]
  -- `u ≠ 1` since `0 < a.val < q` and `ζ` is a primitive `q`-th root.
  have hu_ne : zetaQ q ^ a.val ≠ 1 := by
    intro hu
    rw [hζprim.pow_eq_one_iff_dvd a.val] at hu
    exact absurd (Nat.le_of_dvd (ZMod.val_pos.mpr ha) hu) (not_le.mpr a.val_lt)
  have hu1 : ‖zetaQ q ^ a.val‖ = 1 := by
    have h : ‖zetaQ q ^ a.val‖ ^ q = 1 := by
      rw [← norm_pow, ← pow_mul, mul_comm a.val q, pow_mul, hζpow, one_pow,
        norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.pos q).ne').mp h
  -- Rewrite `ζ^{a.val}` as `exp(θi)` with `θ = 2π·a.val/q`.
  have hζdef : zetaQ q = Complex.exp (2 * Real.pi * Complex.I / q) := rfl
  have hζa : zetaQ q ^ a.val
      = Complex.exp ((2 * Real.pi * a.val / q : ℝ) * Complex.I) := by
    rw [hζdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- `e^{iθ} − 1 = e^{iθ/2}·(e^{iθ/2} − e^{−iθ/2}) = e^{iθ/2}·2i·sin(θ/2)`.
  have hfac : Complex.exp ((2 * Real.pi * a.val / q : ℝ) * Complex.I) - 1
      = Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
        * (2 * Complex.I * (Real.sin (Real.pi * a.val / q) : ℂ)) := by
    have h1 : Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
          * Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
        = Complex.exp ((2 * Real.pi * a.val / q : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h2 : Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
          - Complex.exp ((-Real.pi * a.val / q : ℝ) * Complex.I)
        = 2 * Complex.I * (Real.sin (Real.pi * a.val / q) : ℂ) := by
      rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, neg_mul, neg_div,
        Real.sin_neg, Real.cos_neg]
      push_cast
      ring
    have h3 : Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
        * Complex.exp ((-Real.pi * a.val / q : ℝ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      have : ((Real.pi * a.val / q : ℝ) : ℂ) * Complex.I
          + ((-Real.pi * a.val / q : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast
        ring
      rw [this, Complex.exp_zero]
    calc Complex.exp ((2 * Real.pi * a.val / q : ℝ) * Complex.I) - 1
        = Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
            * Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
          - Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
            * Complex.exp ((-Real.pi * a.val / q : ℝ) * Complex.I) := by
            rw [h1, h3]
      _ = Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
            * (Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
              - Complex.exp ((-Real.pi * a.val / q : ℝ) * Complex.I)) := by
            rw [mul_sub]
      _ = Complex.exp ((Real.pi * a.val / q : ℝ) * Complex.I)
            * (2 * Complex.I * (Real.sin (Real.pi * a.val / q) : ℂ)) := by
            rw [h2]
  -- Hence `‖u − 1‖ = 2·sin(π·a.val/q) ≥ 4·min(a.val, (−a).val)/q`.
  have hsin_pos : 0 < Real.sin (Real.pi * a.val / q) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hv : (0 : ℝ) < a.val := by exact_mod_cast ZMod.val_pos.mpr ha
      exact div_pos (mul_pos Real.pi_pos hv) hqR
    · -- π·a.val/q < π since a.val < q
      rw [div_lt_iff₀ hqR]
      have : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
      nlinarith [Real.pi_pos]
  have hnorm : ‖zetaQ q ^ a.val - 1‖ = 2 * Real.sin (Real.pi * a.val / q) := by
    rw [hζa, hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
      norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsin_pos.le]
  -- Jordan's inequality: `sin(π·m/q) ≥ 2m/q` for `m ≤ q/2`.
  have jordan : ∀ m : ℕ, m ≤ q / 2 →
      2 * (m : ℝ) / q ≤ Real.sin (Real.pi * m / q) := by
    intro m hm
    have hx0 : (0 : ℝ) ≤ Real.pi * m / q := by positivity
    have hx1 : Real.pi * m / q ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hqR, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 2),
        mul_assoc]
      apply mul_le_mul_of_nonneg_left _ Real.pi_nonneg
      exact_mod_cast (by omega : m * 2 ≤ q)
    have h := Real.mul_le_sin hx0 hx1
    have hcancel : (2 : ℝ) / Real.pi * (Real.pi * m / q) = 2 * m / q := by
      field_simp [Real.pi_ne_zero, hq0]
    rwa [hcancel] at h
  have hden : 4 * ((min a.val (-a).val : ℕ) : ℝ) / q
      ≤ ‖zetaQ q ^ a.val - 1‖ := by
    rw [hnorm]
    rcases lt_or_ge (q / 2 : ℕ) a.val with h1 | h1
    · -- `q / 2 < a.val`: the minimum is `(−a).val = q − a.val`.
      have hmin : min a.val (-a).val = q - a.val := by
        rw [ZMod.neg_val, ite_eq_right ha]
        exact min_eq_right (by omega)
      rw [hmin]
      have hmq : q - a.val ≤ q / 2 := by omega
      have h := jordan (q - a.val) hmq
      have hsin : Real.sin (Real.pi * a.val / q)
          = Real.sin (Real.pi * ((q - a.val : ℕ) : ℝ) / q) := by
        have hval : a.val ≤ q := Nat.le_of_lt a.val_lt
        have heq : Real.pi * a.val / q
            = Real.pi - Real.pi * ((q - a.val : ℕ) : ℝ) / q := by
          rw [Nat.cast_sub hval, eq_sub_iff_add_eq, ← add_div,
            div_eq_iff hq0]
          ring
        rw [heq, Real.sin_pi_sub]
      rw [hsin]
      calc 4 * ((q - a.val : ℕ) : ℝ) / q
            = 2 * (2 * ((q - a.val : ℕ) : ℝ) / q) := by ring
        _ ≤ 2 * Real.sin _ := mul_le_mul_of_nonneg_left h (by norm_num)
    · -- `a.val ≤ q / 2`: the minimum is `a.val`.
      have hmin : min a.val (-a).val = a.val := by
        rw [ZMod.neg_val, ite_eq_right ha]
        exact min_eq_left (by omega)
      rw [hmin]
      have h := jordan a.val h1
      calc 4 * (a.val : ℝ) / q = 2 * (2 * a.val / q) := by ring
        _ ≤ 2 * Real.sin _ := mul_le_mul_of_nonneg_left h (by norm_num)
  -- Assemble: `‖∑‖ = ‖(u^N − 1)/(u − 1)‖ ≤ 2/‖u−1‖ ≤ q/(2m)`.
  have hsum : ∑ n ∈ Finset.range N, stdAddChar q (↑n * a)
      = ∑ n ∈ Finset.range N, (zetaQ q ^ a.val) ^ n :=
    Finset.sum_congr rfl fun n _ => hterm n
  have hpos : (0 : ℝ) < 2 * ((min a.val (-a).val : ℕ) : ℝ) := by
    have hvp : 0 < a.val := ZMod.val_pos.mpr ha
    have hlt : a.val < q := a.val_lt
    have hm : 0 < min a.val (-a).val := by
      rw [ZMod.neg_val, ite_eq_right ha]
      omega
    have h0 : (0 : ℝ) < ((min a.val (-a).val : ℕ) : ℝ) := by
      exact_mod_cast hm
    exact mul_pos (by norm_num) h0
  have hnorm_pos : (0 : ℝ) < ‖zetaQ q ^ a.val - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hu_ne)
  calc ‖∑ n ∈ Finset.range N, stdAddChar q (↑n * a)‖
      = ‖∑ n ∈ Finset.range N, (zetaQ q ^ a.val) ^ n‖ := by rw [hsum]
    _ = ‖((zetaQ q ^ a.val) ^ N - 1) / (zetaQ q ^ a.val - 1)‖ := by
        rw [geom_sum_eq hu_ne]
    _ = ‖(zetaQ q ^ a.val) ^ N - 1‖ / ‖zetaQ q ^ a.val - 1‖ := norm_div _ _
    _ ≤ 2 / ‖zetaQ q ^ a.val - 1‖ := by
        apply (div_le_div_iff_of_pos_right hnorm_pos).mpr
        calc ‖(zetaQ q ^ a.val) ^ N - 1‖ ≤ ‖(zetaQ q ^ a.val) ^ N‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
          _ = ‖zetaQ q ^ a.val‖ ^ N + 1 := by rw [norm_pow]; norm_num
          _ = 2 := by rw [hu1]; norm_num
    _ ≤ (q : ℝ) / (2 * (min a.val (-a).val : ℕ)) := by
        rw [div_le_div_iff₀ hnorm_pos hpos]
        -- goal: `2 * (2·m) ≤ q * ‖u − 1‖`; `hden` gives `4m/q ≤ ‖u−1‖`.
        have h' := (div_le_iff₀ hqR).mp hden
        nlinarith [h']

/-- The key summation estimate:
`∑_{a≠0} q/(2·min(a.val,(−a).val)) ≤ q·(1 + log q)`. -/
lemma sum_geom_bound (hq : 2 ≤ q) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q),
      (q : ℝ) / (2 * (min a.val (-a).val : ℕ)))
      ≤ q * (1 + Real.log q) := by
  classical
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega : 0 < q)
  -- split `a ≠ 0` into `a.val ≤ q/2` and `a.val > q/2`
  set S1 := (Finset.univ.erase (0 : ZMod q)).filter (fun a => a.val ≤ q / 2)
    with hS1d
  set S2 := (Finset.univ.erase (0 : ZMod q)).filter (fun a => q / 2 < a.val)
    with hS2d
  set T := Finset.univ.filter (fun b : ZMod q => 1 ≤ b.val ∧ b.val ≤ q / 2)
    with hTd
  have hunion : Finset.univ.erase (0 : ZMod q) = S1 ∪ S2 := by
    ext a
    simp only [hS1d, hS2d, Finset.mem_union, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_univ, and_true]
    constructor
    · intro ha
      rcases lt_or_ge (q / 2 : ℕ) a.val with h | h
      · exact Or.inr ⟨ha, h⟩
      · exact Or.inl ⟨ha, h⟩
    · rintro (⟨ha, -⟩ | ⟨ha, -⟩) <;> exact ha
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [hS1d, hS2d, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true] at ha1 ha2
    omega
  -- on S1, `min a.val (−a).val = a.val`
  have hS1 : ∀ a ∈ S1, min a.val (-a).val = a.val := by
    intro a ha
    simp only [hS1d, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true] at ha
    rw [ZMod.neg_val, ite_eq_right ha.1]
    exact min_eq_left (by omega)
  -- on S2, `min a.val (−a).val = (−a).val`
  have hS2 : ∀ a ∈ S2, min a.val (-a).val = (-a).val := by
    intro a ha
    simp only [hS2d, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true] at ha
    rw [ZMod.neg_val, ite_eq_right ha.1]
    exact min_eq_right (by omega)
  -- `neg '' S2 ⊆ T`
  have hneg : S2.image Neg.neg ⊆ T := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simp only [hS2d, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true] at ha
    have hval : (-a).val = q - a.val := by rw [ZMod.neg_val, ite_eq_right ha.1]
    simp only [hTd, Finset.mem_filter, Finset.mem_univ, true_and]
    have hlt := a.val_lt
    omega
  -- summing over `S2` via the image under `Neg.neg`
  have hsum2 : (∑ b ∈ S2.image Neg.neg, (q : ℝ) / (2 * (b.val : ℝ)))
      = ∑ a ∈ S2, (q : ℝ) / (2 * ((-a).val : ℝ)) :=
    Finset.sum_image (f := fun b : ZMod q => (q : ℝ) / (2 * (b.val : ℝ)))
      (fun x _ y _ h => neg_injective h)
  -- `S1 ⊆ T`
  have hS1T : S1 ⊆ T := by
    intro a ha
    simp only [hS1d, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true] at ha
    simp only [hTd, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ZMod.val_pos.mpr ha.1, ha.2⟩
  -- the sum over T in terms of the values
  have hT : ∑ b ∈ T, (q : ℝ) / (2 * (b.val : ℝ))
      = ∑ j ∈ T.image ZMod.val, (q : ℝ) / (2 * (j : ℝ)) := by
    rw [Finset.sum_image (fun x _ y _ h => ZMod.val_injective q h)]
  have hTsub : T.image ZMod.val ⊆ Finset.Icc 1 (q / 2) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨b, hb, rfl⟩ := hj
    simp only [hTd, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact Finset.mem_Icc.mpr hb
  have hnn : ∀ j : ℕ, 0 ≤ (q : ℝ) / (2 * (j : ℝ)) := fun j => by positivity
  -- harmonic bound
  have hharm : ((harmonic (q / 2) : ℚ) : ℝ)
      = ∑ j ∈ Finset.Icc 1 (q / 2), (j : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have hIcc : ∑ j ∈ Finset.Icc 1 (q / 2), (q : ℝ) / (2 * (j : ℝ))
      = (q / 2) * (harmonic (q / 2) : ℝ) := by
    rw [hharm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_eq_mul_inv, mul_inv]
    ring
  -- assemble
  calc (∑ a ∈ Finset.univ.erase (0 : ZMod q), (q : ℝ) / (2 * (min a.val (-a).val : ℕ)))
      = ∑ a ∈ S1, (q : ℝ) / (2 * (a.val : ℝ))
          + ∑ a ∈ S2, (q : ℝ) / (2 * ((-a).val : ℝ)) := by
        rw [hunion, Finset.sum_union hdisj]
        congr 1
        · apply Finset.sum_congr rfl
          intro a ha
          rw [hS1 a ha]
        · apply Finset.sum_congr rfl
          intro a ha
          rw [hS2 a ha]
    _ = ∑ a ∈ S1, (q : ℝ) / (2 * (a.val : ℝ))
          + ∑ b ∈ S2.image Neg.neg, (q : ℝ) / (2 * (b.val : ℝ)) := by
        rw [hsum2]
    _ ≤ ∑ b ∈ T, (q : ℝ) / (2 * (b.val : ℝ))
          + ∑ b ∈ T, (q : ℝ) / (2 * (b.val : ℝ)) := by
        apply add_le_add
        · exact Finset.sum_le_sum_of_subset_of_nonneg hS1T
            (fun b hb _ => hnn b.val)
        · exact Finset.sum_le_sum_of_subset_of_nonneg hneg
            (fun b hb _ => hnn b.val)
    _ = 2 * ∑ b ∈ T, (q : ℝ) / (2 * (b.val : ℝ)) := by ring
    _ = 2 * ∑ j ∈ T.image ZMod.val, (q : ℝ) / (2 * (j : ℝ)) := by rw [hT]
    _ ≤ 2 * ∑ j ∈ Finset.Icc 1 (q / 2), (q : ℝ) / (2 * (j : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        exact Finset.sum_le_sum_of_subset_of_nonneg hTsub (fun j hj _ => hnn j)
    _ = 2 * ((q / 2) * (harmonic (q / 2) : ℝ)) := by rw [hIcc]
    _ = q * (harmonic (q / 2) : ℝ) := by ring
    _ ≤ q * (1 + Real.log ((q / 2 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hqR)
        exact harmonic_le_one_add_log (q / 2)
    _ ≤ q * (1 + Real.log q) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hqR)
        have hpos' : (0 : ℝ) < ((q / 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
        have hle : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) := by
          exact_mod_cast Nat.div_le_self q 2
        have := Real.log_le_log hpos' hle
        linarith

/-- **Pólya–Vinogradov** for a primitive Dirichlet character `χ` mod `q ≥ 2`:
`‖∑_{n<N} χ(n)‖ ≤ √q·(1 + log q)`. -/
theorem polya_vinogradov (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : DirichletCharacter.IsPrimitive χ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ (↑n : ZMod q)‖
      ≤ Real.sqrt q * (1 + Real.log q) := by
  classical
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega : 0 < q)
  have hχi : DirichletCharacter.IsPrimitive χ⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  set e := stdAddChar q
  have hτ : ‖gaussSum χ⁻¹ e‖ = Real.sqrt q := norm_gaussSum_eq_sqrt χ⁻¹ hχi
  have hτ0 : gaussSum χ⁻¹ e ≠ 0 := by
    rw [← norm_pos_iff, hτ]
    exact Real.sqrt_pos.mpr hqR
  -- Fourier expansion of `χ` in terms of `χ⁻¹`.
  have key : ∀ t : ZMod q, gaussSum χ⁻¹ (e.mulShift t) = χ t * gaussSum χ⁻¹ e := by
    intro t
    rw [gaussSum_mulShift_of_isPrimitive e hχi t, inv_inv]
  have hfour : ∀ n : ℕ, χ (↑n : ZMod q)
      = (gaussSum χ⁻¹ e)⁻¹ * ∑ a : ZMod q, χ⁻¹ a * e (↑n * a) := by
    intro n
    have h := key (↑n : ZMod q)
    -- `h : gaussSum χ⁻¹ (e.mulShift ↑n) = χ ↑n * τ`
    have hS : (∑ a : ZMod q, χ⁻¹ a * e (↑n * a))
        = χ (↑n : ZMod q) * gaussSum χ⁻¹ e := by
      rw [← h]
      unfold gaussSum
      simp only [AddChar.mulShift_apply]
    have h' : (gaussSum χ⁻¹ e)⁻¹ * (∑ a : ZMod q, χ⁻¹ a * e (↑n * a))
        = χ (↑n : ZMod q) := by
      rw [hS, mul_comm (χ (↑n : ZMod q)) (gaussSum χ⁻¹ e), ← mul_assoc,
        inv_mul_cancel₀ hτ0, one_mul]
    exact h'.symm
  calc ‖∑ n ∈ Finset.range N, χ (↑n : ZMod q)‖
      = ‖(gaussSum χ⁻¹ e)⁻¹
          * ∑ a : ZMod q, χ⁻¹ a * ∑ n ∈ Finset.range N, e (↑n * a)‖ := by
        congr 1
        rw [Finset.sum_congr rfl (fun n _ => hfour n)]
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum]
    _ = ‖gaussSum χ⁻¹ e‖⁻¹
          * ‖∑ a : ZMod q, χ⁻¹ a * ∑ n ∈ Finset.range N, e (↑n * a)‖ := by
        rw [norm_mul, norm_inv]
    _ ≤ ‖gaussSum χ⁻¹ e‖⁻¹
          * ∑ a : ZMod q, ‖χ⁻¹ a‖ * ‖∑ n ∈ Finset.range N, e (↑n * a)‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ‖∑ a : ZMod q, χ⁻¹ a * ∑ n ∈ Finset.range N, e (↑n * a)‖
            ≤ ∑ a : ZMod q, ‖χ⁻¹ a * ∑ n ∈ Finset.range N, e (↑n * a)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ a : ZMod q, ‖χ⁻¹ a‖ * ‖∑ n ∈ Finset.range N, e (↑n * a)‖ :=
              Finset.sum_le_sum fun a _ => le_of_eq (norm_mul _ _)
    _ = ‖gaussSum χ⁻¹ e‖⁻¹
          * ∑ a ∈ Finset.univ.erase (0 : ZMod q),
            ‖χ⁻¹ a‖ * ‖∑ n ∈ Finset.range N, e (↑n * a)‖ := by
        congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
        have h0 : χ⁻¹ (0 : ZMod q) = 0 :=
          DirichletCharacter.map_zero' χ⁻¹ (show q ≠ 1 by omega)
        rw [h0]
        simp
    _ ≤ ‖gaussSum χ⁻¹ e‖⁻¹
          * ∑ a ∈ Finset.univ.erase (0 : ZMod q),
            (q : ℝ) / (2 * (min a.val (-a).val : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro a ha
        have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
        have h1 : ‖χ⁻¹ a‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have h2 := norm_sum_stdAddChar_le a hane N
        calc ‖χ⁻¹ a‖ * ‖∑ n ∈ Finset.range N, e (↑n * a)‖
            ≤ 1 * ((q : ℝ) / (2 * (min a.val (-a).val : ℕ))) :=
              mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          _ = (q : ℝ) / (2 * (min a.val (-a).val : ℕ)) := one_mul _
    _ ≤ ‖gaussSum χ⁻¹ e‖⁻¹ * (q * (1 + Real.log q)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_geom_bound hq
    _ = Real.sqrt q * (1 + Real.log q) := by
        rw [hτ]
        have hqq : (Real.sqrt q)⁻¹ * (q : ℝ) = Real.sqrt q := by
          rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]
        rw [← mul_assoc, hqq]

/-- The Pólya–Vinogradov inequality with a single explicit constant:
for primitive `χ` mod `q ≥ 2`, `‖∑_{n<N} χ(n)‖ ≤ 4·√q·log q`. -/
theorem polya_vinogradov' (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : DirichletCharacter.IsPrimitive χ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ (↑n : ZMod q)‖
      ≤ 4 * Real.sqrt q * Real.log q := by
  have h := polya_vinogradov hq χ hχ N
  have hlog2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log 2 ≤ Real.log q := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    exact_mod_cast hq
  have hlogq : (0 : ℝ) < Real.log q := by
    linarith [Real.log_two_gt_d9]
  calc ‖∑ n ∈ Finset.range N, χ (↑n : ZMod q)‖
      ≤ Real.sqrt q * (1 + Real.log q) := h
    _ ≤ Real.sqrt q * (4 * Real.log q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        nlinarith [hlog2, hlog]
    _ = 4 * Real.sqrt q * Real.log q := by ring

end

end JSP314
