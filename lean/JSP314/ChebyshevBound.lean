import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Factorization

/-!
# An elementary Chebyshev-type upper bound below `log 4`

We prove `Chebyshev.theta n ≤ c · n` eventually for `c = 5 / 4 < 127 / 100`,
improving on the classical `θ n ≤ (log 4) · n` that comes from
`Nat.primorial_le_four_pow`.

The argument is Chebyshev's method with the `(2, 3, 6)` combination of
factorials: `C(n) := n! / ((n/2)! · (n/3)! · (n/6)!)` is a positive integer
divisible by every prime in `(n/6, n]`, hence
`θ n − θ (n/6) ≤ log (C n)`.  The elementary bounds
`k·log k − k ≤ log k! ≤ k·log k − k + log k + 1` yield
`log (C n) ≤ c₀·n + 6·log n + 7` with `c₀ = (2/3)·log 2 + (1/2)·log 3`,
and iterating along `n ↦ n/6` gives `θ n ≤ (6/5)·c₀·n + O((log n)²)`.
-/

open Nat Finset Real
open scoped Chebyshev

namespace JSP314

/-- The Chebyshev-type integer `n! / ((n/2)!·(n/3)!·(n/6)!)`. -/
def chebC (n : ℕ) : ℕ := n ! / ((n / 2)! * (n / 3)! * (n / 6)!)

lemma cheb_div_div_pow_comm (n d p i : ℕ) : (n / d) / p ^ i = (n / p ^ i) / d := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm d]

lemma cheb_floor_le (u : ℕ) : u / 2 + u / 3 + u / 6 ≤ u := by omega

lemma cheb_floor_ge {u : ℕ} (h1 : 1 ≤ u) (h2 : u < 6) :
    1 ≤ u - u / 2 - u / 3 - u / 6 := by
  interval_cases u <;> decide

lemma chebC_aux_dvd (n : ℕ) : (n / 2)! * (n / 3)! * (n / 6)! ∣ n ! := by
  have hfa : ∀ m : ℕ, (m !) ≠ 0 := fun m ↦ Nat.factorial_ne_zero m
  rw [← Nat.factorization_le_iff_dvd (by positivity) (hfa n), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hlog : ∀ m : ℕ, m ≤ n → Nat.log p m < n + 1 := by
      intro m hm; have h := Nat.log_le_self p m; omega
    rw [Nat.factorization_mul (by positivity) (hfa _), Finsupp.add_apply,
      Nat.factorization_mul (hfa _) (hfa _), Finsupp.add_apply,
      Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
      Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
      Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
      Nat.factorization_factorial hp (hlog _ le_rfl),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [cheb_div_div_pow_comm, cheb_div_div_pow_comm, cheb_div_div_pow_comm]
    exact cheb_floor_le _
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]



lemma log_factorial_eq (k : ℕ) :
    Real.log (k !) = (k : ℝ) * Real.log k - k +
      ∑ j ∈ Finset.range k,
        (Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1)) := by
  have hfac : ((k ! : ℕ) : ℝ) = ∏ j ∈ Finset.range k, (j + 1 : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    norm_cast
  have h1 : Real.log (k !) = ∑ j ∈ Finset.range k, Real.log (j + 1 : ℝ) := by
    rw [hfac, Real.log_prod (fun j _ ↦ by positivity)]
  have h2 : ∑ j ∈ Finset.range k,
        (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j) =
      (k : ℝ) * Real.log k := by
    simpa using Finset.sum_range_sub (fun j : ℕ ↦ (j : ℝ) * Real.log j) k
  have h3 : ∑ j ∈ Finset.range k,
        (Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1)) =
      ∑ j ∈ Finset.range k, Real.log (j + 1 : ℝ) -
        ∑ j ∈ Finset.range k,
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j) +
        (k : ℝ) := by
    have e : ∀ j : ℕ, Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1) =
        (Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j)) + 1 :=
      fun j ↦ by ring
    rw [Finset.sum_congr rfl fun j _ ↦ e j, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    simp
  rw [h3, h1, h2]
  ring

lemma cheb_delta_bounds {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1) ∧
    Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1) ≤
      1 / (j + 1 : ℝ) := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hj
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (0 : ℝ) < j + 1 := by linarith
  set d := Real.log (j + 1 : ℝ) - Real.log (j : ℝ) with hd
  have hdeq : Real.log (j + 1 : ℝ) -
      (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1) =
      1 - j * d := by
    rw [hd]
    push_cast
    ring
  have hd_log : d = Real.log ((j + 1 : ℝ) / j) := by
    rw [hd, Real.log_div (by positivity) hj0]
  have hd_le : d ≤ 1 / j := by
    rw [hd_log]
    calc Real.log ((j + 1 : ℝ) / j) ≤ (j + 1 : ℝ) / j - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
    _ = 1 / j := by field
  have hd_ge : 1 / (j + 1 : ℝ) ≤ d := by
    rw [hd_log]
    have h : Real.log ((j : ℝ) / (j + 1 : ℝ)) ≤ (j : ℝ) / (j + 1 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : (j : ℝ) / (j + 1 : ℝ) - 1 = -(1 / (j + 1 : ℝ)) := by field
    have h3 : Real.log ((j + 1 : ℝ) / j) = -Real.log ((j : ℝ) / (j + 1 : ℝ)) := by
      rw [← Real.log_inv, inv_div]
    rw [h2] at h
    rw [h3]
    linarith
  rw [hdeq]
  constructor
  · have : j * d ≤ j * (1 / j) := by
      apply mul_le_mul_of_nonneg_left hd_le hjp.le
    rw [mul_one_div_cancel hj0] at this
    linarith
  · have hjd : (j : ℝ) * (1 / (j + 1 : ℝ)) ≤ j * d :=
      mul_le_mul_of_nonneg_left hd_ge hjp.le
    have he : 1 - (j : ℝ) * (1 / (j + 1 : ℝ)) = 1 / (j + 1 : ℝ) := by field
    linarith

lemma sum_inv_le_log (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 : ℝ) / (j + 1 : ℝ) ≤ 1 + Real.log k := by
  have hterm : ∀ j : ℕ, (1 : ℝ) / (j + 1 : ℝ) ≤
      (if j = 0 then 1 else 0) +
        (Real.log (j + 1 : ℝ) - Real.log (j : ℝ)) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
      have h1 : Real.log ((j : ℝ) / (j + 1 : ℝ)) ≤ (j : ℝ) / (j + 1 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : (j : ℝ) / (j + 1 : ℝ) - 1 = -(1 / (j + 1 : ℝ)) := by field
      rw [h2] at h1
      have h3 : Real.log (j + 1 : ℝ) - Real.log (j : ℝ) =
          -Real.log ((j : ℝ) / (j + 1 : ℝ)) := by
        rw [Real.log_div hjp.ne' (by positivity)]
        ring
      rw [if_neg hj, zero_add, h3]
      linarith
  calc ∑ j ∈ Finset.range k, (1 : ℝ) / (j + 1 : ℝ)
      ≤ ∑ j ∈ Finset.range k,
          ((if j = 0 then (1 : ℝ) else 0) +
            (Real.log (j + 1 : ℝ) - Real.log (j : ℝ))) :=
        Finset.sum_le_sum fun j _ ↦ hterm j
    _ = (∑ j ∈ Finset.range k, (if j = 0 then (1 : ℝ) else 0)) +
          ∑ j ∈ Finset.range k, (Real.log (j + 1 : ℝ) - Real.log (j : ℝ)) :=
        Finset.sum_add_distrib
    _ ≤ 1 + Real.log k := by
        have htele : ∑ j ∈ Finset.range k,
            (Real.log (j + 1 : ℝ) - Real.log (j : ℝ)) = Real.log k := by
          have h := Finset.sum_range_sub (fun j : ℕ ↦ Real.log (j : ℝ)) k
          simp only [Nat.cast_zero, Real.log_zero, sub_zero] at h
          rw [← h]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Nat.cast_add_one]
        rw [Finset.sum_ite_eq' _ _ (fun _ ↦ (1 : ℝ)), htele]
        split_ifs <;> simp

lemma log_factorial_lower (k : ℕ) :
    (k : ℝ) * Real.log k - k ≤ Real.log (k !) := by
  rw [log_factorial_eq]
  have : 0 ≤ ∑ j ∈ Finset.range k,
      (Real.log (j + 1 : ℝ) -
        (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1)) := by
    apply Finset.sum_nonneg
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · simp
    · exact (cheb_delta_bounds (Nat.pos_of_ne_zero hj0)).1
  linarith

lemma log_factorial_upper (k : ℕ) :
    Real.log (k !) ≤ (k : ℝ) * Real.log k - k + 1 + Real.log k := by
  rw [log_factorial_eq]
  have hδ : ∀ j : ℕ,
      Real.log (j + 1 : ℝ) -
          (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1) ≤
        (1 : ℝ) / (j + 1 : ℝ) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj0
    · simp
    · exact (cheb_delta_bounds (Nat.pos_of_ne_zero hj0)).2
  calc (k : ℝ) * Real.log k - k +
        ∑ j ∈ Finset.range k,
          (Real.log (j + 1 : ℝ) -
            (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) - (j : ℝ) * Real.log j - 1))
      ≤ (k : ℝ) * Real.log k - k +
          ∑ j ∈ Finset.range k, (1 : ℝ) / (j + 1 : ℝ) := by
        have hs : ∑ j ∈ Finset.range k,
            (Real.log (j + 1 : ℝ) -
              (((j + 1 : ℕ) : ℝ) * Real.log (j + 1 : ℕ) -
                (j : ℝ) * Real.log j - 1)) ≤
            ∑ j ∈ Finset.range k, (1 : ℝ) / (j + 1 : ℝ) :=
          Finset.sum_le_sum fun j _ ↦ hδ j
        linarith
    _ ≤ (k : ℝ) * Real.log k - k + (1 + Real.log k) := by
        gcongr
        exact sum_inv_le_log k
    _ = _ := by ring



lemma div_mul_log_le {n d : ℕ} (hd : 0 < d) (h : 2 * d ≤ n) :
    -((n / d : ℕ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) ≤
      -((n / d : ℕ) : ℝ) * (Real.log n - Real.log d) + 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hd0' : (0 : ℝ) < d := by positivity
  set a : ℝ := ((n / d : ℕ) : ℝ) with ha
  have hlt : (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * d := by
    have h := Nat.div_add_mod' n d
    have hm := Nat.mod_lt n hd
    have : n < (n / d) * d + d := by omega
    calc (n : ℝ) < ((n / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    _ = (((n / d : ℕ) : ℝ) + 1) * d := by ring
  have ha_gt : (n : ℝ) / d - 1 < a := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd0', ha]
    exact hlt
  have ha_pos : 0 < a := by
    have : (1 : ℝ) ≤ (n : ℝ) / d - 1 := by
      have hn : (2 * d : ℝ) ≤ n := by exact_mod_cast h
      have : (2 : ℝ) ≤ (n : ℝ) / d := by
        rw [le_div_iff₀ hd0']; linarith
      linarith
    linarith
  have ha_le : a ≤ (n : ℝ) / d := by
    rw [ha]; exact Nat.cast_div_le
  have h1 : Real.log ((n : ℝ) / d - 1) ≤ Real.log a :=
    Real.log_le_log (by
      have htwo : (2 : ℝ) ≤ (n : ℝ) / d := by
        rw [le_div_iff₀ hd0']; exact_mod_cast h
      linarith) ha_gt.le
  have h2 : Real.log ((n : ℝ) / d - 1) = Real.log ((n : ℝ) - d) - Real.log d := by
    have hnd : (n : ℝ) - d ≠ 0 := by
      have hn : (2 * d : ℝ) ≤ n := by exact_mod_cast h
      have : (0 : ℝ) < (n : ℝ) - d := by linarith
      exact this.ne'
    rw [show (n : ℝ) / d - 1 = ((n : ℝ) - d) / d by
        rw [sub_div, div_self hd0],
      Real.log_div hnd hd0]
  have h3 : Real.log ((n : ℝ) - d) ≥ Real.log n - 2 * (d : ℝ) / n := by
    have hn : (2 * d : ℝ) ≤ n := by exact_mod_cast h
    have hn0 : (0 : ℝ) < n := by linarith
    have hnd : (0 : ℝ) < (n : ℝ) - d := by linarith
    have hdn : (0 : ℝ) < 1 - (d : ℝ) / n := by
      rw [sub_pos, div_lt_iff₀ hn0]; linarith
    have e1 : Real.log ((n : ℝ) - d) =
        Real.log n + Real.log (1 - (d : ℝ) / n) := by
      rw [← Real.log_mul hn0.ne' hdn.ne']
      congr 1
      field
    have ht : (0 : ℝ) ≤ (d : ℝ) / n := by positivity
    have ht1 : (d : ℝ) / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hn0]; linarith
    have hlog : Real.log (1 - (d : ℝ) / n) ≥ -((d : ℝ) / n) / (1 - (d : ℝ) / n) := by
      have h4 : Real.log (1 / (1 - (d : ℝ) / n)) ≤ 1 / (1 - (d : ℝ) / n) - 1 :=
        Real.log_le_sub_one_of_pos (one_div_pos.mpr hdn)
      rw [Real.log_div one_ne_zero hdn.ne', Real.log_one, zero_sub] at h4
      have heq : ((d : ℝ) / n) / (1 - (d : ℝ) / n) =
          1 / (1 - (d : ℝ) / n) - 1 := by
        rw [div_eq_iff hdn.ne', sub_mul, div_mul_cancel₀ _ hdn.ne', one_mul,
          sub_sub_self]
      have hneg : -((d : ℝ) / n) / (1 - (d : ℝ) / n) =
          -(((d : ℝ) / n) / (1 - (d : ℝ) / n)) := neg_div _ _
      linarith
    have h5 : ((d : ℝ) / n) / (1 - (d : ℝ) / n) ≤ 2 * ((d : ℝ) / n) := by
      rw [div_le_iff₀ hdn]
      nlinarith [ht, ht1]
    rw [e1]
    have hneg : -((d : ℝ) / n) / (1 - (d : ℝ) / n) =
        -(((d : ℝ) / n) / (1 - (d : ℝ) / n)) := neg_div _ _
    have hdx : 2 * (d : ℝ) / n = 2 * ((d : ℝ) / n) := by ring
    linarith
  have hlog : Real.log a ≥ Real.log n - Real.log d - 2 * (d : ℝ) / n := by
    linarith [h1, h2, h3]
  have hprod : a * (2 * (d : ℝ) / n) ≤ 2 := by
    have hn0 : (0 : ℝ) < n := by
      have : (2 * d : ℝ) ≤ n := by exact_mod_cast h
      linarith
    calc a * (2 * (d : ℝ) / n) ≤ ((n : ℝ) / d) * (2 * (d : ℝ) / n) :=
          mul_le_mul_of_nonneg_right ha_le (by positivity)
    _ = 2 := by field
  nlinarith [hlog]


lemma log_chebC_le {n : ℕ} (hn : 12 ≤ n) :
    Real.log (chebC n) ≤
      ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * n +
        6 * Real.log n + 7 := by
  have hfa : ∀ m : ℕ, (m !) ≠ 0 := fun m ↦ Nat.factorial_ne_zero m
  set a := n / 2 with ha2
  set b := n / 3 with hb3
  set c := n / 6 with hc6
  have hd := chebC_aux_dvd n
  have hDpos : (0 : ℝ) < ((a ! * b ! * c ! : ℕ) : ℝ) := by positivity
  have hlogC : Real.log (chebC n) =
      Real.log (n !) - (Real.log (a !) + Real.log (b !) + Real.log (c !)) := by
    have h1 : ((chebC n : ℕ) : ℝ) = (n ! : ℝ) / ((a ! * b ! * c ! : ℕ) : ℝ) := by
      rw [chebC]
      exact Nat.cast_div hd (by positivity)
    have hf0 : ∀ m : ℕ, ((m ! : ℕ) : ℝ) ≠ 0 :=
      fun m ↦ Nat.cast_ne_zero.mpr (hfa m)
    rw [h1, Real.log_div (hf0 n) (by positivity), Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (mul_ne_zero (hf0 a) (hf0 b)) (hf0 c),
      Real.log_mul (hf0 a) (hf0 b)]
  have hup := log_factorial_upper n
  have hlo_a := log_factorial_lower a
  have hlo_b := log_factorial_lower b
  have hlo_c := log_factorial_lower c
  have h2 := div_mul_log_le (n := n) (d := 2) (by norm_num) (by omega)
  have h3 := div_mul_log_le (n := n) (d := 3) (by norm_num) (by omega)
  have h6 := div_mul_log_le (n := n) (d := 6) (by norm_num) (by omega)
  have hr : ∃ r : ℕ, n - (a + b + c) = r ∧ r ≤ 5 := ⟨n - (a+b+c), rfl, by omega⟩
  obtain ⟨r, hreq, hr5⟩ := hr
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hcast : ((a + b + c : ℕ) : ℝ) = a + b + c := by norm_cast
  have hr_cast : ((n - (a + b + c) : ℕ) : ℝ) = (n : ℝ) - (a + b + c : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have ha_le : (a : ℝ) ≤ (n : ℝ) / 2 := by rw [ha2]; exact Nat.cast_div_le
  have hb_le : (b : ℝ) ≤ (n : ℝ) / 3 := by rw [hb3]; exact Nat.cast_div_le
  have hc_le : (c : ℝ) ≤ (n : ℝ) / 6 := by rw [hc6]; exact Nat.cast_div_le
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hlog6eq : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have habc : (a : ℝ) + b + c = n - r := by
    have hreqr : (r : ℝ) = (n : ℝ) - ((a : ℝ) + b + c) := by
      rw [← hreq]; exact hr_cast
    linarith
  calc Real.log (chebC n)
      = Real.log (n !) - Real.log (a !) - Real.log (b !) - Real.log (c !) := by
        rw [hlogC]; ring
    _ ≤ ((n : ℝ) * Real.log n - n + 1 + Real.log n)
        - ((a : ℝ) * Real.log a - a)
        - ((b : ℝ) * Real.log b - b)
        - ((c : ℝ) * Real.log c - c) := by
        linarith
    _ ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n
        + (-(a : ℝ) * (Real.log n - Real.log 2) + 2 + a)
        + (-(b : ℝ) * (Real.log n - Real.log 3) + 2 + b)
        + (-(c : ℝ) * (Real.log n - Real.log 6) + 2 + c) := by
        linarith [h2, h3, h6]
    _ = ((n : ℝ) - (a + b + c)) * Real.log n
        + ((a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 + (c : ℝ) * Real.log 6)
        - n + a + b + c + Real.log n + 7 := by ring
    _ = (r : ℝ) * Real.log n
        + ((a : ℝ) * Real.log 2 + (b : ℝ) * Real.log 3 + (c : ℝ) * Real.log 6)
        - r + Real.log n + 7 := by
        have hnr : (n : ℝ) - (a + b + c) = (r : ℝ) := by
          rw [← hreq]; exact hr_cast.symm
        rw [hnr]
        linarith [habc]
    _ ≤ 5 * Real.log n
        + ((n : ℝ) / 2 * Real.log 2 + (n : ℝ) / 3 * Real.log 3 +
            (n : ℝ) / 6 * Real.log 6)
        + Real.log n + 7 := by
        have h1 : (r : ℝ) * Real.log n ≤ 5 * Real.log n := by
          apply mul_le_mul_of_nonneg_right _ hlogn
          exact_mod_cast hr5
        have h2' : (a : ℝ) * Real.log 2 ≤ (n : ℝ) / 2 * Real.log 2 :=
          mul_le_mul_of_nonneg_right ha_le hlog2
        have h3' : (b : ℝ) * Real.log 3 ≤ (n : ℝ) / 3 * Real.log 3 :=
          mul_le_mul_of_nonneg_right hb_le hlog3
        have h4' : (c : ℝ) * Real.log 6 ≤ (n : ℝ) / 6 * Real.log 6 :=
          mul_le_mul_of_nonneg_right hc_le hlog6
        have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
        linarith
    _ = ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * n +
          6 * Real.log n + 7 := by
        rw [hlog6eq]; ring


lemma chebC_pos (n : ℕ) : 0 < chebC n := by
  have hd := chebC_aux_dvd n
  have h := Nat.div_mul_cancel hd
  by_contra hz
  rw [not_lt, Nat.le_zero] at hz
  change n ! / ((n / 2)! * (n / 3)! * (n / 6)!) = 0 at hz
  rw [hz] at h
  exact Nat.factorial_ne_zero n (by simpa using h.symm)

lemma chebC_prime_dvd {n p : ℕ} (hp : p.Prime) (hlo : n / 6 < p) (hhi : p ≤ n) :
    p ∣ chebC n := by
  have hfa : ∀ m : ℕ, (m !) ≠ 0 := fun m ↦ Nat.factorial_ne_zero m
  have hD : (n / 2)! * (n / 3)! * (n / 6)! ≠ 0 := by positivity
  have hd := chebC_aux_dvd n
  have hC : chebC n ≠ 0 := (chebC_pos n).ne'
  rw [hp.dvd_iff_one_le_factorization hC]
  have hmul : chebC n * ((n / 2)! * (n / 3)! * (n / 6)!) = n ! := Nat.div_mul_cancel hd
  have hfact : (chebC n).factorization p =
      (n !).factorization p - ((n / 2)! * (n / 3)! * (n / 6)!).factorization p := by
    have h := congrArg (fun m : ℕ ↦ m.factorization p) hmul
    rw [Nat.factorization_mul hC hD, Finsupp.add_apply] at h
    exact Nat.eq_sub_of_add_eq h
  have hlog : ∀ m : ℕ, m ≤ n → Nat.log p m < n + 1 := by
    intro m hm; have h := Nat.log_le_self p m; omega
  rw [hfact,
    Nat.factorization_factorial hp (hlog _ le_rfl),
    Nat.factorization_mul (by positivity) (hfa _), Finsupp.add_apply,
    Nat.factorization_mul (hfa _) (hfa _), Finsupp.add_apply,
    Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
    Nat.factorization_factorial hp (hlog _ (Nat.div_le_self _ _)),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_tsub_distrib _
      (f := fun i ↦ n / p ^ i)
      (g := fun i ↦ n / 2 / p ^ i + n / 3 / p ^ i + n / 6 / p ^ i)
      (fun i _ ↦ by
        show n / 2 / p ^ i + n / 3 / p ^ i + n / 6 / p ^ i ≤ n / p ^ i
        rw [cheb_div_div_pow_comm, cheb_div_div_pow_comm, cheb_div_div_pow_comm]
        exact cheb_floor_le _)]
  rw [cheb_div_div_pow_comm, cheb_div_div_pow_comm, cheb_div_div_pow_comm]
  refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦ n / p ^ i -
    ((n / p ^ i) / 2 + (n / p ^ i) / 3 + (n / p ^ i) / 6)) (fun i _ ↦ Nat.zero_le _)
    (by exact Finset.mem_Ico.mpr ⟨le_refl 1, by have := hp.two_le; omega⟩))
  · have ht1 : 1 ≤ n / p := Nat.div_pos hhi hp.pos
    have ht2 : n / p < 6 := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      have : n < 6 * p := by
        have h' := hlo
        rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 6)] at h'
        omega
      omega
    simp only [pow_one]
    omega

lemma chebC_prod_dvd (n : ℕ) :
    ∏ p ∈ (Ioc (n / 6) n).filter Nat.Prime, p ∣ chebC n := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact ((mem_filter.mp hp).2).prime
  · intro p hp
    obtain ⟨hmem, hp'⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hmem
    exact chebC_prime_dvd hp' hlo hhi

lemma primorial_split (n : ℕ) :
    primorial n = primorial (n / 6) *
      ∏ p ∈ (Ioc (n / 6) n).filter Nat.Prime, p := by
  rw [primorial_eq_prod_primesLE, primorial_eq_prod_primesLE]
  have hsplit : primesLE n =
      primesLE (n / 6) ∪ (Ioc (n / 6) n).filter Nat.Prime := by
    ext p
    simp only [mem_primesLE, mem_union, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt p (n / 6) with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨h, h1⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1.trans (Nat.div_le_self _ _), h2⟩
      · exact ⟨h2, h3⟩
  rw [hsplit, Finset.prod_union]
  rw [Finset.disjoint_left]
  intro p hpA hpB
  have h1 := (mem_primesLE.mp hpA).1
  have h2 := (mem_Ioc.mp (mem_filter.mp hpB).1).1
  omega

lemma theta_sub_theta_le_log_chebC (n : ℕ) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n / 6 : ℕ) : ℝ) ≤
      Real.log (chebC n) := by
  have hprod_pos : (0 : ℕ) < ∏ p ∈ (Ioc (n / 6) n).filter Nat.Prime, p :=
    Finset.prod_pos fun p hp ↦ ((mem_filter.mp hp).2).pos
  have hsplit := primorial_split n
  have hlog : Real.log ((primorial n : ℕ) : ℝ) =
      Real.log ((primorial (n / 6) : ℕ) : ℝ) +
        Real.log ((∏ p ∈ (Ioc (n / 6) n).filter Nat.Prime, p : ℕ) : ℝ) := by
    rw [hsplit, Nat.cast_mul, Real.log_mul]
    · exact_mod_cast (primorial_pos _).ne'
    · exact_mod_cast hprod_pos.ne'
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial,
    Nat.floor_natCast, Nat.floor_natCast, hlog, add_sub_cancel_left]
  apply Real.log_le_log (by exact_mod_cast hprod_pos)
  exact_mod_cast le_of_dvd (chebC_pos n) (chebC_prod_dvd n)


lemma theta_sub_theta_sixth {n : ℕ} (hn : 1 ≤ n) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n / 6 : ℕ) : ℝ) ≤
      ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * n +
        6 * Real.log n + 7 := by
  rcases le_or_gt 12 n with h | h
  · exact (theta_sub_theta_le_log_chebC n).trans (log_chebC_le h)
  · have h1 : Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n / 6 : ℕ) : ℝ) ≤
        Chebyshev.theta (n : ℝ) := by
      linarith [Chebyshev.theta_nonneg ((n / 6 : ℕ) : ℝ)]
    have h2 := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity)
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    have hdiff : Real.log 4 - ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) ≤
        (4 : ℝ) / 10 := by
      have h2l : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have h3l : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
      have h2g : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      have h3g : 1.0986122885 < Real.log 3 := Real.log_three_gt_d9
      rw [hlog4]
      linarith
    have hnn : (n : ℝ) ≤ 11 := by exact_mod_cast (by omega : n ≤ 11)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hdiff0 : 0 ≤ Real.log 4 -
        ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) := by
      have h2g : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
      have h3l : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
      rw [hlog4]; linarith
    have h3 : Real.log 4 * (n : ℝ) ≤
        ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * n +
          6 * Real.log n + 7 := by
      have key : (Real.log 4 -
          ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3)) * n ≤ 7 := by
        calc _ ≤ (4 / 10 : ℝ) * n :=
              mul_le_mul_of_nonneg_right hdiff hn0
          _ ≤ (4 / 10 : ℝ) * 11 :=
              mul_le_mul_of_nonneg_left hnn (by norm_num)
          _ ≤ 7 := by norm_num
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
      linarith [key]
    linarith [h1, h2, h3]

theorem theta_le_explicit (n : ℕ) :
    Chebyshev.theta (n : ℝ) ≤
      ((4 / 5 : ℝ) * Real.log 2 + (3 / 5) * Real.log 3) * n +
        6 * (Real.log n) ^ 2 + 7 * Real.log n + 7 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [Chebyshev.theta_zero]
  set t := Nat.log 6 n with ht
  have ht_pow : 6 ^ t ≤ n := Nat.pow_log_le_self 6 hn0
  have ht_lt : n < 6 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hdiv_ge : ∀ i : ℕ, i < t → 1 ≤ n / 6 ^ i := by
    intro i hi
    have : 6 ^ (i + 1) ≤ n := (pow_le_pow_right₀ (by norm_num)
      (Nat.succ_le_of_lt hi)).trans ht_pow
    have h6 : (0 : ℕ) < 6 ^ i := by positivity
    rw [Nat.le_div_iff_mul_le h6]
    calc 1 * 6 ^ i = 6 ^ i := by ring
    _ ≤ n := by
      calc 6 ^ i ≤ 6 ^ (i + 1) := by
            apply pow_le_pow_right₀ (by norm_num); omega
      _ ≤ n := this
  have htel : Chebyshev.theta (n : ℝ) - Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) =
      ∑ i ∈ Finset.range t,
        (Chebyshev.theta ((n / 6 ^ i : ℕ) : ℝ) -
          Chebyshev.theta ((n / 6 ^ (i + 1) : ℕ) : ℝ)) := by
    rw [Finset.sum_range_sub' (fun i ↦ Chebyshev.theta ((n / 6 ^ i : ℕ) : ℝ)) t]
    simp
  have hterm : ∀ i ∈ Finset.range t,
      Chebyshev.theta ((n / 6 ^ i : ℕ) : ℝ) -
          Chebyshev.theta ((n / 6 ^ (i + 1) : ℕ) : ℝ) ≤
        ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) *
            ((n / 6 ^ i : ℕ) : ℝ) +
          6 * Real.log ((n / 6 ^ i : ℕ) : ℝ) + 7 := by
    intro i hi
    have hi' : i < t := Finset.mem_range.mp hi
    have hge : 1 ≤ n / 6 ^ i := hdiv_ge i hi'
    have hstep := theta_sub_theta_sixth (n := n / 6 ^ i) hge
    have hdiv : (n / 6 ^ i) / 6 = n / 6 ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [hdiv] at hstep
    exact hstep
  have hsum_div : ∑ i ∈ Finset.range t, ((n / 6 ^ i : ℕ) : ℝ) ≤ (6 : ℝ) / 5 * n := by
    calc ∑ i ∈ Finset.range t, ((n / 6 ^ i : ℕ) : ℝ)
        ≤ ∑ i ∈ Finset.range t, (n : ℝ) / 6 ^ i := by
          apply Finset.sum_le_sum
          intro i _
          have h := Nat.cast_div_le (α := ℝ) (m := n) (n := 6 ^ i)
          simp only [Nat.cast_pow, Nat.cast_ofNat] at h
          exact h
      _ = (n : ℝ) * ∑ i ∈ Finset.range t, ((1 / 6 : ℝ)) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [div_pow, one_pow, mul_one_div]
      _ = (n : ℝ) * ((1 - (1 / 6 : ℝ) ^ t) / (1 - 1 / 6)) := by
          congr 1
          rw [geom_sum_eq (by norm_num : (1 / 6 : ℝ) ≠ 1)]
          field
      _ ≤ (n : ℝ) * (6 / 5 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 1/6)]
          have : (0 : ℝ) ≤ (1 / 6 : ℝ) ^ t := by positivity
          linarith
      _ = _ := by ring
  have hlog_le : ∀ i ∈ Finset.range t,
      Real.log ((n / 6 ^ i : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    intro i hi
    apply Real.log_le_log
    · exact_mod_cast (hdiv_ge i (Finset.mem_range.mp hi))
    · exact_mod_cast Nat.div_le_self n (6 ^ i)
  have hlast : Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) ≤ 7 := by
    have hlt6 : n / 6 ^ t < 6 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0 : ℕ) < 6 ^ t)]
      calc n < 6 ^ (t + 1) := ht_lt
      _ = 6 * 6 ^ t := by rw [pow_succ]; ring
    have hle : ((n / 6 ^ t : ℕ) : ℝ) ≤ (5 : ℝ) := by
      exact_mod_cast (by omega : n / 6 ^ t ≤ 5)
    calc Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ)
        ≤ Chebyshev.theta (5 : ℝ) := Chebyshev.theta_mono hle
      _ ≤ Real.log 4 * 5 := Chebyshev.theta_le_log4_mul_x (by norm_num)
      _ ≤ 7 := by
          have h2l : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
          have hlog4 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
          rw [hlog4]; linarith
  have ht_log : (t : ℝ) ≤ Real.log (n : ℝ) := by
    have h1 : (6 : ℝ) ^ t ≤ (n : ℝ) := by exact_mod_cast ht_pow
    have h2 : Real.log ((6 : ℝ) ^ t) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : (1 : ℝ) ≤ Real.log 6 := by
      have : Real.log (Real.exp 1) ≤ Real.log (6 : ℝ) :=
        Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
      rwa [Real.log_exp] at this
    calc (t : ℝ) = t * 1 := by ring
    _ ≤ t * Real.log 6 := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Real.log (n : ℝ) := h2
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hmain : Chebyshev.theta (n : ℝ) ≤
      Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) +
        ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * ((6 : ℝ) / 5 * n) +
          (6 * Real.log n + 7) * t := by
    calc Chebyshev.theta (n : ℝ)
        = Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) +
            ∑ i ∈ Finset.range t,
              (Chebyshev.theta ((n / 6 ^ i : ℕ) : ℝ) -
                Chebyshev.theta ((n / 6 ^ (i + 1) : ℕ) : ℝ)) := by
          linarith [htel]
      _ ≤ Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) +
            ∑ i ∈ Finset.range t,
              (((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) *
                  ((n / 6 ^ i : ℕ) : ℝ) +
                6 * Real.log ((n / 6 ^ i : ℕ) : ℝ) + 7) := by
          have hs := Finset.sum_le_sum fun i hi ↦ hterm i hi
          linarith
      _ = Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) +
            (((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) *
              (∑ i ∈ Finset.range t, ((n / 6 ^ i : ℕ) : ℝ)) +
            ∑ i ∈ Finset.range t, (6 * Real.log ((n / 6 ^ i : ℕ) : ℝ) + 7)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ Chebyshev.theta ((n / 6 ^ t : ℕ) : ℝ) +
            (((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) *
              ((6 : ℝ) / 5 * n) +
            ∑ i ∈ Finset.range t, (6 * Real.log n + 7)) := by
          have hcoef : (0 : ℝ) ≤ (2 / 3) * Real.log 2 + (1 / 2) * Real.log 3 := by
            have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
            have h3 := Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)
            linarith
          have hs2 : ∑ i ∈ Finset.range t,
                  (6 * Real.log ((n / 6 ^ i : ℕ) : ℝ) + 7) ≤
                ∑ i ∈ Finset.range t, (6 * Real.log (n : ℝ) + 7) := by
            apply Finset.sum_le_sum
            intro i hi
            have := hlog_le i hi
            linarith
          have hm := mul_le_mul_of_nonneg_left hsum_div hcoef
          linarith
      _ = _ := by simp [nsmul_eq_mul]; ring
  have hlast' : ((6 * Real.log n + 7) : ℝ) * t ≤ (6 * Real.log n + 7) * Real.log n := by
    apply mul_le_mul_of_nonneg_left ht_log
    linarith
  have hc1 : ((2 / 3 : ℝ) * Real.log 2 + (1 / 2) * Real.log 3) * ((6 : ℝ) / 5 * n) =
      ((4 / 5 : ℝ) * Real.log 2 + (3 / 5) * Real.log 3) * n := by ring
  linarith [hmain, hlast, hlast', hc1]

lemma eventually_log_sq_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      6 * (Real.log (n : ℝ)) ^ 2 + 7 * Real.log (n : ℝ) + 7 ≤
        (33 / 1000 : ℝ) * n := by
  have h₁ := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 2)
    (by norm_num)).comp_tendsto tendsto_natCast_atTop_atTop
  have h₁ := h₁.bound (by norm_num : (0 : ℝ) < 1 / 20)
  have h₂ := (Real.isLittleO_log_id_atTop).comp_tendsto tendsto_natCast_atTop_atTop
  have h₂ := h₂.bound (by norm_num : (0 : ℝ) < 1 / 1000)
  filter_upwards [h₁, h₂, Filter.eventually_ge_atTop 7000,
    Filter.eventually_ge_atTop 1] with n h₁ h₂ h7000 h1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
  simp only [Function.comp_apply, id_eq] at h₁ h₂
  rw [Real.norm_eq_abs, abs_of_nonneg hlogn, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) ^ (1/2 : ℝ))] at h₁
  rw [Real.norm_eq_abs, abs_of_nonneg hlogn, Real.norm_eq_abs,
    abs_of_nonneg hn0.le] at h₂
  rw [← Real.sqrt_eq_rpow] at h₁
  have hsqrt : (0 : ℝ) ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (√(n : ℝ) / 20) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · linarith [h₁]
  rw [div_pow, Real.sq_sqrt (by positivity)] at hsq
  have h7 : (7 : ℝ) ≤ (1 : ℝ) / 1000 * n := by
    have : (n : ℝ) ≥ 7000 := by exact_mod_cast h7000
    linarith
  nlinarith [hsq, h₂, h7, hlogn]

theorem chebyshev_theta_lt : ∃ c : ℝ, c < (127 : ℝ) / 100 ∧
    ∀ᶠ n : ℕ in Filter.atTop, Chebyshev.theta (n : ℝ) ≤ c * n := by
  refine ⟨5 / 4, by norm_num, ?_⟩
  filter_upwards [eventually_log_sq_le] with n hn
  have hbound := theta_le_explicit n
  have hc1 : ((4 / 5 : ℝ) * Real.log 2 + (3 / 5) * Real.log 3) ≤
      1217 / 1000 := by
    have h2l : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have h3l : Real.log 3 < 1.0986122888 := Real.log_three_lt_d9
    linarith
  have hc10 : (0 : ℝ) ≤ ((4 / 5 : ℝ) * Real.log 2 + (3 / 5) * Real.log 3) := by
    have h2g : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    have h3g : 1.0986122885 < Real.log 3 := Real.log_three_gt_d9
    linarith
  nlinarith [hn, hbound, hc1]

theorem chebyshev_primorial_lt : ∃ c : ℝ, c < (127 : ℝ) / 100 ∧
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (primorial n) ≤ c * n := by
  obtain ⟨c, hc, h⟩ := chebyshev_theta_lt
  refine ⟨c, hc, ?_⟩
  filter_upwards [h] with n hn
  rwa [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hn

end JSP314
