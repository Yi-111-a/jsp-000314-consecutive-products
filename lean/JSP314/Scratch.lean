import Mathlib.Tactic

theorem test_omega {k : ℕ} (hk : 42 ≤ k) :
    144 * (k * k) + 588 * k + 600 ≤ 288 * (k * k) + 600 * k + 312 := by
  have hkk : 2 ≤ k * k := le_trans (by norm_num) (Nat.mul_le_mul hk hk)
  omega

theorem test_omega2 {k : ℕ} (hk : 42 ≤ k)
    (hexp : (12 * (k + 1) + 12) * (12 * (k + 1) + 13) =
        144 * (k * k) + 588 * k + 600)
    (hexp' : (12 * k + 12) * (12 * k + 13) =
        144 * (k * k) + 300 * k + 156) :
    (12 * (k + 1) + 12) * (12 * (k + 1) + 13) ≤
      2 * ((12 * k + 12) * (12 * k + 13)) := by
  rw [hexp, hexp']
  have hkk : 2 ≤ k * k := le_trans (by norm_num) (Nat.mul_le_mul hk hk)
  omega
