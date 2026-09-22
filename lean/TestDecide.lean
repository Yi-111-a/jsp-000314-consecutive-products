import Mathlib
set_option maxRecDepth 5000 in
theorem test_check_mid :
    ∀ n ∈ Finset.Icc 16 210, ∀ k ∈ Finset.Icc 8 37,
      2 * k ≤ n → ∃ m ∈ Finset.Icc (n + 1 - k) n, ∃ q ∈ m.primeFactors, k < q := by
  decide
