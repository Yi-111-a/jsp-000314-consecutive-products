import Mathlib

#check @Nat.dvd_sub
#check @Nat.dvd_sub_mod
example (P a b : ℕ) (ha : P ∣ a) (hb : P ∣ b) : P ∣ b - a := by exact?
