import JSP314.SieveBase
import JSP314.RunDecomp
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.PrimeCounting

open Finset Nat

#check @Nat.mul_add_mod_self_left
#check @Nat.add_mul_mod_self_left
#check @Nat.add_mul_mod_self_right
#check @Finset.filter_subset_filter
#check @Finset.filter_eq_empty_iff
#check @Finset.card_eq_zero
#check @Nat.ModEq.add_right
#check @Nat.mod_eq_zero_of_dvd
#check @Nat.dvd_iff_mod_eq_zero
#check @Finset.sum_ite_eq
#check @Finset.sum_ite_eq'
#check @Finset.sum_ite
#check @nsmul_eq_mul
#check @Nat.one_le_pow
#check @dvd_pow_self
#check @Finset.sum_add_distrib
#check @Finset.sum_const_zero
#check @Finset.sum_const
#check @Nat.mod_lt
#check @Finset.sum_le_sum
#check @Finset.card_le_card
#check @Nat.add_right_cancel
#check @Nat.le_of_dvd
#check @Nat.div_le_div_right
#check @Finset.sum_ite_eq_of_mem
