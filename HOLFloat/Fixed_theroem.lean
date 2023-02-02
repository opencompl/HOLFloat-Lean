import Mathlib
import HOLFloat.Common
import HOLFloat.Fixed

--TODO: move all the theorems here

--set_option pp.all  true
--
#check is_valid_fformat 1 2

theorem fformat_valid_imp_radix_lt_one {r : Int}{p : ℤ} : is_valid_fformat r p → 1 < r := by
  intro h; exact h.left

theorem fformat_valid_imp_radix_even {r : Int}{p : ℤ} : is_valid_fformat r p → r % 2 = 0 := by
  intro h; exact h.right.left

theorem fformat_valid_imp_prec_lt_0 {r : ℤ}{p : ℤ} : is_valid_fformat r p → 0 < p := by
  intro h; exact h.right.right

theorem fformat_radix_lt_1: ∀ (fmt : fformat), 1 < fmt.val.r := by
  intro h
  exact h.prop.left

theorem fformat_radix_lt_0 : ∀ (fmt : fformat), 0 < fmt.val.r := by
  intro h
  have h₁ := h.prop.left
  have h₂ : 0 < (1 : Int) := by trivial
  apply Int.lt_trans h₂ h₁

theorem  gt_zero_ne_zero (x : Int) : 1 < x → x ≠ 0 := by
  intros h h₁; simp [h₁] at h;

theorem fformat_radix_ne_0 : ∀(fmt : fformat), fmt.val.r ≠ 0 := by
  intro h;
  have h₁ := h.prop.left
  apply gt_zero_ne_zero; trivial
