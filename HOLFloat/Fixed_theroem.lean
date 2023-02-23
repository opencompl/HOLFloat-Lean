import Mathlib
import HOLFloat.Common
import HOLFloat.Fixed
-- Note: Using Aesop for proof searches
--set_option pp.all  true

@[simp]
theorem fformat_valid_imp_radix_lt_one {fmt : format} : is_valid_fformat fmt → 1 < fmt.r := by
  intro h; exact h.left

@[simp]
theorem fformat_valid_imp_radix_even {fmt : format} : is_valid_fformat fmt → fmt.r % 2 = 0 := by
  intro h; exact h.right.left

@[simp]
theorem fformat_valid_imp_prec_lt_0 {fmt : format} : is_valid_fformat fmt → 0 < fmt.p := by
  intro h; exact h.right.right

@[simp]
theorem fformat_radix_lt_1: ∀ (fmt : fformat), 1 < fmt.val.r := by
  intro h
  exact h.prop.left

@[simp]
theorem fformat_radix_lt_0 : ∀ (fmt : fformat), 0 < fmt.val.r := by
  intro h
  have h₁ := h.prop.left
  have h₂ : 0 < (1 : Int) := by trivial
  apply Int.lt_trans h₂ h₁

@[simp]
theorem  gt_zero_ne_zero (x : Int) : 1 < x → x ≠ 0 := by
  intros h h₁; simp [h₁] at h;

@[simp]
theorem fformat_radix_ne_0 : ∀(fmt : fformat), fmt.val.r ≠ 0 := by
  intro h;
  have h₁ := h.prop.left
  apply gt_zero_ne_zero; trivial

@[simp]
theorem fformat_radix_even (fmt :fformat) : fmt.val.r % 2 = 0 := by
  simp [fmt.prop.right.left]

@[simp]
theorem fformat_prec_lt_0 (fmt : fformat) : 0 < fmt.val.p := by
  simp [fmt.prop.right.right]

-- NOTE: Don't think we need this
/-
let FFORMAT_PREC_IPOW_EQ_EXP =
  prove(`!(fmt:fformat). &(fr fmt) ipow (&(fp fmt) - &1) = 
      &((fr fmt) EXP ((fp fmt) - 1))`,
	REPEAT GEN_TAC THEN MATCH_MP_TAC IPOW_EQ_EXP_P THEN
	REWRITE_TAC[FFORMAT_PREC_LT_0]);;

-/

@[simp]
theorem fformat_radix_ipow_le_0 (fmt : fformat)(e : ℤ) : fmt.val.r ^ e ≠ 0 := by
  simp [HPow.hPow, Pow.pow]
  cases e with
  | ofNat n =>
    simp [pow_ne_zero]
  | negSucc n =>
    aesop
