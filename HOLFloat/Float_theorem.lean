--TODO: Port Theorems. 
--
import Mathlib
import HOLFloat.Common
import HOLFloat.Fixed
import HOLFloat.Float
import Aesop
set_option trace.aesop.steps true
/-
let FLOAT_NORMALIZE_REAL =
  prove(`!(fmt:flformat) (x:real). ~(x = &0) ==>
	  (if (&0 <= x)
	   then
	     x = &(greatest_m(fmt) x) * &(flr fmt) ipow (greatest_e(fmt) x) +
		 (greatest_r(fmt) x)
	   else 
	     x = -- (&(greatest_m(fmt) x) * 
                     &(flr fmt) ipow (greatest_e(fmt) x)) +
		 (greatest_r(fmt) x))`,
	REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "xneq0") THEN
	USE_THEN "xneq0" (fun xneq0 -> old_dump_ge_gm_gr_info xneq0) THEN
        REWRITE_TAC[greatest_r] THEN ASM_REWRITE_TAC[] THEN
        ARITH_TAC);;
-/
-- NOTE: goal: prove FLOAT_NORMALIZE_REAL

@[simp]
theorem flformat_radix_lt_0 (fmt:flformat) : 0 < fmt.val.r := by
  linarith [fmt.prop.left]

@[simp]
theorem flformat_radix_lt_1 (fmt:flformat) : 1 < fmt.val.r := by
  linarith [fmt.prop.left]

@[simp]
theorem flformat_radix_le_2 (fmt:flformat): 2 ≤ fmt.val.r := by
  linarith [fmt.prop.left]

@[simp]
theorem flformat_radix_lt_0_real (fmt : flformat): 0 < (fmt.val.r : ℝ) := by
  norm_cast
  linarith [fmt.prop.left]

@[simp]
theorem flformat_radix_lt_1_real (fmt: flformat) : 1 < (fmt.val.r : ℝ) := by
  norm_cast
  linarith [fmt.prop.left]

@[simp, norm_cast]
theorem cast_two: ((2 : ℤ) : ℝ) = 2 :=
  Int.cast_ofNat 2

@[simp]
theorem flformat_radix_le_2_real (fmt: flformat) : 2 ≤ (fmt.val.r : ℝ) := by
  norm_cast
  linarith [Int.lt_add_one_iff.2 fmt.prop.left, fmt.prop.left]


@[simp]
theorem float_radix_ipow_lt_0 (fmt: flformat)(e : ℤ) : 0 < (fmt.val.r: ℝ) ^ e := by
  have h : 0 < fmt.val.r := by apply Int.one_lt_zero_lt; exact fmt.prop.left
  apply ipow_lt_zero
  simp_all only [Int.one_lt_zero_le_iff, zero_add, Int.cast_pos]

@[simp]
theorem float_ipow_le_real (fmt :flformat)(x : ℝ) : ∃(e : ℤ), x ≤ ((fmt.val.r : ℝ ) ^ e) := by
  apply ipow_le_real --FIXME: wait for port
  case a =>
    simp [flformat_radix_le_2]


@[simp]
theorem float_ipow_le_real_2 (fmt :flformat)(x : ℝ) : 0 < x → ∃(e:ℤ), x ≤(fmt.val.r : ℝ) ^ e  := by
  norm_cast
  intros
  apply ipow_le_real
  simp_all only [flformat_radix_le_2_real]

