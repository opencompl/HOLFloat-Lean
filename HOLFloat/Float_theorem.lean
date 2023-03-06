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
  have h := fmt.prop.left
  apply Int.one_lt_zero_lt
  exact h

@[simp]
theorem flformat_radix_lt_1 (fmt:flformat) : 1 < fmt.val.r := by
  have h := fmt.prop.left
  exact h

@[simp]
theorem flformat_radix_le_2 (fmt:flformat): 2 ≤ fmt.val.r := by
  simp [LE.le, Int.le]
  have h := flformat_radix_lt_1 fmt
  simp_all only [Int.one_lt_zero_le_iff]
  exact h
@[simp]
theorem flformat_radix_lt_0_real (fmt : flformat): 0 < (fmt.val.r : ℝ) := by
  simp only [Int.cast_pos]
  apply flformat_radix_lt_0

@[simp]
theorem cast_lt_right {m n : ℤ} : n < (m : ℝ) ↔ n < m :=
  Int.cast_strictMono.lt_iff_lt

@[simp]
theorem cast_lt_both {m n : ℤ} : (n : ℝ) < (m : ℝ) ↔ n < m := by
  simp_all only [Int.cast_lt, Int.one_lt_zero_le_iff]

@[simp, norm_cast]
theorem cast_one : ((1 : ℤ): ℝ) = 1  := 
  (AddGroupWithOne.intCast_ofNat 1).trans Nat.cast_one
  
@[simp]
theorem cast_one_lt  {n : ℤ} : 1 < (n : ℝ) ↔ 1 < n := by
  rw [←cast_one, cast_lt_right]

@[simp, norm_cast]
theorem cast_two: ((2 : ℤ) : ℝ) = 2 :=
  Int.cast_ofNat 2
@[simp]
theorem cast_two_lt  {n : ℤ} : 2 < (n : ℝ) ↔ 2 < n := by
  rw [←cast_two, cast_lt_right]

@[simp]
theorem flformat_radix_lt_1_real (fmt: flformat) : 1 < (fmt.val.r : ℝ) := by
  rw [cast_one_lt]
  apply flformat_radix_lt_1

@[simp]
theorem flformat_radix_le_2_real (fmt: flformat) : 2 ≤ (fmt.val.r : ℝ) := by
  rw [←cast_two]
  have h := fmt.prop.left
  have two: (1 : ℤ) + 1 = 2 := by trivial
  conv at h =>
    simp [Int.one_lt_zero_le_iff]
    lhs
    rw [two]
  sorry
  --FIXME: types??

@[simp]
theorem float_radix_ipow_lt_0 (fmt: flformat)(e : ℤ) : 0 < (fmt.val.r: ℝ) ^ e := by
  have h : 0 < fmt.val.r := by apply Int.one_lt_zero_lt; exact fmt.prop.left
  apply ipow_lt_zero
  simp_all only [Int.one_lt_zero_le_iff, zero_add, Int.cast_pos]

@[simp]
theorem float_ipow_le_real (fmt :flformat)(x : ℝ) : ∃(e : ℤ), x ≤ ((fmt.val.r : ℝ ) ^ e) := by
  apply ipow_le_real --FIXME: implement this in Common.lean if possible
  case a =>
    simp [flformat_radix_le_2]


@[simp]
theorem float_ipow_le_real_2 (fmt :flformat)(x : ℝ) : 0 < x → ∃(e:ℤ), (fmt.val.r : ℝ ) ^ e ≤ x := by
  sorry


@[simp]
def is_greatest_e (fmt :flformat)(x : ℝ)(e : ℤ) :=
  (fmt.val.r ^ e : ℝ) ≤ |x| ∧ ∀(e₁ : ℤ), (fmt.val.r ^ e₁ :ℝ) ≤ |x|

@[simp]
theorem float_greatest_e_exists (fmt : flformat) (x : ℝ) : x ≠ 0 
  → ∃(e: ℤ), greatest_e fmt x = e ∧ is_greatest_e fmt x e := by
  intro h
  sorry
