--TODO: Port Theorems. 
import Mathlib
import HOLFloat.Common
import HOLFloat.Fixed
import HOLFloat.Float
import Aesop
set_option trace.aesop.steps true
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

@[aesop unsafe]
def is_greatest_e (fmt : flformat)(x : ℝ)(e : ℤ) : Prop :=
  (fmt.val.r : ℝ) ^ e  ≤ |x| ∧
  ∀(e' : ℤ), (fmt.val.r : ℝ) ^ e' ≤ |x| → e' ≤ e

#eval (2 : ℤ) ^ (-2 : ℤ)

@[simp]
theorem float_greatest_e_exists (fmt:flformat) (x : ℝ)(e : ℤ) : x ≠ 0 → e = greatest_e fmt x → is_greatest_e fmt x e :=  by
  have ⟨fmt_val, FMT⟩ := fmt
  intro hx he
  simp only [greatest_e, is_greatest_e] at *
  simp only [ne_eq, Int.cast_eq_zero]
  apply And.intro
  case left =>
    norm_cast
    suffices e ∈  { z : ℤ | (fmt_val.r : ℝ) ^ z ≤ abs x } by {
      have H := this.out;
      have R_GT_1 : 1 < fmt_val.r := FMT.left;
      norm_cast at H;
    }
    rw[he];
    apply Int.csupₛ_mem;
    case h1 => {
      have R_GT_1 : 1 < fmt_val.r := FMT.left;
      -- show the existnece of a negative z that makes this true.
      -- please kill me
      -- ok
      -- r ^ z < x → (1 / (r ^ z)) > x → (1/r) ^ z > x, use pow_unbounded_of_one_lt
      -- writing this won't shoot myself
      simp[Set.Nonempty]; sorry
    }
    case h2 => {
      exists 42 -- fake bound, need log.
      simp[BddAbove];
      simp[upperBounds];
      intros a H;
      sorry -- need some theory of log to exhibit an upper bound
      
    }
  case right => sorry

def is_greatest_m (fmt:flformat) (x: ℝ) (m : ℤ): Prop :=
  m * (fmt.val.r : ℝ) ^ (greatest_e fmt x) ≤ |x| ∧
  ∃(m' : ℤ), m * (fmt.val.r : ℝ)  ^ (greatest_e fmt x) ≤ |x| → m' <= m

--NOTE: theorems for mantissa
@[simp]
theorem float_greatest_m_exists (fmt : flformat)(x : ℝ) (m : ℤ): 
  x ≠ 0 
  → greatest_m fmt x = m 
  → is_greatest_m fmt x m ∧ 1 ≤ m ∧ m < fmt.val.r := by
  sorry
--NOTE: theorems for exponent
theorem is_greatest_e_exist_greatest_e (fmt :flformat)( e : ℤ) : x ≠ 0 → is_greatest_e fmt x e → greatest_e fmt x = e := by
  intro hx he
  simp
  sorry

--TODO: theorem float_normalize_real
@[simp]
theorem float_normalize_real (fmt : flformat) (x : ℝ) : x < 0 → x = greatest_m fmt x * (fmt.val.r : ℝ) ^ greatest_e fmt x + greatest_r fmt x := by
  intro h
  sorry
@[simp]
theorem float_eq_ipow (fmt : flformat) (x : ℝ)(e : ℤ)(m : ℤ) :
  x ≠ 0 → 1 ≤ m → m < fmt.val.r → |x| = m * (fmt.val.r : ℝ) ^ e 
  → greatest_e fmt x  = e ∧ greatest_m fmt x = m  := by
  intros hx hm hr he
  apply And.intro
  case left =>
    sorry
  case right =>
    sorry

