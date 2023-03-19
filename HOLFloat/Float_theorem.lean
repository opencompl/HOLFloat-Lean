--TODO: Port Theorems. 
import Mathlib
import HOLFloat.Common
import HOLFloat.Fixed
import HOLFloat.Float
import Aesop
set_option trace.aesop.steps true
--set_option trace.aesop.ruleSet true
--set_option aesop.maxRuleApplications 400
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


@[simp]
theorem pow_le_real (a x : ℝ) (ha1 : a ≠ 1) (hx0 : x ≠ 0) : ∃ (z : ℤ), a ^ z ≤ abs x :=
  if ha0 : a ≤ 0
  then ⟨1, (zpow_one a).symm ▸ le_trans ha0 (abs_nonneg _)⟩
  else if hal1 : a < 1
    then let ⟨k, hk⟩ := pow_unbounded_of_one_lt (abs x)⁻¹ (one_lt_inv (lt_of_not_ge ha0) hal1)
      ⟨k, (inv_le_inv (abs_pos.2 hx0) (pow_pos (lt_of_not_ge ha0) _)).1
        (le_of_lt $ by simpa using hk)⟩
    else let ⟨k, hk⟩ := pow_unbounded_of_one_lt (abs x)⁻¹ (lt_of_le_of_ne (le_of_not_gt hal1) ha1.symm)
      ⟨-k, (inv_le_inv (abs_pos.2 hx0) (zpow_pos_of_pos (lt_of_not_ge ha0) _)).1
        (le_of_lt $ by simpa)⟩
@[simp]
theorem float_greatest_e_exists (fmt:flformat) (x : ℝ)(e : ℤ) : x ≠ 0 → e = greatest_e fmt x → is_greatest_e fmt x e :=  by
  have ⟨fmt_val, FMT⟩ := fmt
  intro hx he
  simp only [greatest_e, is_greatest_e] at *
  simp only [ne_eq, Int.cast_eq_zero]
  apply And.intro

  have R_GT_1 : 1 < fmt_val.r := FMT.left;
  suffices e ∈  { z : ℤ | (fmt_val.r : ℝ) ^ z ≤ abs x } by {
    have H := this.out;
    have R_GT_1 : 1 < fmt_val.r := FMT.left;
    norm_cast at H;
  }

  case left =>
    norm_cast

    rw[he];
    apply Int.csupₛ_mem;

    case h1 => {
     
      simp[Set.Nonempty];
      -- show the existnece of a negative z that makes this true.
      -- please kill me
      apply pow_le_real
      norm_cast
      aesop_subst he
      simp_all only [ne_eq, Int.one_lt_zero_le_iff, Int.one_lt_ne_one, not_false_iff]
      aesop_subst he
      simp_all only [ne_eq, Int.one_lt_zero_le_iff, not_false_iff]
    }
    case h2 => {
      
     --NOTE: exists 42 -- fake bound, need log.
      simp[BddAbove];
      simp[upperBounds, Set.Nonempty];
      exists e
      intros e1 hp
      norm_cast
      have he1: e1 ∈ { z | (fmt_val.r: ℝ) ^ z ≤ abs x } :=  by
        aesop_subst he
        simp_all only [ne_eq, Int.one_lt_zero_le_iff, Int.cast_eq_zero, Set.mem_setOf_eq]
      sorry
    }
  case right =>
    intro e1 hp
    aesop_subst he
    have he1: e1 ∈ { z | (fmt_val.r: ℝ) ^ z ≤ abs x } :=  by
      simp_all only [ne_eq, Int.cast_eq_zero, Set.mem_setOf_eq]
    apply le_csupₛ
    case h₂ =>
      simp_all only [ne_eq, Int.cast_eq_zero, Set.mem_setOf_eq]
    case h₁ =>
      sorry

#check le_supₛ 
#check CompleteSemilatticeSup ℤ 
#check le_csupₛ 
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
    rw [greatest_e]
    norm_cast
    sorry
  case right =>
    sorry





