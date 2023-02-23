import HOLFloat.Common
import HOLFloat.Fixed
import HOLFloat.Float


-- This format is for IEEE
structure format' extends format where
  emin : ℤ
  emax : ℤ
deriving Repr

def is_valid_ieee_format(fmt : format') : Prop :=
    1 < fmt.r 
  ∧ fmt.r % 2 = 0 
  ∧ 1 < fmt.p 
  ∧ fmt.emin ≤ fmt.emax

abbrev ieee_format : Type :=
  {fmt : format' // is_valid_ieee_format fmt}

def ieee_format.pnat : ieee_format → ℕ 
| { val := { r := _, p := p, e := _, emin := _, emax := _ }, property := _ } => p.toNat


-- making common format
def mk_format (fmt : ieee_format) : format :=
    format.mk fmt.val.r fmt.val.p fmt.val.emin

@[simp]
theorem ieee_to_flformat {fmt : ieee_format} : is_valid_flformat (mk_format fmt) := by
  have h := fmt.prop
  apply And.intro
  case left =>
    apply h.left
  case right =>
    apply And.intro
    case left =>
      apply h.right.left
    case right =>
      apply h.right.right.left
      
def to_flformat (fmt : ieee_format): flformat:=
  ⟨mk_format fmt, by apply ieee_to_flformat⟩

--NOTE: is there a way to replace Coe.coe with ⟨⟩ ?
instance : Coe ieee_format fformat where
  coe fmt :=  to_fformat <| to_flformat  fmt

instance : Coe ieee_format flformat where
  coe fmt := to_flformat fmt
-- Largest ieee fp magnitude = f_max * r^(emax - p + 1)
def max_ieee (fmt : ieee_format): ℚ :=
  (fmt.val.r ^ fmt.val.p - (1 : ℚ) )* (fmt.val.r) ^ (fmt.val.emax - fmt.pnat + 1)

def ieee_threshold (fmt :ieee_format) : ℚ :=
  max_ieee fmt + fmt.val.r ^ (fmt.val.emax - fmt.pnat + 1)

def is_ieee_pinf ( fmt : ieee_format) (x : ℝ): Prop :=
  ⟨(ieee_threshold fmt)⟩ ≤ x

def is_ieee_ninf (fmt :ieee_format) (x : ℝ) : Prop :=
  x ≤ ⟨-(ieee_threshold fmt)⟩

def is_ieee (fmt :ieee_format) (x : ℝ) : Prop :=
  is_fixed (Coe.coe fmt) x  
  ∨ (is_float (Coe.coe fmt) x ∧
    fmt.val.emin ≤ greatest_e (Coe.coe fmt) x ∧
    greatest_e (Coe.coe fmt) x ≤ fmt.val.emax) 
  ∨ is_ieee_pinf fmt x
  ∨ is_ieee_ninf fmt x
noncomputable def ieee_exp (fmt : ieee_format)(x : ℝ) : ℤ :=
  if |x| ≤ finf (Coe.coe fmt) then
    fmt.val.emin
  else
    greatest_e (Coe.coe fmt) x


-- Rounding 
--
noncomputable def ieee_round (fmt : ieee_format)(x: ℝ)(mode: roundmode): ℝ :=
  match mode with

  | roundmode.to_near =>
    if |x|  ≤ finf (Coe.coe fmt) then
      fround (Coe.coe fmt) roundmode.to_near x
    else if |x| ≤ ieee_threshold fmt then
      flround (Coe.coe fmt) roundmode.to_near x
    else
      x
  | roundmode.to_zero =>
      if |x| ≤ finf (Coe.coe fmt) then
        fround (Coe.coe fmt) roundmode.to_zero x
      else if |x| ≤  ieee_threshold fmt then
        flround (Coe.coe fmt) roundmode.to_zero x
      else if x > ieee_threshold fmt then
        max_ieee fmt
      else
        - (max_ieee fmt)
  | roundmode.to_pinf =>
      
      if |x|  ≤ finf (Coe.coe fmt) then
        fround (Coe.coe fmt) roundmode.to_pinf x
      else if x ≤ (- max_ieee fmt) then
        - max_ieee fmt
      else
        flround (Coe.coe fmt) roundmode.to_pinf x
  | roundmode.to_ninf =>
      if |x|  ≤ finf (Coe.coe fmt) then
        fround (Coe.coe fmt) roundmode.to_ninf x
      else if max_ieee fmt ≤ x then
        max_ieee fmt
      else
        flround (Coe.coe fmt) roundmode.to_ninf x
-- machine epsilon
def ieee_eps (fmt :ieee_format) :=
  fl_eps (Coe.coe fmt)
