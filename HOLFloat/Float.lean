import HOLFloat.Common
import HOLFloat.Fixed
import Mathlib
import Aesop
--set_option pp.all true
def is_valid_flformat (fmt : format): Prop :=
    1 < fmt.r
  ∧ fmt.r % 2 = 0
  ∧ 1 < fmt.p


abbrev flformat : Type :=
  {fmt : format // is_valid_flformat fmt}


def flformat.pnat : flformat → ℕ 
| { val := { r := r, p := p, e := e}, property := P } => p.toNat
  /-
  \ in an flformat, the 'p' is always > 0, and is thus
  a natural number
  -/

def is_frac_and_exp (fmt: flformat)(x : ℝ)(f : ℤ)(e : ℤ): Prop:= 
  0 < f 
  ∧ f < fmt.val.r  ^ fmt.pnat
  ∧ |x| = f * ((fmt.val.r ^ (e - fmt.pnat + 1)) : ℝ)

def is_float (fmt: flformat) (x : ℝ): Prop :=
  ∃(f: ℤ)(e :ℤ), is_frac_and_exp fmt x f e

theorem flformat_to_fformat {float : flformat} : is_valid_fformat float.val := by
  apply And.intro
  case left => 
    exact float.prop.left
  case right => 
    apply And.intro
    case left  =>
      exact float.prop.right.left
    case right =>
      apply Int.one_lt_zero_lt
      exact float.prop.right.right

def to_fformat (fmt : flformat): fformat :=
  ⟨fmt.val, by simp [flformat_to_fformat]⟩

instance : Coe flformat fformat where
  coe fmt := to_fformat fmt

-- Normalization
noncomputable def greatest_e (fmt : flformat) (x : ℝ): ℤ :=
  supₛ {z : ℤ | ⟨fmt.val.r ^ z⟩  ≤ |x|}

noncomputable def greatest_m (fmt : flformat) (x : ℝ) : ℝ :=
  supₛ {m : ℝ | m * (fmt.val.r ^ greatest_e fmt x : ℝ) ≤ |x|}

noncomputable def greatest_r ( fmt : flformat ) (x : ℝ) : ℝ := 
  if (0 ≤ x) then 
    (x - greatest_m fmt x) * ((fmt.val.r) ^ (greatest_e fmt x) : ℝ)
  else
    (x + greatest_m fmt x) * ((fmt.val.r) ^ (greatest_e fmt x) : ℝ)

-- Rounding
--
noncomputable def flround (fmt : flformat) (mode : roundmode)( x : Real) : Real :=
  let (m : ℝ) := greatest_m fmt x
  let (e : ℤ) := greatest_e fmt x
  let (r : ℝ) := greatest_r fmt x
  if (0 ≤ x) then
    m * (fmt.val.r ^ e : ℝ) + (fround (Coe.coe fmt) mode r)
  else
    - ((m * (fmt.val.r ^ e : ℝ)) + fround (Coe.coe fmt) mode r)

-- Machine Epsilon
--
-- fl_eps = r ^ (-p + 1) / 2
def fl_eps (fmt : flformat) : ℤ :=
  fmt.val.r ^ (1 - fmt.pnat) / (2 : ℤ)
  
