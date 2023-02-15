import Mathlib.Data.Real.Basic
import HOLFloat.Common

--set_option pp.all  true


def is_valid_fformat (x : format) : Prop :=
  1 < x.r ∧ (x.r % 2 = 0) ∧ 0 < x.p

abbrev fformat : Type :=
  {fmt : format // is_valid_fformat fmt}

def is_frac (fmt : fformat )(x: ℝ)(f: ℤ) : Prop :=
  let e1 := fmt.val.r ^ (fmt.val.r - 1)
  let p1 := f ≤ e1
  let p2 := |x| = f * fmt.val.r ^ (fmt.val.e - fmt.val.p + 1)
  p1 ∧ p2

open Classical

noncomputable def ff (fmt: fformat)(x: ℝ) : ℤ :=
  Classical.epsilon (is_frac fmt x)

def is_fixed (fmt: fformat)(x: ℝ) : Prop :=
  ∃ f, is_frac fmt x f
def is_fin_fixed (fmt: fformat)(x: ℝ) : Prop :=
  ∃ f, is_frac fmt x f ∧ f < fmt.val.r ^ (fmt.val.p - 1)

-- fix point ulp

def fulp (fmt: fformat) : ℝ :=
  fmt.val.r ^ (fmt.val.e - fmt.val.p + 1)

def finf (fmt: fformat) : ℝ :=
  fmt.val.r ^ fmt.val.e

abbrev fixed (fmt: fformat) : Set ℝ :=
  { x | is_fixed fmt x}

def is_ub (fmt : fformat) (x y : ℝ) : Prop :=
  y ∈ fixed fmt ∧ x ≤ y

def is_lub (fmt : fformat)(x y : ℝ): Prop :=
  is_ub fmt x y ∧ (∀y₁, is_ub fmt x y₁ → y <= y₁)

noncomputable def glb (fmt: fformat)(x: ℝ): ℝ:=
  supₛ {y: ℝ | y ∈ (fixed fmt) ∧ y <= x}

noncomputable def lub (fmt: fformat)(x: ℝ): ℝ:=
  infₛ {y: ℝ | y ∈ (fixed fmt) ∧ y <= x}

inductive roundmode where
| to_near : roundmode
| to_zero : roundmode
| to_pinf : roundmode
| to_ninf : roundmode

noncomputable def fround (fmt: fformat)(mode : roundmode)(x: ℝ): ℝ :=
  let lo := glb fmt x
  let hi := lub fmt x
  match mode with
  | roundmode.to_near => 
    if (closer lo hi x) then
      lo
    else if (closer hi lo x) then
      hi
    else if (ff (fmt) lo % 2 = 0) then
      hi
    else
      hi
  | roundmode.to_zero =>
    if (0 ≤ x) then
      glb fmt x
    else
      lub fmt x
  | roundmode.to_pinf =>
    lub fmt x
  | roundmode.to_ninf =>
    glb fmt x
