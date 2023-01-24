import Mathlib
import HOLFloat.Common

def is_valid_fformat (r p : Int) : Bool :=
  1 < r ∧ r % 2 == 0 ∧ 0 < p

structure fformat where
  r : ℝ
  p : ℤ
  e : ℤ


#check fformat.mk 1 2 3

def is_frac (fmt : fformat)(x: ℝ)(f: ℤ) : Prop :=
  let e1 := fmt.r ^ (fmt.p - 1)
  let p1 := f ≤ e1
  let p2 := |x| = f * fmt.r ^ (fmt.e - fmt.p + 1)
  p1 ∧ p2

open Classical

noncomputable def ff (fmt: fformat)(x: ℝ) : ℤ :=
  Classical.epsilon (is_frac fmt x)

def is_fixed (fmt: fformat)(x: ℝ) : Prop :=
  ∃ f, is_frac fmt x f
def is_fin_fixed (fmt: fformat)(x: ℝ) : Prop :=
  ∃ f, is_frac fmt x f ∧ f < fmt.r ^ (fmt.p - 1)

-- fix point ulp

noncomputable def fulp (fmt: fformat) : ℝ :=
  fmt.r ^ (fmt.e - fmt.p + 1)

noncomputable def finf (fmt: fformat) : ℝ :=
  fmt.r ^ fmt.e

abbrev fixed (fmt: fformat) : Set ℝ :=
  fun x: ℝ => is_fixed fmt x

#check fixed (fformat.mk 1 2 3)
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
#check roundmode.to_near
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
