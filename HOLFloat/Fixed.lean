import Mathlib
import HOLFloat.Common

def is_valid_fformat (r p : Int) : Bool :=
  1 < r ∧ r % 2 == 0 ∧ 0 < p

structure fformat where
  r : ℚ 
  p : ℤ 
  e : ℤ 
deriving Repr


#check fformat.mk 1 2 3

def is_frac (fmt : fformat)(x: ℚ)(f: ℤ) : Prop :=
  let e1 := fmt.r ^ (fmt.p - 1)
  let p1 := f ≤ e1
  let p2 := |x| = f * fmt.r ^ (fmt.e - fmt.p + 1)
  p1 ∧ p2  
open Classical

noncomputable def ff (fmt: fformat)(x: ℚ) : ℤ := 
  Classical.epsilon (is_frac fmt x)

def is_fixed (fmt: fformat)(x: ℚ) : Prop :=
  ∃ f, is_frac fmt x f

def is_fin_fixed (fmt: fformat)(x: ℚ) : Prop :=
  ∃ f, is_frac fmt x f ∧ f < fmt.r ^ (fmt.p - 1)

-- fix point ulp

def fulp (fmt: fformat) : ℚ :=
  fmt.r ^ (fmt.e - fmt.p + 1)

def finf (fmt: fformat) : ℚ :=
  fmt.r ^ fmt.e

abbrev fixed (fmt: fformat) : Set ℚ :=
  fun (x: ℚ) => is_fixed fmt x

