import Mathlib
import Std
--set_option pp.all true

def ipow (r : ℝ) (i : ℤ): ℝ :=
  match i with
  | Int.ofNat   n => r ^ n
  | Int.negSucc n => r ^ (0 - n)

#check ipow

#eval ipow 1 (-10)

instance : HPow ℝ ℤ ℝ where
  hPow := ipow

def pow_int(r : ℤ) (i : ℤ): ℤ :=
  match i with
  | Int.ofNat   n => r ^ n
  | Int.negSucc n => r ^ (0 - n)

def real_mul (r : ℝ) (i : ℤ) : ℝ :=
  match i with
  | Int.ofNat   n => r * n
  | Int.negSucc n => r * (0 - n)

instance : HMul ℝ ℤ ℝ where
  hMul := real_mul
instance : HPow ℤ ℤ ℤ where
  hPow := pow_int

theorem ipow_lt_zero {r : ℝ}{i : ℤ} : 0 < r → 0 < r ^ i := by
  intro h
  cases i with
  | ofNat n =>
    sorry
  | negSucc n => 
    sorry

theorem ipow_inv_neg {r : ℝ}{i : ℤ} : r ≠ 0 → r ^ i = Inv.inv (r ^(-i)) := by
  sorry

theorem ipow_add_exp {r : ℝ}(u : ℤ)(v : ℤ) : r ≠ 0 → r ^ u * r ^ v = r ^ (u + v) := by
  sorry

/- 
theorem ipow_eq_exp
theorem ipow_eq_exp_p
-/

theorem ipow_between {x : ℝ}{y z i : ℤ} : 
  (0 < x) → (y * x ^ e ≤ z * x ^ e) → (z * x ^ e ≤ (y + 1) * x ^ e) 
  → (z = y) ∨ (z = y + 1):= by
  sorry
theorem ipow_to_one {r : ℝ} : r ^ 1 = r := by
  simp

theorem ipow_to_zero {r : ℝ} : r ^ 0 = 1 := by
  simp

theorem ipow_le_one {r : ℝ}{i : ℤ} : 1 ≤ r → 0 ≤ i → 1 ≤ r ^ i := by
  sorry

theorem ipow_lt_one {r : ℝ}{i : ℤ} : 1 < r → 0 < i → 1 < r ^ i := by
  sorry
theorem ipow_le_sum {r : ℝ}{n : ℝ} : 2 ≤ r → 0 ≤ i → ∃ e : ℤ , n ≤ r ^ e := by
  sorry

theorem ipow_le_rat {r : ℝ}{z : ℝ} : 2 ≤ r → ∃ e : ℤ , z ≤ r ^ e := by
  sorry
theorem ipow_le_rat_two {r : ℝ}{z : ℝ} : 0 < z → 2 ≤ r → ∃ e : ℤ , r ^ e ≤ z := by
  sorry
theorem ipow_monotone {r : ℝ}{u : ℤ}{v : ℤ} : 2 ≤ r → r ^ u ≤ r ^ v → u ≤ v := by
  sorry
theorem ipow_monotone_two {r : ℝ}{u : ℤ}{v : ℤ} : 1 ≤ r → u ≤ v → r ^ u ≤ r ^ v := by
  sorry
theorem ipow_mul_inv_eq_one {r : ℝ}{i : ℤ} : 0 < r → r ^ i * r ^ (-i) = 1 := by
  sorry

def rerror? {K: Type}[LinearOrderedField K](a : K)(b : K): Option K :=
  if a ≠ 0 then
    let re := |((b - a) / a)|
    some re
  else none

def closer (x y z : ℝ): Prop :=
  abs (x - z) < abs (y - z)
open Int
theorem Int.one_lt_zero_lt (i : ℤ) : 1 < i → 0 < i := by
  intro h
  have hz : (0: ℤ) < 1 := by simp
  apply lt_trans hz h

-- sup inf definitions
def is_sup_int (s : Int → Prop)(e : Int): Prop :=
  s e ∧ ∀(k : Int) , s k → (k ≤ e)

def is_sup_real ( s : ℝ → Prop)(r : ℝ) : Prop :=
  s r ∧  ∀(k : ℝ) , s k → (k ≤ r)

/-
open Classical
noncomputable def sup_num (s : ℝ → Prop) : ℝ :=
  Classical.epsilon (is_sup_real s)

noncomputable def sup_int (s : ℤ → Prop) : ℤ :=
  Classical.epsilon (is_sup_int s)

-/
