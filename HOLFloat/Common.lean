import Mathlib

import Lean
import Aesop
--set_option pp.all true

structure format where
  r : ℤ
  p : ℤ
  e : ℤ

@[aesop unsafe]
def pow_int(r : ℤ) (i : ℤ): ℚ :=
  (r : ℚ) ^ i

@[aesop unsafe]
def real_mul (r : ℝ) (i :ℤ) : ℝ :=
  r * (i : ℝ)

noncomputable instance : HMul ℝ ℤ ℝ where
  hMul := real_mul

instance : HPow ℤ ℤ ℚ where
  hPow := pow_int
@[aesop unsafe]
theorem ipow_lt_zero {r : ℝ}{i : ℤ} : 0 < r → 0 < r ^ i := by
  intro h
  cases i with 
  | ofNat n  =>
    -- HACK: aesop
      simp_all only [Int.ofNat_eq_coe, zpow_coe_nat, gt_iff_lt, pow_pos]
  | negSucc n =>
    -- HACK: aesop
      simp_all only [zpow_negSucc, inv_pos, gt_iff_lt, pow_pos]
@[simp]
theorem ipow_inv {r : ℝ}{i : ℕ} : r ^ Int.negOfNat i = Inv.inv (r ^ i) := by
  induction i
  case zero => simp; trivial
  case succ => constructor

@[simp]
theorem ipow_neg_succ {r : ℝ}{i : ℕ} : r ^ Int.negSucc i = Inv.inv (r ^ (Nat.succ i)):= by
  simp_all only [zpow_negSucc]
  
@[simp]
theorem ipow_inv_neg {r : ℝ}{i : ℤ} : r ≠ 0 → r ^ i = Inv.inv (r ^(-i)) := by
  cases i with
  | ofNat n =>
      -- HACK: aesop
      intros
      simp_all only [ne_eq, Int.ofNat_eq_coe, zpow_coe_nat, zpow_neg, inv_inv]
  | negSucc n =>
      -- HACK: aesop
      intros
      simp_all only [ne_eq, zpow_negSucc, zpow_neg, inv_inv]
@[simp]
theorem ipow_add_exp {r : ℝ} (u : ℤ) (v : ℤ) : r ≠ 0 → r ^ u * r ^ v = r ^ (u + v) := by
  sorry


/- 
theorem ipow_eq_exp
theorem ipow_eq_exp_p
-/
/-
@[simp]
theorem ipow_between {x : ℝ}{y z i : ℤ} : 
  (0 < x) → (y * x ^ e ≤ z * x ^ e) → (z * x ^ e ≤ (y + 1) * x ^ e) 
  → (z = y) ∨ (z = y + 1):= by
    sorry
-/
@[simp]
theorem ipow_to_one {r : ℝ} : r ^ 1 = r := by
  simp

@[simp]
theorem ipow_to_zero {r : ℝ} : r ^ 0 = 1 := by
  simp

@[simp]
theorem ipow_le_one {r : ℝ}{i : ℤ} : 1 ≤ r → 0 ≤ i → 1 ≤ r ^ i := by
  sorry
  

@[simp]
theorem ipow_lt_one {r : ℝ}{i : ℤ} : 1 < r → 0 < i → 1 < r ^ i := by
  sorry

@[simp]
theorem ipow_le_sum {r : ℝ}{n : ℝ} : 2 ≤ r → 0 ≤ i → ∃(e : ℤ), n ≤ r ^ e := by
  sorry

@[simp]
theorem ipow_le_real {r : ℝ}{z : ℝ} : 2 ≤ r → ∃ (e : ℤ) , z ≤ r ^ e := by
  --TODO: finding the bound using log is impossible because log isn't defined yet in mathlib4 for real numbers
  sorry

@[simp]
theorem ipow_le_real_two {r : ℝ}{z : ℝ} : 0 < z → 2 ≤ r → ∃ e : ℤ , r ^ e ≤ z := by
  sorry

@[simp]
theorem ipow_monotone {r : ℝ}{u : ℤ}{v : ℤ} : 1 ≤ r → u ≤ v → r ^ u ≤ r ^ v := by
  sorry

@[simp]
theorem ipow_monotone_two {r : ℝ}{u : ℤ}{v : ℤ} : 2 ≤ r → r ^ u ≤ r ^ v → u ≤ v := by
  sorry


@[simp]
theorem ipow_mul_inv_eq_one {r : ℝ}{i : ℤ} : 0 < r → r ^ i * r ^ (-i) = 1 := by
  sorry

noncomputable def rerror (a : ℝ)(b : ℝ): ℝ :=
  |((b - a) / a)|

def closer (x y z : ℝ): Prop :=
  abs (x - z) < abs (y - z)

open Int
@[simp]
theorem Int.one_lt_zero_lt (i : ℤ) : 1 < i → 0 < i := by
  intro h
  have hz : (0: ℤ) < 1 := by simp
  apply lt_trans hz h
@[simp]
theorem Int.one_lt_zero_le_iff (i : ℤ) (j : ℤ) : j < i ↔ j + 1 ≤ i := by
  apply Iff.intro
  · intro a
    exact a
  · intro a
    exact a
@[simp]
theorem Int.one_lt_ne_one {a : ℤ}(h : 1 < a):a ≠ 1 := by
  intro a_1
  simp_all only [one_lt_zero_le_iff, ne_eq]


-- sup inf definitions
--
@[aesop unsafe]
def is_sup_int (s : Int → Prop)(e : Int): Prop :=
  IsLUB s e
@[aesop unsafe]
def is_sup_real ( s : ℝ → Prop)(r : ℝ) : Prop :=
  IsGLB s r

open Classical

@[aesop unsafe]
noncomputable def sup_num (s : ℝ → Prop) : ℝ :=
  Classical.epsilon (is_sup_real s)

@[aesop unsafe]
noncomputable def sup_int (s : ℤ → Prop) : ℤ :=
  Classical.epsilon (is_sup_int s)
