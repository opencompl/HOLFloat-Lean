import Mathlib


-- Should I define it this way?
def npow : (@& ℚ) → (@& ℕ) → ℚ
  | _, 0 => 1
  | x, Nat.succ n => x ^ (Nat.succ n)
def ipow : (@& ℚ) → (@& ℤ) → ℚ
  | x, Int.ofNat n => npow x n
  | x, Int.negSucc n => Rat.inv (npow x n)

instance : HPow Rat Int Rat where
  hPow := ipow

theorem ipow_lt_zero {r : ℚ}{i : ℤ} : 0 < r → 0 < r ^ i := by
  sorry

theorem ipow_inv_neg {r : ℚ}{i : ℤ} : r ≠ 0 → r ^ i = Rat.inv (r ^(-i)) := by
  sorry

theorem ipow_add_exp {r : ℚ}(u : ℤ)(v : ℤ) : r ≠ 0 → r ^ u * r ^ v = r ^ (u + v) := by
sorry

/- 
theorem ipow_eq_exp
theorem ipow_eq_exp_p
-/

theorem ipow_between {x : ℚ}{y z i : ℤ} : 
  (0 < x) → (y * x ^ e ≤ z * x ^ e) → (z * x ^ e ≤ (y + 1) * x ^ e) 
  → (z = y) ∨ (z = y + 1):= by
  sorry
theorem ipow_to_one {r : ℚ} : r ^ 1 = r := by
  simp

theorem ipow_to_zero {r : ℚ} : r ^ 0 = 1 := by
  simp

theorem ipow_le_one {r : ℚ}{i : ℤ} : 1 ≤ r → 0 ≤ i → 1 ≤ r ^ i := by
  sorry

theorem ipow_lt_one {r : ℚ}{i : ℤ} : 1 < r → 0 < i → 1 < r ^ i := by
  sorry
theorem ipow_le_sum {r : ℚ}{n : ℚ} : 2 ≤ r → 0 ≤ i → ∃ e : ℤ , n ≤ r ^ e := by
  sorry

theorem ipow_le_rat {r : ℚ}{z : ℚ} : 2 ≤ r → ∃ e : ℤ , z ≤ r ^ e := by
  sorry
theorem ipow_le_rat_two {r : ℚ}{z : ℚ} : 0 < z → 2 ≤ r → ∃ e : ℤ , r ^ e ≤ z := by
  sorry
theorem ipow_monotone {r : ℚ}{u : ℤ}{v : ℤ} : 2 ≤ r → r ^ u ≤ r ^ v → u ≤ v := by
  sorry
theorem ipow_monotone_two {r : ℚ}{u : ℤ}{v : ℤ} : 1 ≤ r → u ≤ v → r ^ u ≤ r ^ v := by
  sorry
theorem ipow_mul_inv_eq_one {r : ℚ}{i : ℤ} : 0 < r → r ^ i * r ^ (-i) = 1 := by
  sorry

def rerror {a : ℚ}{b : ℚ} :=
  abs ((b - a)/ a)

def closer {x y z : ℚ} :=
  abs (x - z) < abs (y - z)
