import Mathlib

def power (r : ℝ) (i : ℕ): ℝ :=
  r ^ i
noncomputable def ipow : (@& ℝ) → (@& ℤ) → ℝ
  | x, Int.ofNat n => x ^ n
  | x, Int.negSucc n =>  Inv.inv (x ^ n)

noncomputable instance : HPow ℝ Int ℝ where
  hPow := ipow

theorem ipow_lt_zero {r : ℝ}{i : ℤ} : 0 < r → 0 < r ^ i := by
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

noncomputable def rerror {a : ℝ}{b : ℝ}: ℝ :=
  abs ((b - a) / a)

def closer (x y z : ℝ): Prop :=
  abs (x - z) < abs (y - z)
