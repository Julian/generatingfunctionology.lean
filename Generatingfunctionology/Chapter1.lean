import Generatingfunctionology.Basic

open PowerSeries

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

-- A(x)
abbrev A : ℚ⟦X⟧ := mk α

/-
  `A.shift = 2 * A + (1 - X)⁻¹`
-/
theorem left_eq_right : A/ₓ = 2 * A + 1 / (1 - X) := by ext n; cases' n <;> simp

/-
  `A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹`
-/
theorem A_eq : A = X * 1 / (1 - X) * 1 / (1 - 2*X) := by
  have := shift.shift_inv left_eq_right
  simp [constantCoeff_mk, map_zero, add_zero, -two_eq_C] at this
  rw [← mul_comm, left_distrib, ←mul_assoc] at this
  have : A - X * 2 * A = X * invOneScaled 1 := sub_eq_of_eq_add' this.symm
  rw [mul_comm, ← mul_one A, mul_assoc, ← mul_assoc 1, ← mul_sub_left_distrib, one_mul] at this
  have : A * (1-X*2)*(invOneScaled 2) = X * invOneScaled 1 * (invOneScaled 2) := congrFun (congrArg HMul.hMul this) (invOneScaled 2)
  have inverse_works : (1 - 2*X : ℚ⟦X⟧) * (invOneScaled 2) = 1 := by
    have : (1-2*X : ℚ⟦X⟧)*(invOneScaled 2) = (1 - 2*X) * 1 / (1 - 2 * X) := by simp
    rw [this]
    exact invOneScaled_inv 2
  rw [mul_assoc, mul_comm X 2, inverse_works, mul_one] at this
  simpa

/- Rewrite A using partial fraction decomposition -/
theorem A.pfd : X * (2 / (1 - 2*X) - 1 / (1 - X)) = (X : ℚ⟦X⟧) * 1 / (1 - X) * 1 / (1 - 2*X) := by
  calc
    (X : ℚ⟦X⟧) * (2 / (1 - 2*X) - 1 / (1 - X)) = X * (2 / (1 - C' 2*X) * ((1 - C' 1 * X) * 1 / (1 - C' 1 * X)) - ((1 - C' 2 * X) * 1 / (1 - C' 2 *X)) * 1 / (1 - C' 1* X)) := by
      rw [invOneScaled_inv, invOneScaled_inv]
      simp
    _ = X * 1 / (1 - C' 1 * X) * 1 / (1 - C' 2*X) * (2 * 1 - 2 * C' 1 * X - 1 + C' 2 * X) := by ring
    _ = X * 1 / (1 - C' 1 * X) * 1 / (1 - C' 2*X) := by simp; ring
    _ = X * 1 / (1 - X) * 1 / (1 - 2*X) := by simp

/- Find the coefficients of the partial fraction decomposition version of A -/
theorem A.pfd_eq : (X * (2 / (1 - 2*X) - 1 / (1 - X)) : ℚ⟦X⟧) = mk fun n => 2^n - 1 := by
  ext n; cases' n with n <;> simp [pow_succ, pow_mul_comm']

theorem coeff_alpha : α = fun n => 2^n - 1 := 
  suffices A = (mk fun n => 2^n - 1) by
    ext n
    simpa using PowerSeries.ext_iff.mp this n
  by rw [←A.pfd_eq, A.pfd, ←A_eq]
