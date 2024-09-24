import Generatingfunctionology.Basic

open PowerSeries

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

-- A(x)
abbrev A : ℚ⟦X⟧ := mk α

/-
  `A/ₓ = 2 * A + (1 - X)⁻¹`
-/
theorem left_eq_right : A/ₓ = 2 • A + 1 / (1 - X) := by ext n; cases n <;> simp [two_eq_C]

/-
  `A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹`
-/
theorem A_eq : A = X * 1 / (1 - X) * 1 / (1 - 2 • X) :=
  have := sub_eq_of_eq_add' <| calc
    _ = (2 • A + 1 / (1 - X)) * X + C' (constantCoeff' A) := shift_inv left_eq_right |>.symm
    _ = (C' 2 * A + invOneScaled 1) * X := by simp [two_eq_C]
    _ = X * C' 2 * A + X * invOneScaled 1 := by ring
  by
    rw [mul_comm, ← mul_one A, mul_assoc, ← mul_assoc 1, ← mul_sub_left_distrib, one_mul] at this
    have := congrFun (congrArg HMul.hMul this) (invOneScaled 2)
    have inverse_works : (1 - 2*X : ℚ⟦X⟧) * invOneScaled 2 = 1 := by simpa using invOneScaled_cast_inv 2 (α := ℚ)
    simpa [mul_assoc, mul_comm X, ← two_eq_C, inverse_works]

/- Rewrite A using partial fraction decomposition -/
theorem A.pfd : (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X)) = X * 1 / (1 - X) * 1 / (1 - 2 • X) :=
  calc (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X))
      = X * (2 / (1 - C' 2*X) * ((1 - C' 1 * X) * 1 / (1 - C' 1 * X)) - ((1 - C' 2 * X) * 1 / (1 - C' 2 *X)) * 1 / (1 - C' 1* X)) := by
        rw [invOneScaled_inv, invOneScaled_inv]
        simp [two_eq_C]
    _ = X * 1 / (1 - C' 1 * X) * 1 / (1 - C' 2*X) * (2 * 1 - 2 * C' 1 * X - 1 + C' 2 * X) := by ring
    _ = X * 1 / (1 - X) * 1 / (1 - 2 • X) := by simp [two_eq_C]; ring

/- Find the coefficients of the partial fraction decomposition version of A -/
theorem A.pfd_eq : (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X)) = mk (2 ^ · - 1) := by
  ext n; cases n <;> simp [pow_succ, pow_mul_comm', two_eq_C]

theorem coeff_alpha : α = (2 ^ · - 1) := ext_mk <| A.pfd_eq ▸ A.pfd ▸ A_eq
