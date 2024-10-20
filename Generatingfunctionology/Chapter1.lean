import Generatingfunctionology.Basic

open scoped DivNotation
open PowerSeries

namespace «1.2»

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

/-- A(x) -/
abbrev A : ℚ⟦X⟧ := mk α

/--
  `A/ₓ = 2 * A + (1 - X)⁻¹`
-/
theorem left_eq_right : A/ₓ = 2 • A + 1 / (1 - X) := by ext n; cases n <;> simp [two_eq_C]

/--
  `A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹`
-/
theorem A_eq : A = X * 1 / (1 - X) * 1 / (1 - 2 • X) :=
  have := sub_eq_of_eq_add' <| calc
    _ = (2 • A + 1 / (1 - X)) * X + C' (constantCoeff' A) := eq_mul_X_add_of_shift left_eq_right
    _ = (C' 2 * A + invOneScaled 1) * X := by simp [extractInvOneScaled, two_eq_C]
    _ = X * C' 2 * A + X * invOneScaled 1 := by ring
  by
    rw [mul_comm, ← mul_one A, mul_assoc, ← mul_assoc 1, ← mul_sub_left_distrib, one_mul] at this
    have := congr($this * invOneScaled 2)
    have inverse_works : (1 - 2*X : ℚ⟦X⟧) * invOneScaled 2 = 1 := by simpa [extractInvOneScaled] using invOneScaled_cast_inv 2 (α := ℚ)
    simpa [mul_assoc, mul_comm X, extractInvOneScaled, ← two_eq_C, inverse_works]

/-- Rewrite A using partial fraction decomposition -/
theorem A.pfd : (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X)) = X * 1 / (1 - X) * 1 / (1 - 2 • X) :=
  calc (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X))
      = X * (2 / (1 - C' 2*X) * ((1 - C' 1 * X) * 1 / (1 - C' 1 * X)) - ((1 - C' 2 * X) * 1 / (1 - C' 2 *X)) * 1 / (1 - C' 1* X)) := by
        rw [invOneScaled_inv, invOneScaled_inv]
        simp [two_eq_C]
    _ = X * 1 / (1 - C' 1 * X) * 1 / (1 - C' 2*X) * (2 * 1 - 2 * C' 1 * X - 1 + C' 2 * X) := by ring
    _ = X * 1 / (1 - X) * 1 / (1 - 2 • X) := by simp [two_eq_C]; ring

/-- Find the coefficients of the partial fraction decomposition version of A -/
theorem A.pfd_eq : (X : ℚ⟦X⟧) * (2 / (1 - 2 • X) - 1 / (1 - X)) = mk (2 ^ · - 1) := by
  ext n; cases n <;> simp [pow_succ, pow_mul_comm', two_eq_C]

theorem coeff_alpha : α = (2 ^ · - 1) := ext_mk <| A.pfd_eq ▸ A.pfd ▸ A_eq

end «1.2»

namespace «1.3»

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + n
| 0 => 1

/-- A(x) -/
abbrev A : ℚ⟦X⟧ := mk α


/--
  `(A - 1)/ₓ = 2 • A + X * d⁄dX (1 - X)⁻¹`
-/
theorem left_eq_right : (A - 1)/ₓ = 2 • A + X * (1 / (1 - X)) ^ 2 := by
  calc (A - 1)/ₓ
    _ = (A - C' (constantCoeff' A))/ₓ := rfl
    _ = mk fun n ↦ 2 • (α n) + n := by simp_rw [shift_sub_const, mk_shift_eq_mk_add, nsmul_eq_mul, Nat.cast_ofNat]
    _ = (mk fun n ↦ 2 • (α n)) + (mk (·) : ℚ⟦X⟧) := rfl
    _ = 2 • A + (mk (·) : ℚ⟦X⟧) := by ext n; cases n <;> simp [two_eq_C]  -- GENERALIZEME...
    _ = 2 • A + X * d⁄dX ℚ (mk 1) := by rw [X_mul_deriv_mk_one]
    _ = 2 • A + X * (1 / (1 - X)) ^ 2 := by rw [←invOneScaled_deriv, ←eq_mkOne, extractInvOne]

theorem A_eq : A = (1 - 2 • X + 2 • X ^ 2 : ℚ⟦X⟧) * (1 / (1 - X) ^ 2) * (1 / (1 - 2 • X)) := by
  have : (A - C' (constantCoeff' A)) /ₓ = 2 • A + X * (1 * extractInvOneScaled (1 - X)) ^ 2 := left_eq_right
  rw [sub_eq_iff_eq_add.mp <| eq_mul_X_add_of_shift this, extractInvOne, one_mul]
  sorry

theorem A.pfd :
  (1 - 2 • X + 2 • X ^ 2 : ℚ⟦X⟧) * (1 / (1 - X) ^ 2) * (1 / (1 - 2 • X)) =
  ((-1) / (1 - X) ^ 2 : ℚ⟦X⟧) + (2  / (1 - 2 • X) : ℚ⟦X⟧) :=
  sorry

/-- Find the coefficients of the partial fraction decomposition version of A -/
theorem A.pfd_eq :
  ((-1) / (1 - X) ^ 2 : ℚ⟦X⟧) + (2  / (1 - 2 • X) : ℚ⟦X⟧) =
    mk (fun n ↦ 2 ^ (n + 1) - n - 1 : ℕ → ℚ) := by
  ext n; cases n <;> sorry

theorem coeff_alpha : α = (fun n ↦ 2 ^ (n + 1) - n - 1 : ℕ → ℚ) := ext_mk <| A.pfd_eq ▸ A.pfd ▸ A_eq

end «1.3»
