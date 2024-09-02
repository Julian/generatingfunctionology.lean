import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

namespace PowerSeries

variable {α : Type*} [Semiring α] (φ φ' : PowerSeries α)

/- Same as normal but ring is implicit -/
abbrev coeff' := coeff α
abbrev C' := C α
abbrev constantCoeff' := constantCoeff α

/-
  Given `p = a_0 + a_1 * X + a_2 * X^2 + ...`,
  `p.shift = a_1 + a_2 * X + a_3 * X^2 + ...`
-/
abbrev shift : PowerSeries α := mk fun n ↦ coeff' (n + 1) φ

notation φ " /ₓ " => shift φ

namespace shift

/-
  If `p = a_0 + a_1 * X + a_2 * X^2 + ...`, then
  `p.shift * X + a_0 = p`
-/
lemma shift_mul_X_add : φ/ₓ * X + (C' (constantCoeff' φ)) = φ := by
  ext n; cases n <;> simp

variable {φ φ'}

/-
  Given `φ = a_0 + a_1 * X + a_2 * X^2 + ...`,
  if `φ.shift = φ'`, then
  `φ = φ' * X + a_0`
-/
lemma shift_inv (h: φ/ₓ = φ') : φ = φ' * X + (C' (constantCoeff' φ)) := by
  have := congrFun (congrArg HAdd.hAdd (congrFun (congrArg HMul.hMul h) X)) (C' (constantCoeff' φ))
  rwa [shift_mul_X_add] at this

end shift

end PowerSeries

open PowerSeries

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

-- A(x)
abbrev A : ℚ⟦X⟧ := mk α

section invOneScaled

universe u
variable {R : Type u} [Ring R]

/-
  The power series for `(1 - a*X)⁻¹`.
  (It's equal to `1 + a * X + a^2 * X^2 + ...`)
-/
abbrev invOneScaled (a : R) : PowerSeries R := mk fun n => a^n

/-
  The constant coefficient of `(1 - a*X)⁻¹` is 1
-/
@[simp]
theorem constCoeff_invOneScaled (a : R) : constantCoeff' (invOneScaled a) = 1 := by
  simp [constantCoeff', invOneScaled]

/-
  `(1 - a*X)⁻¹ * a*X = a*X + a^2*X^2 + a^3*X^3 + ...`
-/
theorem mul_invOneScaled_scale_shifts (a : R) : (invOneScaled a) * (C' a * X) = mk fun n => if n = 0 then 0 else a^n := by
  ext n
  cases' n
  <;> simp [← mul_assoc, pow_succ]

/-
  `a*X * (1 - a*X)⁻¹ = a*X + a^2*X^2 + a^3*X^3 + ...`
  (Need both sides since not assuming that `R` is a commutative ring)
-/
theorem mul_invOneScaled_scale_shifts' (a : R) : (C' a * X) * (invOneScaled a) = mk fun n => if n = 0 then 0 else a^n := by
  ext n
  cases' n
  <;> simp [mul_assoc, pow_succ, pow_mul_comm']

/-
  `(1 - a*X) * (1 - a*X)⁻¹ = 1`
-/
theorem invOneScaled_inv (a : R) : (1 - C' a * X) * invOneScaled a = 1 := by
  ext n
  cases' n
  · simp
  · rw [sub_mul 1 (C' a * X) (invOneScaled a), mul_invOneScaled_scale_shifts']
    simp

/-
  `(1 - a*X)⁻¹ * (1 - a*X) = 1`
-/
theorem invOneScaled_inv' (a : R) : (invOneScaled a) * (1 - C' a * X) = 1 := by
  ext n
  cases' n with n
  · simp
  · rw [mul_sub_left_distrib (invOneScaled a) 1 (C' a * X), mul_invOneScaled_scale_shifts]
    simp

end invOneScaled

/-
  `A.shift = 2 * A + (1 - X)⁻¹`
-/
theorem left_eq_right : A/ₓ = 2 * A + invUnitsSub 1 := by
  have : 2 * mk α = C' 2 * mk α := rfl
  ext n
  cases' n
  <;> simp [this]

/-
  `A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹`
-/
theorem recurrence : A = X * (invUnitsSub 1) * invOneScaled 2 := by
  have := shift.shift_inv left_eq_right
  simp only [constantCoeff_mk, map_zero, add_zero] at this
  rw [← mul_comm X (2 * A + invUnitsSub 1), left_distrib X (2*A) (invUnitsSub 1), ←mul_assoc] at this
  have : A - X * 2 * A = X * invUnitsSub 1 := sub_eq_of_eq_add' this
  rw [mul_comm (X * 2) A, ← mul_one A, mul_assoc, ← mul_assoc 1 X 2, ← mul_sub_left_distrib, one_mul] at this
  have : A * (1-X*2)*(invOneScaled 2) = X * invUnitsSub 1 * (invOneScaled 2) := congrFun (congrArg HMul.hMul this) (invOneScaled 2)
  have inverse_works : (1-2*X : ℚ⟦X⟧)*(invOneScaled 2) = 1 := invOneScaled_inv 2
  rw [mul_assoc, mul_comm X 2, inverse_works, mul_one] at this
  simpa [←mul_assoc]
