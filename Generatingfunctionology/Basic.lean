import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

variable {α : Type*} (φ φ' : PowerSeries α)

namespace PowerSeries

variable [Semiring α]

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
lemma shift_inv (h: φ/ₓ = φ') : φ' * X + (C' (constantCoeff' φ)) = φ := by rw [←h, shift_mul_X_add]

end shift

end PowerSeries

open PowerSeries

variable [Ring α]

section invOneScaled

/-
  The power series for `(1 - a*X)⁻¹`.
  (It's equal to `1 + a * X + a^2 * X^2 + ...`)
-/
abbrev invOneScaled (a : α) : PowerSeries α := mk (a ^ ·)

abbrev extractInvOneScaled (x : α⟦X⟧) : α⟦X⟧ := invOneScaled <| -(coeff' 1 x)

@[simp]
lemma extractInv_def (x : α⟦X⟧) : extractInvOneScaled x = invOneScaled (-(coeff' 1 x)) := rfl

notation a "/ ( " x " ) " => a * extractInvOneScaled x

/-
  The constant coefficient of `(1 - a*X)⁻¹` is 1
-/
@[simp]
theorem constCoeff_invOneScaled (a : α) : constantCoeff' (1 / (1 - C' a * X)) = 1 := by simp

/-
  `(1 - a*X)⁻¹ * a*X = a*X + a^2*X^2 + a^3*X^3 + ...`
-/
theorem mul_invOneScaled_scale_shifts (a : α) : 1 / (1 - C' a * X) * (C' a * X) = mk fun n => if n = 0 then 0 else a^n := by
  ext n
  cases' n
  <;> simp [← mul_assoc, pow_succ]

/-
  `a*X * (1 - a*X)⁻¹ = a*X + a^2*X^2 + a^3*X^3 + ...`
  (Need both sides since not assuming that `R` is a commutative ring)
-/
theorem mul_invOneScaled_scale_shifts' (a : α) : (C' a * X) * 1 / (1 - C' a * X) = mk fun n => if n = 0 then 0 else a^n := by
  ext n
  cases' n
  <;> simp [mul_assoc, pow_succ, pow_mul_comm']

/-
  `(1 - a*X) * (1 - a*X)⁻¹ = 1`
-/
theorem invOneScaled_inv (a : α) : (1 - C' a * X) * 1 / (1 - C' a * X) = 1 := by
  ext n
  cases' n
  · simp
  · rw [sub_mul 1 (C' a * X) (1 / (1 - C' a * X)), mul_invOneScaled_scale_shifts']
    simp

/-
  `(1 - a*X) * (1 - a*X)⁻¹ = 1`
-/
theorem invOneScaled_inv_left (a : α) : (1 - C' a * X) * 1 / (1 - C' a * X) = 1 := by
  ext n
  cases' n with n
  · simp
  · rw [mul_sub_right_distrib 1 (C' a * X) (1 / (1 - C' a * X)), mul_invOneScaled_scale_shifts']
    simp

/-
  `(1 - a*X)⁻¹ * (1 - a*X) = 1`
-/
theorem invOneScaled_inv_right (a : α) : 1 / (1 - C' a * X) * (1 - C' a * X) = 1 := by
  ext n
  cases' n with n
  · simp
  · rw [mul_sub_left_distrib (1 / (1 - C' a * X)) 1 (C' a * X), mul_invOneScaled_scale_shifts]
    simp

end invOneScaled

section natCast

@[simp]
lemma natCast_eq_C {n : ℕ} : n.cast * φ = C α n.cast * φ := rfl

-- FIXME: Just the above being `simp` doesn't seem to work :/
@[simp]
lemma two_eq_C : 2 * φ = C α 2 * φ := rfl

lemma invOneScaled_cast_inv (n : ℕ) : (1 - n.cast * X : α⟦X⟧) * 1 / (1 - n.cast * X) = 1 := by
  simpa using invOneScaled_inv_left (n.cast : α)

end natCast

section invUnitsSub

theorem invUnitsSub_eq_mkOne.{u} {R : Type u} [Ring R] : invUnitsSub 1 = (mk 1 : R⟦X⟧) := by
  ext n; cases n <;> simp

@[simp]
theorem invUnitSubOne_eq_invOneScaledOne : (invUnitsSub 1 : α⟦X⟧) = invOneScaled 1 := by
  simp [invUnitsSub, invOneScaled, one_pow]

end invUnitsSub
