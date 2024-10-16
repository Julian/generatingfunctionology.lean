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

/--
  Given:

    `φ = a₀ + a₁ * X + a₂ * X^2 + ⋯`,

  we define:

    `φ.shift = a₁ + a₂ * X + a₃ * X^2 + ⋯`,

  i.e. it is the series obtained by "dividing" all terms by X,
  which we now will denote `φ/ₓ` via Lean notation.
-/
abbrev shift : PowerSeries α := mk fun n ↦ coeff' (n + 1) φ

notation φ " /ₓ " => shift φ

/--

  If `φ = a₀ + a₁ * X + a₂ * X^2 + ⋯` then
     `φ/ₓ * X + a₀ = φ`.
-/
lemma shift_mul_X_add : φ/ₓ * X + (C' (constantCoeff' φ)) = φ := by
  ext n; cases n <;> simp

variable {φ φ'}

/-- Given `φ = a₀ + a₁ * X + a₂ * X^2 + ⋯`, if `φ' = φ/ₓ` then `φ' * X + a₀ = φ`. -/
lemma shift_inv (h: φ/ₓ = φ') : φ = φ' * X + (C' (constantCoeff' φ)) := by rw [←h, shift_mul_X_add]

end PowerSeries

open PowerSeries

-- GENERALIZEME: Can this be Semiring?
variable [Ring α]

section invOneScaled

/--
  The power series for `(1 - a*X)⁻¹`.
  (It's equal to `1 + a * X + a^2 * X^2 + ...`)
-/
abbrev invOneScaled (a : α) : PowerSeries α := mk (a ^ ·)

abbrev extractInvOneScaled (x : α⟦X⟧) : α⟦X⟧ := invOneScaled <| -(coeff' 1 x)
notation a "/ ( " x " ) " => a * extractInvOneScaled x

section mkOneSpellings

lemma eq_mkOne : invOneScaled 1 = (mk 1 : α⟦X⟧) := by ext n; simp

lemma eq_invUnitsSubOne : invOneScaled 1 = (invUnitsSub 1 : α⟦X⟧) := by
  simp [invUnitsSub, invOneScaled, one_pow]

end mkOneSpellings

/-- The constant coefficient of `(1 - a*X)⁻¹` is 1. -/
theorem constCoeff_invOneScaled (a : α) : constantCoeff' (1 / (1 - C' a * X)) = 1 := by simp

/-- `(1 - a*X)⁻¹ * a*X = a*X + a^2*X^2 + a^3*X^3 + ...` -/
theorem mul_invOneScaled_scale_shifts (a : α) : 1 / (1 - C' a * X) * (C' a * X) = mk fun n => if n = 0 then 0 else a^n := by
  ext n; cases n <;> simp [← mul_assoc, pow_succ]

/--
  `a*X * (1 - a*X)⁻¹ = a*X + a^2*X^2 + a^3*X^3 + ...`
  (Need both sides since not assuming that `R` is a commutative ring)
-/
theorem mul_invOneScaled_scale_shifts' (a : α) : (C' a * X) * 1 / (1 - C' a * X) = mk fun n => if n = 0 then 0 else a^n := by
  ext n; cases n <;> simp [mul_assoc, pow_succ, pow_mul_comm']

/-- `(1 - a*X) * (1 - a*X)⁻¹ = 1` -/
theorem invOneScaled_inv (a : α) : (1 - C' a * X) * 1 / (1 - C' a * X) = 1 := by
  ext n
  cases n
  · simp
  · rw [sub_mul, mul_invOneScaled_scale_shifts']
    simp

/-- `(1 - a*X) * (1 - a*X)⁻¹ = 1` -/
theorem invOneScaled_inv_left (a : α) : (1 - C' a * X) * 1 / (1 - C' a * X) = 1 := by
  ext n
  cases n
  · simp
  · rw [mul_sub_right_distrib, mul_invOneScaled_scale_shifts']
    simp

/-- `(1 - a*X)⁻¹ * (1 - a*X) = 1` -/
theorem invOneScaled_inv_right (a : α) : 1 / (1 - C' a * X) * (1 - C' a * X) = 1 := by
  ext n
  cases n
  · simp
  · rw [mul_sub_left_distrib, mul_invOneScaled_scale_shifts]
    simp

end invOneScaled

section natCast

variable {φ}

lemma natCast_eq_C {n : ℕ} : n • φ = C α n.cast * φ := by simp

-- FIXME: Just the above being `simp` doesn't seem to work :/
lemma two_eq_C : 2 * φ = C α 2 * φ := rfl

lemma invOneScaled_cast_inv (n : ℕ) : (1 - n • X : α⟦X⟧) * 1 / (1 - n • X) = 1 := by
  simpa using invOneScaled_inv_left (n : α)

end natCast

/-- Two series are equal if their power series are equal -/
-- TODO: @[ext] How do I control which ext lemma ext finds?
theorem ext_mk {a b : ℕ → α} (h : mk a = mk b) : a = b := funext <| by
  simpa using PowerSeries.ext_iff.mp h
