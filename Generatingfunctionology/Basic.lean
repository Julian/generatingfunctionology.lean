import Mathlib.RingTheory.PowerSeries.Derivative
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
abbrev shift : α⟦X⟧ := mk fun n ↦ coeff' (n + 1) φ

notation φ " /ₓ " => shift φ

/-- Unfold the definition of shift. -/
lemma shift_def : φ/ₓ = (mk fun n ↦ coeff' (n + 1) φ : α⟦X⟧) := rfl

/-- Shifting a power series is the same as the power series obtained by shifting the *series*. -/
lemma mk_shift_eq_mk_add {f : ℕ → α}  : (mk f)/ₓ = mk (fun n ↦ f (n + 1)) := by
  ext n; cases n <;> simp

/--
  If `φ = a₀ + a₁ * X + a₂ * X^2 + ⋯` then
     `φ/ₓ * X + a₀ = φ`.
-/
lemma shift_mul_X_add : φ/ₓ * X + (C' (constantCoeff' φ)) = φ := by
  ext n; cases n <;> simp

variable {φ φ'}

/-- Given `φ = a₀ + a₁ * X + a₂ * X^2 + ⋯`, if `φ' = φ/ₓ` then `φ' * X + a₀ = φ`. -/
lemma eq_mul_X_add_of_shift (h: φ/ₓ = φ') : φ = φ' * X + (C' (constantCoeff' φ)) := by
  rw [←h, shift_mul_X_add]

end PowerSeries

open PowerSeries

-- GENERALIZEME: Can this be Semiring?
variable [Ring α]

lemma shift_inv : φ/ₓ * X = φ - (C' (constantCoeff' φ)) := by
  ext n; cases n <;> simp

lemma shift_sub_const (k : α) : (φ - C' k)/ₓ = φ/ₓ := by
  ext n; cases n <;> simp

section invOneScaled

/--
  The power series for `(1 - a*X)⁻¹`.
  (It's equal to `1 + a * X + a^2 * X^2 + ...`)
-/
abbrev invOneScaled (a : α) : α⟦X⟧ := mk (a ^ ·)

abbrev extractInvOneScaled (x : α⟦X⟧) : α⟦X⟧ := invOneScaled <| -(coeff' 1 x)
namespace DivNotation
scoped notation a "/ ( " x " ) " => a * extractInvOneScaled x
end DivNotation

open DivNotation

lemma extractInvOne : (1 / (1 - X) : α⟦X⟧) = invOneScaled 1 := by simp [extractInvOneScaled]

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

section derivative

variable {R: Type*} [CommRing R]

lemma derivative_mk (f : R⟦X⟧) : d⁄dX R f = mk fun n ↦ coeff R (n + 1) f * (n + 1) := rfl

/--
  `X + 2X^2 + 3X ^ 3 + ⋯ = X * d⁄dX (1 + X + X^2 + ⋯)`
-/
lemma X_mul_deriv_mk_one : (mk (·) : R⟦X⟧) = X * d⁄dX R (mk 1) := by
  ext n; cases n <;> simp [derivative_mk]

-- GENERALIZEME: nth deriv
lemma invOneScaled_deriv : d⁄dX R (1 / (1 - X)) = (1 / (1 - X)) ^ 2 :=
  have := calc d⁄dX R (1 / (1 - X))
      = (mk (· + 1) : R⟦X⟧) := by simp [derivative_mk]
    _ = (mk (·) : R⟦X⟧) + (mk 1) := by ext; simp
    _ = (X : R⟦X⟧) * d⁄dX R (1 / (1 - X)) + (mk 1) := by ext n; cases n <;> simp [coeff_succ_X_mul, derivative_mk]

  by
    have : (d⁄dX R (1 / (1 - X))) - X * d⁄dX R (1 / (1 - X)) = 1 / (1 - X) := by
      rw [extractInvOne, eq_mkOne] at this ⊢
      exact (eq_sub_of_add_eq' this.symm).symm
    have h : (d⁄dX R (1 / (1 - X))) * (1 - X) = (1 / (1 - X)) := by
      have foo : (d⁄dX R) (1 * extractInvOneScaled (1 - X)) - X * (d⁄dX R) (1 * extractInvOneScaled (1 - X)) = 1 * (d⁄dX R) (1 * extractInvOneScaled (1 - X)) - X * (d⁄dX R) (1 * extractInvOneScaled (1 - X)) := by ring
      rwa [foo, ←mul_sub_right_distrib, mul_comm] at this
    have h' : d⁄dX R (1 / (1 - X)) * (1 - X) * 1 / (1 - X) = (1 / (1 - X)) * 1 / (1 - X) := congr($h * (1 / (1 - X)))
    have h'' : (1 / (1 - X) : R⟦X⟧) * 1 / (1 - X) = (1 / (1 - X)) ^ 2 := by rw [extractInvOne, eq_mkOne, pow_two]
    have h''' : (1 - X : R⟦X⟧) * (1 * extractInvOneScaled (1 - X)) = 1 := by
      have bla := invOneScaled_inv (1 : R)
      have bla' : C' 1 * X = (1 : R⟦X⟧) * X := rfl
      rwa [bla', one_mul] at bla
    rwa [h'', mul_assoc, h''', mul_one] at h'

end derivative

end invOneScaled

section natCast

variable {φ}

lemma natCast_eq_C {n : ℕ} : n • φ = C α n.cast * φ := by simp

-- FIXME: Just the above being `simp` doesn't seem to work :/
lemma two_eq_C : 2 * φ = C α 2 * φ := rfl

open DivNotation in
lemma invOneScaled_cast_inv (n : ℕ) : (1 - n • X : α⟦X⟧) * 1 / (1 - n • X) = 1 := by
  simpa using invOneScaled_inv_left (n : α)

end natCast

/-- Two series are equal if their power series are equal -/
-- TODO: @[ext] How do I control which ext lemma ext finds?
theorem ext_mk {a b : ℕ → α} (h : mk a = mk b) : a = b := funext <| by
  simpa using PowerSeries.ext_iff.mp h
