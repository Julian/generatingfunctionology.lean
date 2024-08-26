import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Group.Defs

noncomputable section

open PowerSeries

variable {R : Type*}
#check R⟦X⟧

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

-- A(x)
def A : ℚ⟦X⟧ := mk α

lemma A_eq : A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ := sorry

abbrev F₁ : ℚ⟦X⟧ := 2 * (1 - 2 * X)⁻¹
abbrev F₂ : ℚ⟦X⟧ := 1 * (1 - X)⁻¹

#check X
#check (X : ℚ⟦X⟧)
#check F₁
#check A

lemma cancel_left (Y Z : ℚ⟦X⟧) : Y = Z → X * Y = X * Z := by
  intro h
  exact congrArg (HMul.hMul X) h

lemma A_frac : X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ = X * (F₁ - F₂) := by
  rw [F₁, F₂, mul_assoc]
  apply cancel_left
  sorry
  -- todo: partial fraction expansion

example {x y z : ℚ} (h : x ≠ 0) : x * y = x * z → y = z := by sorry

set_option diagnostics true
#synth IsLeftCancelMul ℚ

lemma A_algebraic_easy {x : ℚ} : 1 = 2 * (1 - x) + (-1) * (1 - 2 * x) := by ring

#print mul_left_cancel_iff

lemma add_left {z y : ℚ} (x : ℚ) : y = z → x * y = x * z := by exact fun a ↦ congrArg (HMul.hMul x) a

lemma A_algebraic {x : ℚ} (h₁ : x ≠ 1) (h₂ : x ≠ 1/2) : (1 - x)⁻¹ * (1 - 2 * x)⁻¹ = (2 * (1 - 2 * x)⁻¹ - 1 * (1 - x)⁻¹) := by
  -- 1. multiply both sides by (1 - x)
  let a : ℚ := (1 - x)
  have : (1 - x) * (1 - x)⁻¹ * (1 - 2 * x)⁻¹ = (1 - x) * (2 * (1 - 2 * x)⁻¹ - 1 * (1 - x)⁻¹)
    → (1 - x)⁻¹ * (1 - 2 * x)⁻¹ = (2 * (1 - 2 * x)⁻¹ - 1 * (1 - x)⁻¹) := by sorry
  apply add_left a
  rw [← mul_left_cancel_iff]
  -- 2. multiply both sides by (1 - 2 * x)
  -- exactly A_algebraic_easy
  sorry


lemma α_eq (n : ℕ) : α n = 2 ^ n - 1 := sorry

#check A
