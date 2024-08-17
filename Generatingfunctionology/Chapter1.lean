import Mathlib.RingTheory.PowerSeries.Inverse

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

abbrev F₁ : ℚ⟦X⟧ := 2 * (1 - X)⁻¹
abbrev F₂ : ℚ⟦X⟧ := 1 * (1 - X)⁻¹

lemma A_frac : X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ = X * (F₁ - F₂) := sorry

lemma α_eq (n : ℕ) : α n = 2 ^ n - 1 := sorry

#check A
