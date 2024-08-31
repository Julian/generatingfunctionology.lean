import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

open PowerSeries

namespace PowerSeries

variable {α : Type*} [Semiring α] (φ φ' : PowerSeries α)

def shift : PowerSeries α := PowerSeries.mk fun n ↦ coeff α (n + 1) φ

lemma shift_def : φ.shift = PowerSeries.mk fun n ↦ coeff α (n + 1) φ := rfl

namespace shift

@[simp]
lemma shift_mul_X_add : φ.shift * X + (C α (constantCoeff α φ)) = φ := by
  ext n; cases n <;> simp

variable {φ φ'}

lemma foo (h: φ.shift = φ') : φ = φ' * X + (C α (constantCoeff α φ)) := by
  have : φ.shift * X + (C α (constantCoeff α φ)) = φ' * X + (C α (constantCoeff α φ)) := by exact congrFun (congrArg HAdd.hAdd (congrFun (congrArg HMul.hMul h) X)) ((C α) ((constantCoeff α) φ))
  rw [shift_mul_X_add] at this
  assumption

end shift

#check X⁻¹

end PowerSeries

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

-- A(x)
abbrev A : ℚ⟦X⟧ := mk α

abbrev left : ℚ⟦X⟧ := mk fun n ↦ α (n + 1)
abbrev right : ℚ⟦X⟧ := mk fun n ↦ 2 * α n + 1

-- In the book, this is A / X -- but Mathlib does not define division by X; and it defines
-- X⁻¹ to be 0 (see `X_inv`).
-- So for now we get around thinking too hard by instead talking about X * LHS.
lemma left_eq : A.shift = mk (fun n ↦ α (n + 1)) := by simp [shift_def]

lemma right_eq : mk (2 * α · + 1) = 2 * A + invUnitsSub 1 := calc
  _ = mk (2 * α ·) + invUnitsSub 1 := by ext; simp
  _ = 2 * A + invUnitsSub 1 := by
    ext
    have : ↑2 = C ℚ 2 := rfl
    simp [this]

example : A.shift = 2 * A + invUnitsSub 1 → A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ := by
  intro h
  have := shift.foo h
  simp at this
  rw [this, A]
  have one_eq : mk 1 = invUnitsSub (1 : ℚˣ) := by ext; simp
  rw [← one_eq] at this
  have swap : X * (2 * A + mk 1) = (2 * A + mk 1) * X := by ring
  rw [←swap] at this
  have plzring : X * (2 * A + mk 1) = X * 2 * A + X * mk 1 := by ring
  have plzring' : A - X * 2 * A = X * mk 1 := by exact sub_eq_of_eq_add' this
  have plzring'' : A - X * 2 * A = A * (1 - 2 * X) := by ring
  rw [plzring, ←plzring', plzring''] at this

lemma A_eq : A = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ := sorry

abbrev A_frac : ℚ⟦X⟧ := X * ((2 * (1 - 2 * X)⁻¹) - (1 - X)⁻¹)

lemma A_eq_frac : A = A_frac := by
  symm
  rw [A_eq, A_frac]
  calc (X * (2 * (1 - 2 * X)⁻¹ - (1 - X)⁻¹) : ℚ⟦X⟧)
    _ = X * 2 * (1 - 2 * X)⁻¹ - X * (1 - X)⁻¹ := by ring
    _ = X * 2 * (1 - 2 * X)⁻¹ - X * (1 - X)⁻¹ := rfl
    _ = X * (1 - X)⁻¹ * (1 - 2 * X)⁻¹ := sorry

lemma α_eq (n : ℕ) : α n = 2 ^ n - 1 := by
  -- "Multiply the left side by x^n and sum", which in Mathlib is "form the power series with coeff⋯"
  have A_eq : mk (fun n ↦ α (n + 1)) = 2 * A + invUnitsSub 1 := right_eq

  have : X * mk (fun n ↦ α (n + 1)) = X * 2 * A + invUnitsSub 1 := by
    sorry
  rw [left_eq] at this

  have h' : mk (fun n ↦ 2 * (α n) + 1) = mk (fun n ↦ 2 * (α n)) + mk 1 := rfl
  have h'' : mk (fun n ↦ 2 * (α n)) = 2 * A := by
    have : ↑2 = C ℚ 2 := rfl
    ext n
    simp [coeff_mk, this, coeff_C_mul]
  have : mk 1 = invUnitsSub (1 : ℚˣ) := by ext; simp
  have h''' : mk (fun n ↦ 2 * (α n)) + mk 1 = 2 * A + invUnitsSub 1 := by rw [h'', this]

  sorry

#check A

#exit

example : mk (fun n ↦ α (n + 1)) = X⁻¹ * A := by
  rw [eq_shift_mul_X_add_const A]
  simp only [coeff_mk, constantCoeff_mk, map_zero, add_zero, zero_mul]
  rw [mul_comm _ X, ←mul_assoc]
  simp [left]

example : right = 2 * A + (1 - X)⁻¹ := by
  dsimp [right]
  ext n
  have : ↑2 = C ℚ 2 := rfl
  simp_all

@[simp]
lemma foo (n : ℚ) : (n : ℚ⟦X⟧) = C ℚ n := rfl
