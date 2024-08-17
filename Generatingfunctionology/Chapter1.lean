import Mathlib.RingTheory.PowerSeries.Basic

open PowerSeries

variable {R : Type*}
#check R⟦X⟧

abbrev α : ℕ → ℚ
| n + 1 => 2 * (α n) + 1
| 0 => 0

def A : ℚ⟦X⟧ := mk (α ·)

example : A = A := by
  rfl

#check A
