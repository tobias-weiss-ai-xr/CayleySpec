import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Complex
open scoped UpperHalfPlane

noncomputable section

namespace ModularForm

/-- The `q`-variable `exp(2πiτ)` for `τ` in the upper half-plane. -/
def q_variable (τ : ℍ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))

/-- A function `f : ℍ → ℂ` has a q-expansion if it can be written as a power series in `q`. -/
def has_q_expansion (f : ℍ → ℂ) : Prop :=
  ∃ a : ℕ → ℂ, ∀ τ : ℍ, HasSum (fun n => a n * (q_variable τ) ^ n) (f τ)

/-- `q_variable τ` tends to `0` as `Im(τ)` tends to `∞`. -/
theorem q_variable_is_zero_at_infinity :
    Filter.Tendsto q_variable (Filter.atTop.comap (UpperHalfPlane.im : ℍ → ℝ)) (nhds (0 : ℂ)) := by
  sorry

end ModularForm

end
