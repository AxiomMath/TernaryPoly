module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Derivative

@[expose] public section


/-! Actual directional weak derivatives decompose in the coordinate directions. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The literal weak derivative in any direction is the coordinate-direction linear combination. -/
theorem valuedWeakDerivative_coordinates (m : ℕ) (Ω : TopologicalSpace.Opens (Fin m → ℝ))
    (v : Fin m → ℝ) (T : ValuedWeak (V := V) Ω) :
    valuedWeakDerivative Ω v T =
      ∑ d : Fin m, v d • valuedWeakDerivative Ω (Pi.single d 1) T := by
  have hv : v = ∑ d : Fin m, v d • Pi.single d 1 := by ext d; simp [Pi.single_apply]
  change valuedWeakGradient Ω T v = ∑ d : Fin m, v d • valuedWeakGradient Ω T (Pi.single d 1)
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul]

end TernaryPoly.PolynomialFormWeakSmooth
