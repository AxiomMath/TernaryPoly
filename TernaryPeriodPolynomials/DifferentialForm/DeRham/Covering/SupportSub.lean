module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Support

@[expose] public section


/-! Exact quotient support control under subtraction of actual equivariant forms. -/
noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set SmoothLocalDeRham SymmetricSpaceCharts SymmetricSpaceCovering
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U : Set OrbitSpace} {n : ℕ}

theorem quotientSupport_sub (w z : EquivariantForm ρ U n) :
    quotientSupport (w-z) ⊆ quotientSupport w ∪ quotientSupport z := by
  rw [quotientSupport, quotientSupport, quotientSupport, ← closure_union, ← image_union]
  apply closure_mono
  apply image_mono
  exact Function.support_sub (w.val : RawForm Coordinates F n) (z.val : RawForm Coordinates F n)

end TernaryPoly.SmoothCoveringDeRham
