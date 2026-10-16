module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.IntegralNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerRadical
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section


/-!
# Two generators of the identity-plane stabilizer land in the identity-edge stabilizer

Step 3 of the three-step plan for the `InnerPlaneEdgeParabolic` input needs the identity-plane stabilizer
`flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3))` to meet the identity-edge
stabilizer `Σ₀ := fixedPointLevel rationalLevel standardBadEdge = rationalLevel ⊓ (planeParabolic ℚ
⊓ lineParabolic ℚ)` (`fixedPointLevel_standardBadEdge`) on the two generators used to build the
`T`-coboundary witness: every element of the radical lattice (fact A,
`identityPlaneRadicalInclusion_mem_edgeStabilizer`), and the Levi lift of `ModularGroup.T` (fact A′,
`identityPlaneLeviSection_T_mem_edgeStabilizer`).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.CuspidalSpan


/-- Fact A: every radical-lattice element's identity-plane inclusion lies in the identity-edge
stabilizer `Σ₀`. -/
theorem identityPlaneRadicalInclusion_mem_edgeStabilizer (element : RadicalLattice) :
    (identityPlaneRadicalInclusion element : RationalGL3) ∈
      fixedPointLevel rationalLevel standardBadEdge := by
  rw [fixedPointLevel_standardBadEdge]
  show planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ) ∈
    rationalLevel ⊓ (planeParabolic ℚ ⊓ lineParabolic ℚ)
  have integral_mem : planeUnipotent element.toAdd.1 element.toAdd.2 ∈ arithmeticLevel := by
    rw [arithmeticLevel_mem_iff]
    intro column
    fin_cases column <;> simp [planeUnipotent]
  have level_mem :
      planeUnipotent (element.toAdd.1 : ℚ) (element.toAdd.2 : ℚ) ∈ rationalLevel := by
    have mapped := rationalLevel_mem_of_integral _ integral_mem
    rwa [map_planeUnipotent] at mapped
  exact ⟨level_mem, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Fact A′: the Levi lift of `ModularGroup.T` lies in the identity-edge stabilizer `Σ₀`. -/
theorem identityPlaneLeviSection_T_mem_edgeStabilizer :
    (identityPlaneLeviSection (SpecialLinearGroup.toGL ModularGroup.T) : RationalGL3) ∈
      fixedPointLevel rationalLevel standardBadEdge := by
  rw [fixedPointLevel_standardBadEdge]
  show GeneralLinearGroup.map (Int.castRingHom ℚ)
      (planeLevi (SpecialLinearGroup.toGL ModularGroup.T) 1) ∈
    rationalLevel ⊓ (planeParabolic ℚ ⊓ lineParabolic ℚ)
  have integral_mem :
      planeLevi (SpecialLinearGroup.toGL ModularGroup.T) 1 ∈ arithmeticLevel := by
    rw [arithmeticLevel_mem_iff]
    intro column
    fin_cases column <;> simp [planeLevi, planeBlock]
  have line_mem :
      InLineParabolic (GeneralLinearGroup.map (Int.castRingHom ℚ)
        (planeLevi (SpecialLinearGroup.toGL ModularGroup.T) 1)) := by
    constructor <;>
      simp [GeneralLinearGroup.map_apply, planeLevi, planeBlock,
        SpecialLinearGroup.toGL, ModularGroup.T]
  exact ⟨rationalLevel_mem_of_integral _ integral_mem,
    inPlane_map _ _ (planeLevi_mem _ _), line_mem⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
