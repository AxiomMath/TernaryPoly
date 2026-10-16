module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorAnalyticMaps
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def upperRadicalBinaryContribution (degree : ℕ) (coordinate : Fin 2) :
    HomogeneousPoly degree →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (planeRadicalCoordinate degree).comp (LinearMap.single ℂ (fun _ : Fin 2 => HomogeneousPoly degree) coordinate)

theorem realUpperCuspidalBinaryCoordinate_contributions (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) :
    realUpperCuspidalBinaryCoordinate degree cusp cycle =
      cuspidalTensorMap cusp (upperRadicalBinaryContribution degree 0) (cycle (realRadicalAxis 0 1)) +
        cuspidalTensorMap cusp (upperRadicalBinaryContribution degree 1) (cycle (realRadicalAxis 1 1)) := by
  apply Subtype.ext
  funext argument
  apply Subtype.ext
  rw [realUpperCuspidalBinaryCoordinate_value]
  simp [cuspidalTensorMap, upperRadicalBinaryContribution, planeRadicalCoordinate, smul_add]

theorem realPlaneBinaryCochain_hilbert_analyticAt_one {index binaryIndex : Type} [Fintype index] [Fintype binaryIndex]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (binaryBasis : Module.Basis binaryIndex ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (analytic : ∀ coordinate : Fin 2, AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp (invertibleMatrix matrix) cycle (realRadicalAxis coordinate 1))) 1) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix => cuspidalTensorHilbertEmbedding cusp binaryBasis
      (realPlaneBinaryCochain degree cusp cycle (invertibleMatrix matrix))) 1 := by
  have contribution (coordinate : Fin 2) := cuspidalTensorMap_hilbert_analyticAt cusp basis binaryBasis
    (upperRadicalBinaryContribution degree coordinate)
    (fun matrix : BinaryRealMatrix => realPlaneMixedCocycle degree cusp (invertibleMatrix matrix) cycle (realRadicalAxis coordinate 1)) 1
    (analytic coordinate)
  convert (contribution 0).add (contribution 1) using 1
  funext matrix
  unfold realPlaneBinaryCochain
  rw [realUpperCuspidalBinaryCoordinate_contributions, map_add]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
