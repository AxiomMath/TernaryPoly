module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBoundaryPotentialRegular

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperBoundaryPotential_zero (degree : ℕ) (cusp : CuspidalRepresentation) :
    realUpperBoundaryPotential degree cusp 0 = 0 := by
  change cuspidalTensorMap cusp _ 0 + cuspidalTensorMap cusp _ 0 = 0
  rw [map_zero, map_zero, add_zero]

def realUpperBinaryCorrection (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) :
    cuspidalTensorValues cusp (HomogeneousPoly degree) :=
  realUpperBoundaryPotential degree cusp
    (cycle - realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle))

theorem realUpperBinaryCorrection_zero (degree : ℕ) (cusp : CuspidalRepresentation) :
    realUpperBinaryCorrection degree cusp 0 = 0 := by
  rw [realUpperBinaryCorrection, map_zero, map_zero, sub_zero, realUpperBoundaryPotential_zero]

theorem realUpperBinaryCorrection_normal {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (regular : ∀ coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis (cycle (realRadicalAxis coordinate parameter))) 0) :
    cycle = realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle) +
      oneBoundaryCycle (realUpperCuspidalRep degree cusp) (realUpperBinaryCorrection degree cusp cycle) := by
  obtain ⟨potential, normal⟩ := realUpperCuspidalCocycle_exists_binary_normal degree cusp basis cycle regular
  have zero : groupCohomology.H1π (realUpperCuspidalRep degree cusp)
      (cycle - realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle)) = 0 := by
    have equality := congrArg (groupCohomology.H1π (realUpperCuspidalRep degree cusp)) normal
    rw [map_add, oneBoundaryCycle_H1_zero, add_zero] at equality
    rw [map_sub, equality, sub_self]
  have boundary := realUpperBoundaryPotential_of_H1_zero degree cusp basis _ zero
  change oneBoundaryCycle (realUpperCuspidalRep degree cusp) (realUpperBinaryCorrection degree cusp cycle) =
    cycle - realUpperCuspidalBinarySection degree cusp (realUpperCuspidalBinaryCoordinate degree cusp cycle) at boundary
  rw [boundary]
  abel

theorem realUpperCuspidalBinarySection_finiteLevel
    (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1)))
    (radical : RealPlaneRadical) :
    realUpperCuspidalBinarySection degree cusp values radical ∈
      cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) :=
  cuspidalTensorMap_finiteLevel cusp (realUpperBinaryValue degree radical) values fixed

theorem realUpperBinaryCorrection_finiteLevel
    (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (first : cycle (radicalLatticeReal radicalLatticeFirst) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (second : cycle (radicalLatticeReal radicalLatticeSecond) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (binary_fixed : realUpperCuspidalBinaryCoordinate degree cusp cycle ∈
      cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1))) :
    realUpperBinaryCorrection degree cusp cycle ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  apply realUpperBoundaryPotential_finiteLevel
  · intro matrix argument
    exact congrArg₂ (fun first second : HomogeneousPoly degree => first - second) (first matrix argument)
      (realUpperCuspidalBinarySection_finiteLevel degree cusp _ binary_fixed
        (radicalLatticeReal radicalLatticeFirst) matrix argument)
  · intro matrix argument
    exact congrArg₂ (fun first second : HomogeneousPoly degree => first - second) (second matrix argument)
      (realUpperCuspidalBinarySection_finiteLevel degree cusp _ binary_fixed
        (radicalLatticeReal radicalLatticeSecond) matrix argument)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
