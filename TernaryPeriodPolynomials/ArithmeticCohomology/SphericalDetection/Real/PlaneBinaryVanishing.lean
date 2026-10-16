module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryArithmetic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PrimitiveFiniteLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneMixedCocycle_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (fixed : ∀ first second, cycle.val (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    realPlaneMixedCocycle degree cusp matrix cycle radical ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree) := by
  intro integral argument
  rw [realPlaneMixedCocycle_apply]
  exact congrArg₂ (fun first second : HomogeneousPoly degree => first - second)
    (fixed (SemidirectProduct.inr matrix) (SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) integral argument)
    (fixed (SemidirectProduct.inl radical) (SemidirectProduct.inr matrix) integral argument)

theorem realPlaneBinaryCochain_finiteLevel (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (fixed : ∀ first second, cycle.val (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (matrix : BinaryRealGL) :
    realPlaneBinaryCochain degree cusp cycle matrix ∈
      cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1)) := by
  intro integral argument
  apply Subtype.ext
  change ((realUpperCuspidalBinaryCoordinate degree cusp (realPlaneMixedCocycle degree cusp matrix cycle)).val _).val =
    ((realUpperCuspidalBinaryCoordinate degree cusp (realPlaneMixedCocycle degree cusp matrix cycle)).val _).val
  rw [realUpperCuspidalBinaryCoordinate_value, realUpperCuspidalBinaryCoordinate_value,
    realPlaneMixedCocycle_finiteLevel degree cusp cycle fixed matrix (realRadicalAxis 0 1) integral argument,
    realPlaneMixedCocycle_finiteLevel degree cusp cycle fixed matrix (realRadicalAxis 1 1) integral argument]

theorem realPlaneBinaryCocycle_zero_arithmetic {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (fixed : ∀ first second, cycle.val (first, second) ∈ cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree))
    (arithmetic : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (comparison : ∀ first second,
      (cycle.val (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1 = arithmetic.val (first, second))
    (zero : groupCohomology.H1π (binaryCuspidalRep cusp degree)
      (realPlaneBinaryCocycle degree cusp basis cycle regular) = 0) :
    groupCohomology.H2π (identityPlaneCoefficientRep degree) arithmetic.val = 0 := by
  obtain ⟨values, cuspidal, boundary⟩ :=
    (binaryCocycleToGroupCocycle_H1_zero_iff cusp _ _ _).mp zero
  let potential : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) :=
    ⟨values, (cuspidalTensorValues_binary_iff cusp degree values).mpr cuspidal⟩
  have primitive (matrix : BinaryRealGL) (argument : BinaryAdelicGL) :
      (realPlaneBinaryCochain degree cusp cycle matrix).val argument =
        binaryCohomologicalAction degree matrix potential.val argument - potential.val argument :=
    boundary matrix argument
  have finite : potential ∈ cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1)) :=
    binaryCuspidalPrimitive_finiteLevel degree cusp potential
      (fun matrix => (realPlaneBinaryCochain degree cusp cycle matrix).val) primitive
      (fun matrix => realPlaneBinaryCochain_finiteLevel degree cusp cycle fixed matrix)
  apply (identityPlaneRelativeH2_zero_iff_binaryPotential degree positive odd arithmetic).mpr
  refine ⟨potential.val 1, ?_⟩
  intro matrix
  rw [← realPlaneBinaryCochain_arithmetic degree cusp cycle arithmetic comparison,
    primitive, binaryCohomologicalAction_integralReal degree cusp potential finite]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
