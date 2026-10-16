module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinarySectionCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SemidirectMixedTwoCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realUpperToPlaneRadicalCocycle (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) →ₗ[ℂ]
      groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl (realPlaneCuspidalRep degree cusp trivialCharacter)) :=
  oneCocyclePullback _ _ (MonoidHom.id RealPlaneRadical) LinearMap.id (by
    intro radical
    apply LinearMap.ext
    intro values
    exact congrArg (fun linear => linear values) (realUpperCuspidalRep_inl degree cusp radical).symm)

def realPlaneBinarySectionFamily (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter)) (matrix : BinaryRealGL) :
    groupCohomology.cocycles₁ (Rep.res SemidirectProduct.inl (realPlaneCuspidalRep degree cusp trivialCharacter)) :=
  realUpperToPlaneRadicalCocycle degree cusp
    (realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp cycle matrix))

theorem realPlaneBinarySectionFamily_law {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (first second : BinaryRealGL) (radical : RealPlaneRadical) :
    realPlaneBinarySectionFamily degree cusp cycle (first * second) radical =
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inr first)
        (realPlaneBinarySectionFamily degree cusp cycle second (realPlaneRadicalAction first⁻¹ radical)) +
      realPlaneBinarySectionFamily degree cusp cycle first radical := by
  have equality := congrArg (fun cocycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) => cocycle radical)
    (realPlaneBinarySection_cocycle degree cusp basis cycle regular first second)
  exact equality

def realPlaneBinaryRelativeCycle {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0) :
    relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter) :=
  semidirectMixedRelativeCycle realPlaneRadicalAction (realPlaneCuspidalRep degree cusp trivialCharacter)
    (realPlaneBinarySectionFamily degree cusp cycle) (realPlaneBinarySectionFamily_law degree cusp basis cycle regular)

theorem realPlaneBinaryRelativeCycle_mixed {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (matrix : BinaryRealGL) :
    realPlaneMixedCocycle degree cusp matrix (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) =
      realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp cycle matrix) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [realPlaneMixedCocycle_apply]
  change (semidirectMixedRelativeCycle realPlaneRadicalAction (realPlaneCuspidalRep degree cusp trivialCharacter)
      (realPlaneBinarySectionFamily degree cusp cycle) (realPlaneBinarySectionFamily_law degree cusp basis cycle regular)).val
      (SemidirectProduct.inr matrix, SemidirectProduct.inl (realPlaneRadicalAction matrix⁻¹ radical)) -
    (semidirectMixedRelativeCycle realPlaneRadicalAction (realPlaneCuspidalRep degree cusp trivialCharacter)
      (realPlaneBinarySectionFamily degree cusp cycle) (realPlaneBinarySectionFamily_law degree cusp basis cycle regular)).val
      (SemidirectProduct.inl radical, SemidirectProduct.inr matrix) = _
  rw [semidirectMixedRelativeCycle_levi_radical, semidirectMixedRelativeCycle_radical_levi, sub_zero]
  rfl

theorem realPlaneBinaryRelativeCycle_binary {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (matrix : BinaryRealGL) :
    realPlaneBinaryCochain degree cusp (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) matrix =
      realPlaneBinaryCochain degree cusp cycle matrix := by
  rw [realPlaneBinaryCochain, realPlaneBinaryRelativeCycle_mixed, realUpperCuspidalBinarySection_coordinate]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
