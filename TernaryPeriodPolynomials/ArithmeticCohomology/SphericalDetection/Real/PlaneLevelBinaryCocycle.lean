module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelForget
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryVanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RadicalPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def RealPlaneLevelMixedRegular {index : Type} [Fintype index] (degree : ℕ)
    (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) : Prop :=
  ∀ matrix : BinaryRealGL, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
    cuspidalTensorHilbertEmbedding cusp basis
      (cycle.val (SemidirectProduct.inr matrix,
        SemidirectProduct.inl (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))).val -
    cuspidalTensorHilbertEmbedding cusp basis
      (cycle.val (SemidirectProduct.inl (Multiplicative.ofAdd point), SemidirectProduct.inr matrix)).val)

theorem realPlaneLevelMixedCocycle_differentiable {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (regular : RealPlaneLevelMixedRegular degree cusp trivialCharacter basis cycle) (matrix : BinaryRealGL) (coordinate : Fin 2) :
    DifferentiableAt ℝ (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
        (realRadicalAxis coordinate parameter))) 0 := by
  have composed := (regular matrix).comp (realRadicalAxisCoordinates_contDiff coordinate)
  have smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
        (realRadicalAxis coordinate parameter))) := by
    convert composed using 1
    funext parameter
    let embedding : realPlaneCuspidalRep degree cusp trivialCharacter →ₗ[ℂ] (index → cusp.H) :=
      cuspidalTensorHilbertEmbedding cusp basis
    change embedding (realPlaneMixedCocycle degree cusp matrix _ _) = _
    rw [realPlaneMixedCocycle_apply, map_sub]
    rfl
  exact smooth.differentiable (by simp) 0

def realPlaneLevelBinaryCocycle {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree) := by
  subst character
  exact realPlaneBinaryCocycle degree cusp basis (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
