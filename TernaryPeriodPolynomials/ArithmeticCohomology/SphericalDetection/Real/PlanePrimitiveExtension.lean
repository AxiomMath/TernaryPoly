module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelRadicalCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlanePrimitiveExtension (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) : RealPlaneGroup → representation :=
  fun element => primitive element.left

theorem realPlanePrimitiveExtension_radical (representation : Rep ℂ RealPlaneGroup)
    (primitive : RealPlaneRadical → representation) (radical : RealPlaneRadical) :
    realPlanePrimitiveExtension representation primitive (SemidirectProduct.inl radical) = primitive radical := rfl

def realPlaneRelativeCycle (representation : Rep ℂ RealPlaneGroup)
    (cycle : groupCohomology.cocycles₂ representation) (primitive : RealPlaneRadical → representation)
    (boundary : ∀ first second,
      representation.ρ (SemidirectProduct.inl first) (primitive second) - primitive (first * second) + primitive first =
        cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)) :
    relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl representation :=
  ⟨cycle - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive), by
    intro first second
    change cycle (SemidirectProduct.inl first, SemidirectProduct.inl second) -
      twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive)
        (SemidirectProduct.inl first, SemidirectProduct.inl second) = 0
    rw [twoBoundaryCycle_apply, ← map_mul]
    simp only [realPlanePrimitiveExtension_radical, boundary, sub_self]⟩

theorem realPlaneRelativeCycle_H2 (representation : Rep ℂ RealPlaneGroup)
    (cycle : groupCohomology.cocycles₂ representation) (primitive : RealPlaneRadical → representation)
    (boundary : ∀ first second,
      representation.ρ (SemidirectProduct.inl first) (primitive second) - primitive (first * second) + primitive first =
        cycle (SemidirectProduct.inl first, SemidirectProduct.inl second)) :
    groupCohomology.H2π representation (realPlaneRelativeCycle representation cycle primitive boundary).val =
      groupCohomology.H2π representation cycle := by
  change groupCohomology.H2π representation
    (cycle - twoBoundaryCycle representation (realPlanePrimitiveExtension representation primitive)) = _
  rw [map_sub, twoBoundaryCycle_H2_zero, sub_zero]

theorem realPlaneLevelCuspidalRep_radical_of_trivial (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter) (radical : RealPlaneRadical)
    (values : realPlaneLevelCuspidalRep degree cusp character) :
    ((realPlaneLevelCuspidalRep degree cusp character).ρ (SemidirectProduct.inl radical) values).val =
      cuspidalTensorMap (V := HomogeneousPoly degree) (W := HomogeneousPoly degree) cusp
        ((realUpperRadicalRep degree).ρ radical) values.val := by
  subst character
  exact realPlaneCuspidalRep_radical degree cusp radical values.val

end TernaryPeriodPolynomials.SphericalDetection.Helpers
