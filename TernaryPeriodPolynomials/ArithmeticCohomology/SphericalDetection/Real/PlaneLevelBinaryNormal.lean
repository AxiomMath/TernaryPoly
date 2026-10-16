module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinarySectionCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLevelMixedValue_exists_binary_normal {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    ∃ potential : BinaryRealGL → cuspidalTensorValues cusp (HomogeneousPoly degree),
      ∀ (matrix : BinaryRealGL) (radical : RealPlaneRadical) (argument : BinaryAdelicGL),
        (cycle.val (SemidirectProduct.inr matrix,
            SemidirectProduct.inl (realRadicalInverseLevi matrix radical))).val.val argument -
          (cycle.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix)).val.val argument =
        realUpperBinaryValue degree radical
            ((realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular matrix).val argument) +
          ((realUpperRadicalRep degree).ρ radical ((potential matrix).val argument) -
            (potential matrix).val argument) := by
  subst character
  obtain ⟨potential, equality⟩ := realPlaneMixedCocycle_exists_binary_normal degree cusp basis cycle regular
  refine ⟨potential, ?_⟩
  intro matrix radical argument
  have value := congrArg (fun cocycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) =>
    (cocycle radical).val argument) (equality matrix)
  change (realPlaneMixedCocycle degree cusp matrix
      (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) radical).val argument =
    realUpperBinaryValue degree radical
        ((realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix).val argument) +
      ((realUpperRadicalRep degree).ρ radical ((potential matrix).val argument) -
        (potential matrix).val argument) at value
  rw [realPlaneMixedCocycle_apply] at value
  exact value

end TernaryPeriodPolynomials.SphericalDetection.Helpers
