module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryRelativeCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneInvariantCentral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {index : Type} [Fintype index]

theorem realPlaneBinaryRelativeCycle_edge
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0) :
    splitCocycleEdge realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter)
        (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) =
      splitCocycleEdge realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) cycle := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  change groupCohomology.H1π
      (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneCuspidalRep degree cusp trivialCharacter))
      (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix
        (realPlaneBinaryRelativeCycle degree cusp basis cycle regular)) =
    groupCohomology.H1π
      (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneCuspidalRep degree cusp trivialCharacter))
      (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix cycle)
  obtain ⟨potential, normal⟩ := realUpperCuspidalCocycle_exists_binary_normal degree cusp basis
    (realPlaneMixedCocycle degree cusp matrix cycle) (regular matrix)
  change cuspidalTensorValues cusp (HomogeneousPoly degree) at potential
  have equality : splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix cycle =
      splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix
          (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) +
        oneBoundaryCycle (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
          (realPlaneCuspidalRep degree cusp trivialCharacter)) potential := by
    apply groupCohomology.cocycles₁_ext
    intro radical
    have boundary_value : oneBoundaryCycle
        (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
          (realPlaneCuspidalRep degree cusp trivialCharacter)) potential radical =
        oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential radical :=
      congrArg (fun linear : Module.End ℂ (cuspidalTensorValues cusp (HomogeneousPoly degree)) =>
        linear potential - potential) (realUpperCuspidalRep_inl degree cusp radical).symm
    have section_value := congrArg (fun cocycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) =>
      cocycle radical) (realPlaneBinaryRelativeCycle_mixed degree cusp basis cycle regular matrix)
    have value := congrArg (fun cocycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) =>
      cocycle radical) normal
    apply Subtype.ext
    funext argument
    have section_evaluation := congrArg (fun values : cuspidalTensorValues cusp (HomogeneousPoly degree) =>
      values.val argument) section_value
    have boundary_evaluation := congrArg (fun values : cuspidalTensorValues cusp (HomogeneousPoly degree) =>
      values.val argument) boundary_value
    change (realPlaneMixedCocycle degree cusp matrix cycle radical).val argument =
      (realPlaneMixedCocycle degree cusp matrix (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) radical).val argument +
        (oneBoundaryCycle (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
          (realPlaneCuspidalRep degree cusp trivialCharacter)) potential radical).val argument
    rw [section_evaluation, boundary_evaluation]
    exact congrArg (fun values : cuspidalTensorValues cusp (HomogeneousPoly degree) => values.val argument) value
  have boundary_zero := oneBoundaryCycle_H1_zero
    (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter)) potential
  rw [equality, map_add, boundary_zero, add_zero]

theorem realPlaneBinaryRelativeCycle_H2
    (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0) :
    groupCohomology.H2π (realPlaneCuspidalRep degree cusp trivialCharacter)
        (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val =
      groupCohomology.H2π (realPlaneCuspidalRep degree cusp trivialCharacter) cycle.val := by
  have equality : relativeTwoCocycleClass (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter)
      (realPlaneBinaryRelativeCycle degree cusp basis cycle regular) =
    relativeTwoCocycleClass (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter) cycle := by
    apply realPlaneCohomologyEdge_injective degree cusp central_positive
    rw [splitCohomologyEdge_apply, splitCohomologyEdge_apply,
      realPlaneBinaryRelativeCycle_edge degree cusp basis cycle regular]
  exact congrArg Subtype.val equality

theorem realPlaneBinaryRelativeCycle_exists_primitive
    (degree : ℕ) (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0) :
    ∃ primitive : RealPlaneGroup → realPlaneCuspidalRep degree cusp trivialCharacter,
      cycle.val = (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val +
        twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter) primitive := by
  have zero : groupCohomology.H2π (realPlaneCuspidalRep degree cusp trivialCharacter)
      (cycle.val - (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val) = 0 := by
    rw [map_sub, realPlaneBinaryRelativeCycle_H2 degree cusp central_positive basis cycle regular, sub_self]
  obtain ⟨primitive, boundary⟩ := (groupCohomology.H2π_eq_zero_iff _).mp zero
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  funext pair
  have value := congrFun boundary pair
  change twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter) primitive pair =
    cycle.val pair - (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val pair at value
  change cycle.val pair = (realPlaneBinaryRelativeCycle degree cusp basis cycle regular).val pair +
    twoBoundaryCycle (realPlaneCuspidalRep degree cusp trivialCharacter) primitive pair
  rw [value]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
