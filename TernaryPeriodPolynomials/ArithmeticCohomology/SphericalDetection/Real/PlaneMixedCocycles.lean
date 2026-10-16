module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.RadicalBinaryEquivariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CocycleEdge

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneSplitting : (SemidirectProduct.toGroupExtension realPlaneRadicalAction).Splitting :=
  SemidirectProduct.inr_splitting realPlaneRadicalAction

theorem realPlaneSplitting_input (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    splitRadicalInput realPlaneSplitting matrix radical = realRadicalInverseLevi matrix radical := by
  apply SemidirectProduct.inl_injective (φ := realPlaneRadicalAction)
  apply mul_left_cancel (a := (SemidirectProduct.inr matrix : RealPlaneGroup))
  exact (splitRadicalInput_commute realPlaneSplitting matrix radical).symm.trans
    (realRadicalInverseLevi_product matrix radical)

def realPlaneRadicalCocycle (degree : ℕ) (cusp : CuspidalRepresentation) :
    groupCohomology.cocycles₁ (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter)) →ₗ[ℂ]
      groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) :=
  oneCocyclePullback _ _ (MonoidHom.id RealPlaneRadical) (LinearMap.id) (by
    intro radical
    apply LinearMap.ext
    intro values
    change (realUpperCuspidalRep degree cusp).ρ radical values =
      (realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl radical) values
    exact congrArg (fun linear => linear values) (realUpperCuspidalRep_inl degree cusp radical))

theorem realPlaneRadicalCocycle_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : groupCohomology.cocycles₁ (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter)))
    (radical : RealPlaneRadical) : realPlaneRadicalCocycle degree cusp cycle radical = cycle radical := rfl

theorem realPlaneRadicalCocycle_levi (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter))) :
    realPlaneRadicalCocycle degree cusp
        (splitRadicalCocycleAction realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix cycle) =
      realUpperCuspidalCocycleLevi degree cusp matrix (realPlaneRadicalCocycle degree cusp cycle) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [realPlaneRadicalCocycle_apply, splitRadicalCocycleAction_apply, realPlaneSplitting_input]
  rfl

theorem realPlaneRadicalCocycle_boundary (degree : ℕ) (cusp : CuspidalRepresentation)
    (potential : cuspidalTensorValues cusp (HomogeneousPoly degree)) :
    realPlaneRadicalCocycle degree cusp
        (oneBoundaryCycle (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter)) potential) =
      oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  exact congrArg (fun (linear : Module.End ℂ (cuspidalTensorValues cusp (HomogeneousPoly degree))) =>
    linear potential - potential)
    (realUpperCuspidalRep_inl degree cusp radical).symm

def realPlaneMixedCocycle (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL) :
    relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter) →ₗ[ℂ]
      groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) :=
  (realPlaneRadicalCocycle degree cusp).comp
    (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix)

theorem realPlaneMixedCocycle_apply (degree : ℕ) (cusp : CuspidalRepresentation) (matrix : BinaryRealGL)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter))
    (radical : RealPlaneRadical) :
    realPlaneMixedCocycle degree cusp matrix cycle radical =
      cycle.val (SemidirectProduct.inr matrix, SemidirectProduct.inl (realRadicalInverseLevi matrix radical)) -
        cycle.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix) := by
  change realPlaneRadicalCocycle degree cusp
    (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) matrix cycle) radical = _
  rw [realPlaneRadicalCocycle_apply, splitEdgeCycle_apply, realPlaneSplitting_input]
  rfl

theorem realPlaneMixedCocycle_mul (degree : ℕ) (cusp : CuspidalRepresentation) (first second : BinaryRealGL)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl (realPlaneCuspidalRep degree cusp trivialCharacter)) :
    realPlaneMixedCocycle degree cusp (first * second) cycle =
      realUpperCuspidalCocycleLevi degree cusp first (realPlaneMixedCocycle degree cusp second cycle) +
        realPlaneMixedCocycle degree cusp first cycle +
        oneBoundaryCycle (realUpperCuspidalRep degree cusp)
          (cycle.val (SemidirectProduct.inr first, SemidirectProduct.inr second)) := by
  change realPlaneRadicalCocycle degree cusp
    (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) (first * second) cycle) = _
  rw [splitEdgeCycle_mul, map_add, map_add, realPlaneRadicalCocycle_levi]
  exact congrArg (fun boundary =>
    realUpperCuspidalCocycleLevi degree cusp first (realPlaneMixedCocycle degree cusp second cycle) +
      realPlaneMixedCocycle degree cusp first cycle + boundary)
    (realPlaneRadicalCocycle_boundary degree cusp
      (cycle.val (SemidirectProduct.inr first, SemidirectProduct.inr second)))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
