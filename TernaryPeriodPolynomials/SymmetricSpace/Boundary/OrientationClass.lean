module

public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationGlobal
public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalClass
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ManifoldCharts

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryOrientation
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular RationalLocalChartHomology
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SingularBoundaryRestriction HalfSpaceBoundaryOrientation

/-- The actual entire-boundary class is the literal connecting image of the uniquely
normalized arithmetic relative fundamental class. No generator or sign is chosen here. -/
def boundaryFundamentalClass : (chains BoundaryBase).homology 4 :=
  RationalRelativeSingular.connecting (boundary principalSix) 4
    SymmetricSpaceRelativeFundamental.fundamentalClass

/-- The boundary class uses precisely the fixed degree-lowering connecting homomorphism. -/
theorem boundaryFundamentalClass_eq_connecting :
    boundaryFundamentalClass =
      RelativeChainSequence.connecting (RationalRelativeSingular.inclusion (boundary principalSix)) 4
        SymmetricSpaceRelativeFundamental.fundamentalClass := rfl

/-- The actual boundary-point generator is the literal local projection of the boundary class. -/
def boundaryGenerator (x : BoundaryBase) : (localChains x).homology 4 :=
  globalGenerator 4 boundaryFundamentalClass x

/-- The literal connecting-to-point formula fixes every local generator's sign. -/
theorem boundaryGenerator_eq_connecting_point (x : BoundaryBase) :
    boundaryGenerator x =
      (RationalRelativeSingular.connecting (boundary principalSix) 4 ≫
        homologyMap (absolutePointProjection x) 4)
          SymmetricSpaceRelativeFundamental.fundamentalClass := rfl

/-- The exact boundary-point family is locally represented by one actual global class. -/
theorem boundaryGenerator_locallyRepresented :
    RationalLocalOrientation.LocallyRepresented 4 boundaryGenerator :=
  globalGenerator_locallyRepresented 4 boundaryFundamentalClass

/-- Exactness sends the actual boundary fundamental class to zero in ambient homology. -/
theorem boundaryFundamentalClass_inclusion_zero :
    homologyMap (RationalRelativeSingular.inclusion (boundary principalSix)) 4
      boundaryFundamentalClass = 0 := by
  have hr : boundaryFundamentalClass ∈
      LinearMap.range (RationalRelativeSingular.connecting (boundary principalSix) 4).hom :=
    ⟨SymmetricSpaceRelativeFundamental.fundamentalClass,rfl⟩
  rw [RelativeChainSequence.range_connecting_eq_kernel_inclusion] at hr
  exact hr

end TernaryPoly.SymmetricSpaceBoundaryOrientation
