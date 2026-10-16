module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullTransfer
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyModels

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex ModThreeGoodAction IntegralGL3Congruence
open SymmetricSpaceRationalGluing SingularBoundaryRestriction EquivariantSingularResolution
open SymmetricSpaceBoundaryFullTransfer

/-- The full integral action preserves the entire upstairs geometric boundary. -/
theorem integral_boundary_preserved (g : IntegralGL) (x : BoundaryCover) :
    g • x.val ∈ upstairsBoundary := by
  intro hx
  rcases hx with ⟨S,hS⟩
  apply x.property
  refine ⟨SymmetricSpacePositive.act (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) g⁻¹) S,?_⟩
  have h := congrArg (fun y : Glued => g⁻¹ • y) hS
  rw [inv_smul_smul] at h
  exact (integralAction_embedding g⁻¹ S).symm.trans h

instance integralBoundaryAction : MulAction IntegralGL BoundaryCover where
  smul g x := ⟨g • x.val,integral_boundary_preserved g x⟩
  one_smul x := Subtype.ext (one_smul IntegralGL x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

instance integralBoundaryContinuous : ContinuousConstSMul IntegralGL BoundaryCover where
  continuous_const_smul g :=
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _

/-- Both actions on the cover use the same literal integral matrix. -/
theorem boundary_action_restrict (g : principalSix) (x : BoundaryCover) :
    (g.val : IntegralGL) • x = g • x := rfl

abbrev fullBoundaryChains := equivariantChains IntegralGL (TopCat.of BoundaryCover)

/-- Restriction of the full boundary representation complex is identity on singular chains. -/
def boundaryChainRestrictionIso : restrictedComplex principalSix fullBoundaryChains ≅
    SymmetricSpaceBoundaryIncidenceHomology.boundaryChains :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by rfl)

end TernaryPoly.SymmetricSpaceBoundaryFull
