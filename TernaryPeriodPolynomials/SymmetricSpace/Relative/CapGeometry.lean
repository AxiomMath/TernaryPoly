module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.FundamentalGeometry
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpen
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceComparison
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Contractible

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCap
open CategoryTheory HomologicalComplex TopologicalSpace
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedContractible
open SymmetricSpaceRelativeFundamental SingularBoundaryRestriction
open EquivariantSingularSmall SingularLocalCompactCap SingularLocalHomology SphereOddDegree

/-- The actual whole compact-bordification covering supplies its quotient-covering fact. -/
instance wholeCoverFact : Fact (IsQuotientCoveringMap wholeProjection principalSix) :=
  ⟨wholeQuotientCovering⟩

/-- Invariance of the literal interior preimage under the actual deck action. -/
instance interiorPreimageInvariant : Fact (InvariantSet principalSix (TopCat.of Glued)
    (wholeProjection ⁻¹' (boundary principalSix)ᶜ)) :=
  ⟨preimage_invariant (G := principalSix) wholeProjection (boundary principalSix)ᶜ⟩

/-- The literal interior preimage carries the canonical restricted deck action. -/
instance interiorPreimageAction : MulAction principalSix
    (wholeProjection ⁻¹' (boundary principalSix)ᶜ) :=
  invariantSubtypeAction principalSix (TopCat.of Glued) _

/-- The actual restricted deck action is continuous. -/
instance interiorPreimageContinuous : ContinuousConstSMul principalSix
    (wholeProjection ⁻¹' (boundary principalSix)ᶜ) :=
  invariantSubtypeContinuous principalSix (TopCat.of Glued) _

/-- The literal complement of the boundary is second countable through the arithmetic manifold. -/
instance interiorSecondCountable : SecondCountableTopology ↥(boundary principalSix)ᶜ :=
  interiorHomeomorph.secondCountableTopology

/-- The actual restricted covering above the literal interior complement. -/
abbrev interiorProjection := restrictedProjection wholeProjection (boundary principalSix)ᶜ

/-- The literal restricted interior projection retains its genuine covering fact. -/
instance interiorCoverFact : Fact (IsQuotientCoveringMap interiorProjection principalSix) :=
  ⟨restrictedQuotientCovering (G := principalSix) wholeProjection (boundary principalSix)ᶜ⟩

/-- The actual restricted covering action is free. -/
instance interiorPreimageFree : IsCancelSMul principalSix
    (wholeProjection ⁻¹' (boundary principalSix)ᶜ) :=
  (restrictedQuotientCovering (G := principalSix) wholeProjection (boundary principalSix)ᶜ).isCancelSMul

/-- The actual covering preimage of the interior complement is the proved
contractible symmetric-space interior preimage. -/
theorem preimage_interior_eq : wholeProjection ⁻¹' (boundary principalSix)ᶜ =
    projection principalSix ⁻¹' arithmeticInterior := by
  rw [boundary_compl_eq_range]
  rfl

/-- The cover of the literal interior complement is genuinely contractible. -/
instance interiorCoverContractible :
    ContractibleSpace (wholeProjection ⁻¹' (boundary principalSix)ᶜ) :=
  (Homeomorph.setCongr preimage_interior_eq).contractibleSpace

/-- Actual inclusion of the interior complement induces an isomorphism in all
local-coefficient homology degrees. -/
theorem interiorLocalInclusion_isIso (V : Rep.{0} ℚ principalSix) (k : ℕ) :
    IsIso (homologyMap (openLocalChainMap wholeProjection V (boundary principalSix)ᶜ) k) := by
  let : IsCancelSMul principalSix Glued := wholeQuotientCovering.isCancelSMul
  exact localSpaceMap_homology_isIso (sInclusion (wholeProjection ⁻¹' (boundary principalSix)ᶜ))
    (fun _ _ => rfl) interiorProjection wholeProjection
    (restrictedQuotientCovering wholeProjection (boundary principalSix)ᶜ) wholeQuotientCovering V k

end TernaryPoly.SymmetricSpaceRelativeCap
