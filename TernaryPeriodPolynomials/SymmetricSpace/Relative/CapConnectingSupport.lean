module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapConnectingCore
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundarySupportAdapter
public import TernaryPeriodPolynomials.Topology.SingularLocal.BoundaryCapSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVPairingNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCapConnecting
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport SingularLocalCompactCap RationalCompactBoundary
open SymmetricSpaceBordifiedQuotient CompactInteriorRelativeBoundary

variable (V : Rep.{0} ℚ principalSix)

/-- The exact geometric-relative to interior-support adapter requested by the boundary cap model. -/
def geometricSupportIso : geometricRelativeCochains V ≅
    supportCochains wholeProjection V (boundary principalSix)ᶜ :=
  (boundaryGeometricIso V).symm ≪≫ boundarySupportIso V

/-- This adapter leaves the actual ambient geometric cochain unchanged. -/
theorem geometricSupportIso_inclusion :
    (geometricSupportIso V).hom ≫ supportInclusion wholeProjection V (boundary principalSix)ᶜ =
      kernel.ι (geometricBoundaryRestriction V) := by
  change ((boundaryGeometricIso V).inv ≫ (boundarySupportIso V).hom) ≫ _ = _
  rw [Category.assoc,boundarySupportIso_inclusion,← Category.assoc]
  exact boundaryGeometricIso_inv_inclusion V

/-- The geometric/support adapter and scalar boundary-to-support map preserve the literal cap
on every actual kernel cochain and cokernel scalar chain. -/
theorem geometricSupport_cap (a b : ℕ)
    (x : (geometricRelativeCochains V).X a)
    (c : (RationalRelativeSingular.relativeChains (boundary principalSix)).X (a+b)) :
    supportCap wholeProjection V (boundary principalSix)ᶜ a b
      ((geometricSupportIso V).hom.f a x) ((boundaryToSupport (boundary principalSix)).f (a+b) c) =
      relativeCochainCap boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
        boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V a b x c := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion (boundary principalSix)) (a+b) c
  have hc := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (boundaryToSupport_projection (boundary principalSix)) (a+b))
  change (boundaryToSupport (boundary principalSix)).f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion (boundary principalSix))).f (a+b) c) = _ at hc
  rw [hc,supportCap_projection]
  erw [relativeCochainCap_projection]
  have hx := congrArg (fun f => f x)
    (HomologicalComplex.congr_hom (geometricSupportIso_inclusion V) a)
  exact congrArg (fun y => cap wholeProjection wholeQuotientCovering V a b y c) hx

/-- The literal cap identity survives both homology quotients without changing the scalar class. -/
theorem geometricSupport_cap_homology (a b : ℕ)
    (x : (geometricRelativeCochains V).homology a)
    (c : (RationalRelativeSingular.relativeChains (boundary principalSix)).homology (a+b)) :
    supportCapHomology wholeProjection V (boundary principalSix)ᶜ a b
      (homologyMap (geometricSupportIso V).hom a x)
      (homologyMap (boundaryToSupport (boundary principalSix)) (a+b) c) =
      relativeCochainCapHomology boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
        boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V a b x c := by
  have h := SingularLocalCompactCapMV.pairing_homology_natural (geometricSupportIso V).hom
    (boundaryToSupport (boundary principalSix)) (𝟙 (localChains wholeProjection wholeQuotientCovering V))
    (relativeCochainCap boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
      boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V)
    (supportCap wholeProjection V (boundary principalSix)ᶜ)
    (relativeCochainCap_leibniz boundaryProjection wholeProjection boundaryInclusion boundaryBaseInclusion
      boundary_square boundaryQuotientCovering wholeQuotientCovering boundaryInclusion_equivariant V)
    (supportCap_leibniz wholeProjection V (boundary principalSix)ᶜ)
    (fun a b x c => (geometricSupport_cap V a b x c).symm) a b x c
  simp only [homologyMap_id,ModuleCat.id_apply] at h
  exact h.symm

/-- The actual relative fundamental cap equals the support-model boundary cap through precisely
(boundaryGeometricIso V).symm composed with boundarySupportIso V. -/
theorem relativeFundamentalCap_eq_boundaryCapMap :
    homologyMap (geometricSupportIso V).hom 2 ≫
      SingularLocalBoundaryCap.boundaryCapMap wholeProjection V (boundary principalSix) 3
        SymmetricSpaceRelativeFundamental.fundamentalClass 2 3 rfl =
      relativeFundamentalCap V := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact geometricSupport_cap_homology V 2 3 x SymmetricSpaceRelativeFundamental.fundamentalClass

end TernaryPoly.SymmetricSpaceRelativeCapConnecting
