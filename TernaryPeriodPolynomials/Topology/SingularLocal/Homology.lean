module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Complex
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Contractible

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedPrincipalSix
  SymmetricSpaceBordifiedQuotient SymmetricSpaceCompactBordification IntegralGL3Congruence
open scoped Classical

/-- The actual projection of the contractible full rational corner gluing to its compact
principal-six arithmetic bordification, as a genuine TopCat morphism. -/
def bordifiedProjection : TopCat.of Glued ⟶ TopCat.of BordifiedOrbit :=
  TopCat.ofHom ⟨SymmetricSpaceBordifiedQuotient.projection principalSix,
    projection_continuous principalSix⟩

/-- The actual principal-six action is free and has finite compact transporters, so the
literal projection is a quotient covering, including at every boundary stratum. -/
theorem bordifiedProjection_quotientCovering : IsQuotientCoveringMap bordifiedProjection principalSix :=
  SymmetricSpaceCovering.quotientCovering_of_finite_transporters
    (subgroup_compact_transporters principalSix) principalSix_free

/-- The genuine quotient-covering freeness supplies the singular-chain projective resolution. -/
instance bordifiedPrincipalSixFree : IsCancelSMul principalSix Glued :=
  bordifiedProjection_quotientCovering.isCancelSMul

/-- The actual geometric local-coefficient chains on the compact arithmetic bordification. -/
abbrev bordifiedLocalChains (V : Rep.{0} ℚ principalSix) : ChainComplex (ModuleCat ℚ) ℕ :=
  localChains bordifiedProjection bordifiedProjection_quotientCovering V

/-- The full compact-bordification comparison is a genuine chain isomorphism to actual
coinvariant singular chains of the proved contractible covering space. -/
def bordifiedChainIso (V : Rep.{0} ℚ principalSix) :
    coinvariantChains principalSix (TopCat.of Glued) V ≅ bordifiedLocalChains V :=
  chainIso bordifiedProjection bordifiedProjection_quotientCovering V

/-- In every degree the actual geometric local-coefficient homology of the compact
principal-six bordification computes literal Mathlib group homology. -/
def bordifiedGroupLocalHomologyIso (V : Rep.{0} ℚ principalSix) (n : ℕ) :
    groupHomology V n ≅ (bordifiedLocalChains V).homology n :=
  groupLocalHomologyIso bordifiedProjection bordifiedProjection_quotientCovering V n

/-- The actual elementary-chain correspondence retains the original singular lift and the
coefficient's value at its actual first vertex. -/
theorem bordifiedChainIso_inv_single (V : Rep.{0} ℚ principalSix) (n : ℕ)
    {σ : SingularSimplex (TopCat.of BordifiedOrbit) n} (τ : Lifts bordifiedProjection σ)
    (c : FiberCoefficient bordifiedProjection bordifiedProjection_quotientCovering V (atVertex σ)) :
    (bordifiedChainIso V).inv.f n (DFinsupp.single σ c) =
      generator principalSix (TopCat.of Glued) V n τ.val
        (c.val (liftVertexEquiv bordifiedProjection bordifiedProjection_quotientCovering σ τ)) :=
  chainIso_inv_single bordifiedProjection bordifiedProjection_quotientCovering V n τ c

/-- The actual compact-bordification boundary uses the backwards transported actual face coefficients. -/
theorem bordified_boundary_single (V : Rep.{0} ℚ principalSix) (n : ℕ)
    (σ : SingularSimplex (TopCat.of BordifiedOrbit) (n+1))
    (c : FiberCoefficient bordifiedProjection bordifiedProjection_quotientCovering V (atVertex σ)) :
    (bordifiedLocalChains V).d (n+1) n (DFinsupp.single σ c) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        DFinsupp.single (pullSimplex (simplexCoface n i) σ)
          (coefficientTransportLinear bordifiedProjection bordifiedProjection_quotientCovering
            (simplexPullPath (simplexCoface n i) σ).symm c) := by
  change (localChains bordifiedProjection bordifiedProjection_quotientCovering V).d (n+1) n _ = _
  simp only [localChains, ChainComplex.of_d]
  exact boundary_single bordifiedProjection bordifiedProjection_quotientCovering V n σ c

end TernaryPoly.SingularLocalHomology
