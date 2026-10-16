module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.GeoEval
public import TernaryPeriodPolynomials.Topology.SingularLocal.DualityDetection
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Orientation

@[expose] public section


/-!
# The geometric Poincaré-duality pairing on the arithmetic boundary

On the closed oriented four-manifold `∂M` (quotient boundary of the bordified symmetric space of `Γ(6)`),
for a rational representation `V` of `Γ(6)` with full contragredient `dualRepresentation V`, the pairing of
`H²(∂M; V*)` with `H²(∂M; V)` is defined from the two pieces the library supplies and nothing else:

* the cap product `boundaryOrdinaryCapIso V o 2 2 : H²(∂M; V) ≅ H₂(∂M; V)` with the fundamental class of an
  orientation `o` (`SymmetricSpaceBoundaryManifold`), and
* the Kronecker pairing `homologyPairing` of `H²(∂M; V*)` with `H₂(∂M; V)` (universal coefficients,
  `SingularLocalDuality`).

`geoPairing V o α β = ⟨α, [∂M] ∩ β⟩`.  It is the Poincaré-duality pairing of the manifold, the "oriented face"
integration pairing of the paper in the geometric model.  Proved: it is left non-degenerate with the full
dual (`geoPairing_leftEquiv`: `α ↦ geoPairing α` is a linear equivalence `H²(∂M; V*) ≃ Dual H²(∂M; V)`), and
right non-degenerate (`geoPairing_right_injective`).

Not asserted: any comparison with the cochain model's `facePairing`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex TernaryPoly.SymmetricSpaceBoundaryGeometricCone
open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SingularBoundaryRestriction
  TernaryPoly.SymmetricSpaceBoundaryManifold TernaryPoly.RationalLocalOrientation

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable (V : Rep.{0} ℚ principalSix)

/-- The linear map `H²(∂M; V*) → Dual H²(∂M; V)`: Kronecker pairing with the cap product. -/
def geoPairing (o : Orientation 4 (TopCat.of BoundaryBase)) :
    (localBoundaryCochains (SingularLocalDuality.dualRepresentation V)).homology 2 →ₗ[ℚ]
      Module.Dual ℚ ((localBoundaryCochains V).homology 2) :=
  haveI : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  (boundaryOrdinaryCap V o 2 2 rfl).hom.dualMap.comp
    (SingularLocalDuality.homologyPairing boundaryProjection boundaryQuotientCovering V 2)

/-- **Left perfectness**: `α ↦ ⟨α, [∂M] ∩ ·⟩` is a linear equivalence from `H²(∂M; V*)` onto the full dual of
`H²(∂M; V)` (universal coefficients composed with the inverse of the cap isomorphism). -/
def geoPairingEquiv (o : Orientation 4 (TopCat.of BoundaryBase)) :
    (localBoundaryCochains (SingularLocalDuality.dualRepresentation V)).homology 2 ≃ₗ[ℚ]
      Module.Dual ℚ ((localBoundaryCochains V).homology 2) :=
  haveI : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  ((SingularLocalDuality.universalCoefficientIso boundaryProjection boundaryQuotientCovering V 2).toLinearEquiv
    ≪≫ₗ (boundaryOrdinaryCapIso V o 2 2 rfl).toLinearEquiv.dualMap)

theorem geoPairingEquiv_apply (o : Orientation 4 (TopCat.of BoundaryBase))
    (α : (localBoundaryCochains (SingularLocalDuality.dualRepresentation V)).homology 2) :
    geoPairingEquiv V o α = geoPairing V o α := rfl

/-- **Right non-degeneracy**: a class of `H²(∂M; V)` pairing to zero with all of `H²(∂M; V*)` vanishes. -/
theorem geoPairing_right_injective (o : Orientation 4 (TopCat.of BoundaryBase))
    (β : (localBoundaryCochains V).homology 2) (h : ∀ α, geoPairing V o α β = 0) : β = 0 := by
  have : IsCancelSMul principalSix BoundaryCover := boundaryQuotientCovering.isCancelSMul
  have hz : (boundaryOrdinaryCap V o 2 2 rfl).hom β = 0 :=
    (SingularLocalDuality.homology_eq_zero_iff_pairing boundaryProjection boundaryQuotientCovering V 2 _).2
      (fun α => h α)
  exact (boundaryOrdinaryCapIso V o 2 2 rfl).toLinearEquiv.injective (hz.trans (map_zero _).symm)

/-- The pairing for the orientation of the boundary fundamental class (`boundaryOrientation`). -/
abbrev geoPairingBoundary :=
  geoPairing V TernaryPoly.SymmetricSpaceBoundaryOrientation.boundaryOrientation

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
