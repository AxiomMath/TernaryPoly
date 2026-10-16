module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.LineDict

@[expose] public section


/-!
# A coinvariant cycle of the model cone kills the differentials of invariant edge cochains on its corner chain

If `v : coneR.X 4` is a coinvariant cycle and `f` an `N6`-invariant complex edge two-cochain, then for every
`ℚ`-linear functional `r : ℂ → ℚ` the value of `r` on the evaluation of `d f` on the corner chain of `v` is zero:
the corner cochain `(r ∘ f, 0, 0)` of the cone has coboundary `(-(d (r ∘ f)), 0, 0)`, which `v` kills.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

attribute [local instance] Comparison.vertexAction

theorem evalOmega_differentialTwo (v : coneR.X 4) (hv : IsCoinvCycle v) (r : ℂ →ₗ[ℚ] ℚ)
    (f : cochains N6 (functionRepresentation scalarTrivial Edges) 2) :
    r (evalOmega (cornerChain v) (differentialTwo N6 (functionRepresentation scalarTrivial Edges) f)) = 0 := by
  let e : (prodComplex Γ6 RationalGL3 Flag).X 2 ⟶ 𝟙_ (Rep.{0} ℚ Γ6) :=
    toHom psiEdge psiEdge_smul 2 f ≫ rHom r
  have h1 : coneR.d 4 3 ≫ cornerCochain flagLineHom.hom flagPlaneHom.hom (𝟙_ (Rep.{0} ℚ Γ6)) 2 e =
      cornerCochain flagLineHom.hom flagPlaneHom.hom (𝟙_ (Rep.{0} ℚ Γ6)) 3
        (-((prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ e)) := by
    apply (signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (𝟙_ (Rep.{0} ℚ Γ6)) 3).injective
    rw [cone_coboundary_coordinates, cornerCochain_coords, cornerCochain_coords]
    simp
  have h3 : (coneR.d 4 3 ≫ cornerCochain flagLineHom.hom flagPlaneHom.hom (𝟙_ (Rep.{0} ℚ Γ6)) 2 e).hom v = 0 :=
    hv (cornerCochain flagLineHom.hom flagPlaneHom.hom (𝟙_ (Rep.{0} ℚ Γ6)) 2 e)
  rw [h1, cornerCochain_eq] at h3
  have h4 : -(((prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ e).hom (cornerChain v)) = 0 := h3
  have h5 : ((prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ e).hom (cornerChain v) = 0 := neg_eq_zero.mp h4
  have h6 := hom_eq_evalChain_r (Y := (Fin (3 + 1) → RationalGL3) × Flag) ((prodComplex Γ6 RationalGL3 Flag).d 3 2 ≫ e) r
    (fun y => differentialTwo N6 (functionRepresentation scalarTrivial Edges) f y.1 (psiEdge.symm y.2))
    (fun y => (congrArg (rHom r).hom (homFun_d_toHom_two psiEdge psiEdge_smul f y.1 y.2)).trans (rHom_apply r _))
    (cornerChain v)
  exact (h6.symm.trans h5)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
