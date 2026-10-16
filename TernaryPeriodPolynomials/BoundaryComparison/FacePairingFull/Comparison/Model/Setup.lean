module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete
public import TernaryPeriodPolynomials.Topology.TopHomology.FreeNerve
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Inv
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Flags

@[expose] public section


/-!
# The three model resolutions of the stabilizer cone

The model resolutions `resFlag`, `resLine`, `resPlane` (`TopHomology.prodResolution` with the free
`Γ(6)`-set of ambient vertices `GL₃(ℚ)`) resolve the permutation modules of the flag, line and plane labels
of the arithmetic boundary (`TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation`), and the maps
`flagLineHom`, `flagPlaneHom` are resolution morphisms over the incidence maps `lineIncidence`,
`planeIncidence`.  The model flag sets `Edges`, `Flags .line`, `Flags .plane` are `Γ(6)`-equivariantly in
bijection with the labels (`psiEdge`, `psiLine`, `psiPlane`), compatibly with the endpoint maps.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open TernaryPoly TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation TernaryPoly.IntegralGL3Congruence
open TernaryPeriodPolynomials.Argument.TopHomology
open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

theorem vertexAction_free' : ∀ (γ : Γ6) (v : RationalGL3), γ • v = v → γ = 1 :=
  fun γ v h => vertexAction_free γ v h

/-- The model resolution of the flag labels. -/
abbrev resFlag : ProjectiveResolution flagLabels :=
  prodResolution Γ6 RationalGL3 Flag 1 vertexAction_free'

abbrev resLine : ProjectiveResolution lineLabels :=
  prodResolution Γ6 RationalGL3 Line 1 vertexAction_free'

abbrev resPlane : ProjectiveResolution planeLabels :=
  prodResolution Γ6 RationalGL3 Plane 1 vertexAction_free'

theorem lineIncidence_eq :
    lineIncidence = ofMulActionMap Γ6 Flag SymmetricSpaceBoundaryFaceAugmentation.flagLine
      flagLine_equivariant := by
  refine hom_ext_single Flag _ (fun F => ?_)
  rw [ofMulActionMap_single]
  exact lineIncidence_single F 1

theorem planeIncidence_eq :
    planeIncidence = ofMulActionMap Γ6 Flag SymmetricSpaceBoundaryFaceAugmentation.flagPlane
      flagPlane_equivariant := by
  refine hom_ext_single Flag _ (fun F => ?_)
  rw [ofMulActionMap_single]
  exact planeIncidence_single F 1

/-- The chain map from the flag resolution to the line resolution. -/
abbrev flagLineHom : ProjectiveResolution.Hom resFlag resLine lineIncidence where
  hom := prodMapHom Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagLine
    flagLine_equivariant
  hom_f_zero_comp_π_f_zero := by
    rw [lineIncidence_eq]
    simpa [resFlag, resLine, prodResolution, prodEpsToSingle] using
      prodMapHom_f_zero_comp_eps Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagLine
        flagLine_equivariant

/-- The chain map from the flag resolution to the plane resolution. -/
abbrev flagPlaneHom : ProjectiveResolution.Hom resFlag resPlane planeIncidence where
  hom := prodMapHom Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagPlane
    flagPlane_equivariant
  hom_f_zero_comp_π_f_zero := by
    rw [planeIncidence_eq]
    simpa [resFlag, resPlane, prodResolution, prodEpsToSingle] using
      prodMapHom_f_zero_comp_eps Γ6 RationalGL3 Flag SymmetricSpaceBoundaryFaceAugmentation.flagPlane
        flagPlane_equivariant

/-! ### Identification of the model flag sets with the labels -/

/-- Complete flags of the model are the labels `Flag` of the corners. -/
def psiEdge : Edges ≃ Flag := edgeEquiv

theorem psiEdge_smul (γ : Γ6) (e : Edges) : psiEdge (iotaQ γ • e) = γ • psiEdge e := by
  apply Subtype.ext
  have h := edgePair_smul (iotaQ γ) e
  exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

def psiLine : Flags .line ≃ Line := flagLineEquiv

theorem psiLine_smul (γ : Γ6) (F : Flags .line) : psiLine (iotaQ γ • F) = γ • psiLine F :=
  flagLine_smul (iotaQ γ) F

def psiPlane : Flags .plane ≃ Plane := flagPlaneEquiv

theorem psiPlane_smul (γ : Γ6) (F : Flags .plane) : psiPlane (iotaQ γ • F) = γ • psiPlane F :=
  flagPlane_smul (iotaQ γ) F

theorem psiEdge_line (e : Edges) :
    SymmetricSpaceBoundaryFaceAugmentation.flagLine (psiEdge e) = psiLine (endpoint .line e) := rfl

theorem psiEdge_plane (e : Edges) :
    SymmetricSpaceBoundaryFaceAugmentation.flagPlane (psiEdge e) = psiPlane (endpoint .plane e) := rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
