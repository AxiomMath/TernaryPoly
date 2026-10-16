module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Restriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProjectiveUniqueness
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.PairHomotopyHom

@[expose] public section


/-!
# The restriction to the boundary cone is determined by its augmentation

The point resolution `ptRes` (the model resolution of the trivial representation) is a projective
resolution and the terms of the cone `coneR` are projective, so every chain map `coneR ⟶ ptRes.complex` with
the augmentation of `coneToPt` is homotopic to it (`coneToPt_unique`).  Consequently the map
`H^k(Γ(6); W) → H^k(coneR; W)` induced by *any* chain map over this augmentation is the one used in
`geoRestriction` (`homologyMap_homPullback_eq_of_augmentation`); in particular, any geometric
construction of the restriction `H^k(M; W) → H^k(∂M; W)` through chain maps of resolutions agrees with it as
soon as it sends a point of a face to the generator of `ℚ`.  The augmentation of `coneToPt` on the line and
plane summands is the collapse `ℚ[Line] → ℚ`, `ℚ[Plane] → ℚ` (`coneToPt_line_augmentation`,
`coneToPt_plane_augmentation`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly.EquivariantSingularPairHomotopy TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPoly.OrdinaryIncidence (Line Plane)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

/-- The model projective resolution of the trivial representation. -/
abbrev ptRes : ProjectiveResolution (Rep.ofMulAction ℚ Γ6 PUnit) :=
  prodResolution Γ6 RationalGL3 PUnit 1 vertexAction_free'

theorem coneR_projective (n : ℕ) : Projective (coneR.X n) := by
  have : ∀ n, Projective (resFlag.complex.X n) := fun n => resFlag.projective n
  have : ∀ n, Projective ((resLine.complex ⊞ resPlane.complex).X n) := projective_middle
  exact projectiveCone (signedArrow flagLineHom.hom flagPlaneHom.hom) n

/-- Two chain maps from the cone to the point resolution with the same augmentation are homotopic. -/
def coneHomotopy (g : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit)
    (hg : g.f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0) : Homotopy g coneToPt :=
  haveI : ∀ n, Projective (coneR.X n) := coneR_projective
  uniqHomotopy (Q := ptRes) g coneToPt hg

theorem homologyMap_homPullback_eq_of_augmentation (g : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit)
    (hg : g.f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0) (W : Rep.{0} ℚ Γ6) (n : ℕ) :
    homologyMap (homPullback g W) n = homologyMap (homPullback coneToPt W) n :=
  homPullback_cohomology_eq (coneHomotopy g hg) W n

theorem ptRes_π_f_zero : ptRes.π.f 0 = prodEps Γ6 RationalGL3 PUnit := by
  simp [ptRes, prodResolution, prodEpsToSingle]

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- **Canonicity of the geometric restriction in degree two**: any chain map from the cone to the point
resolution with the same augmentation induces the same restriction `H²(Γ(6); ρ) → H²(cone; ρ)`. -/
theorem geoRestriction_eq_of_augmentation (g : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit)
    (hg : g.f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0) (c : cocycles N6 ρ) :
    (homologyMap (homPullback g (coeffRep ρ)) 2).hom (ptCls ρ c) = geoRestriction ρ c := by
  unfold geoRestriction
  rw [homologyMap_homPullback_eq_of_augmentation g hg]

/-- The augmentation of the geometric restriction on the line summand is the collapse `ℚ[Line] → ℚ`. -/
theorem coneToPt_line_augmentation :
    signedLineInclusion flagLineHom.hom flagPlaneHom.hom 0 ≫ coneToPt.f 0 ≫
        prodEps Γ6 RationalGL3 PUnit =
      prodEps Γ6 RationalGL3 Line ≫ ofMulActionMap Γ6 Line (fun _ => PUnit.unit) (fun _ _ => rfl) := by
  rw [← Category.assoc, show signedLineInclusion flagLineHom.hom flagPlaneHom.hom 0 ≫ coneToPt.f 0 =
    (ptMap Line).f 0 from signedLineInclusion_coneDesc _ _ _ _ line_plane_ptMap 0]
  exact prodMapHom_f_zero_comp_eps Γ6 RationalGL3 Line (fun _ => PUnit.unit) (fun _ _ => rfl)

/-- The augmentation of the geometric restriction on the plane summand is the collapse `ℚ[Plane] → ℚ`. -/
theorem coneToPt_plane_augmentation :
    signedPlaneInclusion flagLineHom.hom flagPlaneHom.hom 0 ≫ coneToPt.f 0 ≫
        prodEps Γ6 RationalGL3 PUnit =
      prodEps Γ6 RationalGL3 Plane ≫ ofMulActionMap Γ6 Plane (fun _ => PUnit.unit) (fun _ _ => rfl) := by
  rw [← Category.assoc, show signedPlaneInclusion flagLineHom.hom flagPlaneHom.hom 0 ≫ coneToPt.f 0 =
    (ptMap Plane).f 0 from signedPlaneInclusion_coneDesc _ _ _ _ line_plane_ptMap 0]
  exact prodMapHom_f_zero_comp_eps Γ6 RationalGL3 Plane (fun _ => PUnit.unit) (fun _ _ => rfl)

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
