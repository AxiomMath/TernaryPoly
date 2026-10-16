module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.T0Face
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Unique
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.FaceRestrictionModel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.RationalNaturality
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.InnerLiftAmbiguity
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.StabilizerCoordinateModel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProduct
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.FaceCoordCone
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.SingularRestriction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.CornerIndependence
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.T0FaceSingular

@[expose] public section


/-!
# P09 L3: the constant-term restrictions of the cochain model are the geometric restrictions to the faces

Formalized by Claude Sonnet 5.5.

**Setting.**  `coneR` is the cone of the signed incidence of the three model resolutions
`ℚ[GL₃(ℚ)^{•+1} × Z]`, `Z` = complete flags, lines, planes, of `Γ(6)`; `Hom(coneR, W)` computes `H^*(∂M; W)`.  `coeffRep ρ` is the restriction of a
complex representation `ρ` of `GL₃(ℚ)` to `Γ(6)` as a rational representation.

**Results.**

* (model coordinates are plain restrictions) `faceRestriction ρ x`: restriction of group cohomology from the
  level `Γ` to the stabilizer `Γ_x` of a flag; `fixedPointH2_stratum_eq`, `cuspRes_restrictionCocycle`: the
  Shapiro coordinate of the constant-on-flags restriction `r_s a` is `faceRestriction`;
  `bridge_faceRestriction`: under the bridge to Mathlib it is `groupCohomology.map` along `Γ_x ↪ Γ`.
* (the model's `H²` is the cohomology of the open faces) for a `GL₃(ℚ)`-set `X ≃ Z`, the homogeneous
  cochains of `N6` with values in `Fun(X, ρ)` are the morphisms out of the model resolution
  `ℚ[V^{•+1} × Z] ⟶ coeffRep ρ` compatibly with the differentials (`modelHomOf`, `cochainOfHom`), and
  `modelClsH2 : H² N6 (Fun(X, ρ)) ≃ H²(Hom(ℚ[V^{•+1} × Z], coeffRep ρ))` is bijective
  (`modelClsH2_injective`, `modelClsH2_surjective`).
* (the geometric restriction) `coneToPt : coneR ⟶ ℚ[V^{•+1}]`, zero homotopy on the corner, induces
  `geoRestriction ρ : H²(Γ(6); ρ) → H²(coneR; ρ)`; it is the unique such map over the augmentation
  (`geoRestriction_eq_of_augmentation`, `coneToPt_line_augmentation`, `coneToPt_plane_augmentation`).
* (the dictionary) the line / plane components of `geoRestriction` of a global class `c` are `r_Q c`, `r_P c`:
  `geoRestriction_line_globalCoordinates`, `geoRestriction_plane_globalCoordinates`, and the cone
  coordinates of the representative are `(0, (r_Q c, r_P c))` (`geoRestriction_coordinates`).
* (inner classes) `innerLine_lift`, `innerPlane_lift`: an inner line (plane) class of the stratum lifts to a
  class of `H²(coneR; ρ)` with that line (plane) component and the other face component zero; the lift is the
  cone cochain `(e, l, 0)` (`(e, 0, p)`) whose corner component is the Hom cochain of the edge primitive
  (`InnerLift.lean`).
* (rational coefficients) `RationalNaturality`: postcomposition `homPost` is natural for all the maps above
  (`homologyMap_homPost_geo`, `homologyMap_homPost_line/plane`); `complexifyHom n : polyRep n (-1) ⟶ coeffRep E`
  is the complexification of the rational `Sym^n` of `Γ(6)`; `rational_face_components`: every rational
  class of `H²(Γ(6); polyRep n (-1))` complexifies to `ptCls E c` for a model cocycle `c`, and the complexified
  face components of its geometric restriction are the model coordinates `r_Q c`, `r_P c`.
* (lifts of inner classes modulo the corner) `InnerLiftAmbiguity`: `innerLineCone_shift` (independent of the
  representative), `innerLineCone_edge_change` / `innerLineCone_unique_mod_corner` (two lifts of the same
  class differ by `cornerClass e` for a corner cocycle `e`, which restricts to zero on both faces:
  `cornerClass_line`, `cornerClass_plane`), and the same for planes.  The model face pairing does not see
  this freedom: `FacePairingForm.pairingValue_eq` is independent of the edge primitive.
* (per-orbit Shapiro coordinate) `StabilizerCoordinate`: for a point `z` with stabilizer `S`, `faceCoord` sends
  `H^n(Hom_Γ(ℚ[V^{•+1}×Z], W))` to Mathlib's `groupCohomology (Rep.res S W) n` (through the bar resolution of
  `S`, for which `groupCohomologyIso` is the homology of the inhomogeneous cochains); on a bar generator
  `(x_1, ..., x_k)` it is the invariant function evaluated at the simplex with vertices `(x_1 ⋯ x_i) v₀` over
  `z` (`stabCoord_single`), independent of the chain map over the augmentation (`fixCoord_homology_eq`, by
  `uniqHomotopy`); `StabilizerCoordinateModel.stabCoord_modelHomOf(_two)`: for a model cochain it is the
  model's `fixedPointCochain` on the vertices `ι(x_1 ⋯ x_i)`, in degree two `(1, ι a, ι (a b))` as in
  `bridgeCocycle`.
* (agreement with the library's Shapiro decomposition) `ShapiroAgreement.stabCoord_homology_eq_subCoord`: for a
  representative `a = o.out` of an orbit, `faceCoord_a` is the `o`-th component of
  `homPullback κ ≫ fullShapiroIso` for every comparison `κ : stabilizerResolution ⟶ R`; and
  `ShapiroProduct.faceCoord_product_bijective`: **the product over orbit representatives of the Shapiro
  coordinates is an isomorphism** `H²(Hom_Γ(R, W)) ≃ ∏_o groupCohomology (Rep.res Stab(o) W) 2`.
* (restriction to the stabilizer) `StabilizerRestriction.faceCoord_restriction`: for the pullback to `Z` of a
  class on the point resolution, the coordinate at `z` is Mathlib's `groupCohomology.map` along `S ≤ Γ`;
  `FaceCoordCone.faceCoord_line_geoRestriction`, `faceCoord_plane_geoRestriction`: the same for the line and
  plane components of the geometric restriction of a class of `Γ(6)`.
* (singular restriction, link L5) `SingularRestriction.singular_restriction_eq_geoRestriction`: for every rational
  representation `W` of `Γ(6)` and every degree `n`, the geometric restriction `H(homPullback coneToPt W)` of a class of
  the point resolution is the singular restriction `geometricBoundaryRestriction` to the actual boundary of the
  corresponding class of the singular cohomology of the bordification (`groupLocalCohomologyIso`), transported to the
  model cone by the library's quasi-isomorphism `modelBoundaryQuasiIso` (built from `cone_to_boundary_quasiIso`);
  `geoRestriction_eq_singular_restriction` is degree two for `ptCls ρ c`.  Proof: the boundary comparison
  `coneEquiv.hom ≫ faceConeStabilizerEquiv.inv ≫ faceConeToBoundary`, the inclusion of the boundary, the comparison of
  the singular and bar resolutions and `fixThetaBar` give a chain map `coneToPtSingular` over the augmentation of
  `coneToPt` (`ConeAugmentation`: every comparison preserves the coefficient sum; the homotopy inverse does too, as
  chain maps into `single₀` are rigid under homotopy), hence homotopic to it (`coneHomotopy`).
* (corner ambiguity at the cone-cup level) `CornerIndependence.cone_pairing_corner_independent` (and the plane twin
  `cone_pairingP_corner_independent`, `corner_difference_evalOmega_zero`): the evaluation on the fundamental cycle `Ω` of the
  corner cochain of the cone cup product of the lifts `(z,0,w)`, `(y^φ,0,s^φ)` does not depend on the edge primitives, i.e. on
  the corner-cocycle ambiguity of the lifts; combination of the `traceValue_eq_evalOmega` with the representative
  independence `traceValue_eq_of_classes`.
* (the intertwiner) `T0_graph_geometric`: for any `T` with the graph property of `line_constant_term_comparison`, the graph of `T`
  on inner classes is the set of pairs (plane component, line component) of geometric restrictions of global
  classes with inner coordinates.

**Scope.**  The cone-level statements are at the level of the stratum cohomology `StratumH2`, i.e. of
all open faces simultaneously (`H²` of the Hom complex of `ℚ[V^{•+1} × Line]`, `ℚ[V^{•+1} × Plane]`).  The
per-point Shapiro coordinate `faceCoord` lands in Mathlib's `groupCohomology` of the stabilizer, agrees with
the model's stabilizer cocycle on cochains and, over all orbits, with the library's `fullShapiroIso` (degree two
for the product statement).  The comparison of `geoRestriction` with the singular restriction `H^*(M) → H^*(∂M)` of the library is link L5
(`geoRestriction_is_singular_restriction`, below): `geoRestriction_eq_of_augmentation` reduces it to exhibiting a
chain map over the augmentation, which is the boundary comparison of the library followed by the inclusion of the
boundary and the comparison of resolutions (`SingularRestriction.coneToPtSingular`).  The
model cone cup product of P2 (`modelCup`) is a function-level cup of cone cochains; the ambiguity of the lifts does not
affect the evaluation of its corner component on the fundamental cycle (`cone_pairing_corner_independent`).  The
identification of that evaluation with the geometric pairing on `H²(∂M; ρ)` (the cap comparison) is not asserted here.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FaceRestriction

open CategoryTheory GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

/-- The geometric restriction `H²(Γ(6); ρ) → H²(∂M; ρ)` (cocycle level), unique over the augmentation. -/
theorem geometric_restriction_unique {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (g : coneR ⟶ TernaryPeriodPolynomials.Argument.TopHomology.prodComplex Γ6 RationalGL3 PUnit)
    (hg : g.f 0 ≫ ptRes.π.f 0 = coneToPt.f 0 ≫ ptRes.π.f 0) (c : cocycles N6 ρ) :
    (HomologicalComplex.homologyMap
        (TernaryPoly.EquivariantSingularSmall.homPullback g (coeffRep ρ)) 2).hom (ptCls ρ c) =
      geoRestriction ρ c :=
  geoRestriction_eq_of_augmentation ρ g hg c

/-- The boundary coordinates of a global class are the face components of its geometric restriction. -/
theorem boundary_coordinates_are_face_restrictions (n : ℕ) (χ : RankOneCharacter)
    (c : cocycles rationalLevel (rationalCoefficientComponent n χ)) :
    (HomologicalComplex.homologyMap
        (TernaryPoly.EquivariantSingularSmall.homPullback conePlane
          (coeffRep (rationalCoefficientComponent n χ))) 2).hom
        (geoRestriction (rationalCoefficientComponent n χ)
          (TernaryPeriodPolynomials.Argument.LevelTransfer.cocyclesRes
            (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
      planeCls n χ (globalCoordinates n χ c).1 ∧
    (HomologicalComplex.homologyMap
        (TernaryPoly.EquivariantSingularSmall.homPullback coneLine
          (coeffRep (rationalCoefficientComponent n χ))) 2).hom
        (geoRestriction (rationalCoefficientComponent n χ)
          (TernaryPeriodPolynomials.Argument.LevelTransfer.cocyclesRes
            (rationalCoefficientComponent n χ) N6_le_rationalLevel c)) =
      lineCls n χ (globalCoordinates n χ c).2 :=
  ⟨geoRestriction_plane_globalCoordinates n χ c, geoRestriction_line_globalCoordinates n χ c⟩

/-- Inner line classes of the stratum are line components of classes of the cohomology of `∂M`. -/
theorem inner_line_class_lifts (n : ℕ) (χ : RankOneCharacter) (ξ : StratumH2 n χ .line)
    (hξ : InnerBoundary n χ .line ξ) :
    ∃ κ : (TernaryPoly.EquivariantSingularSmall.homCochains coneR
        (coeffRep (rationalCoefficientComponent n χ))).homology 2,
      (HomologicalComplex.homologyMap
          (TernaryPoly.EquivariantSingularSmall.homPullback coneLine
            (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = lineCls n χ ξ ∧
      (HomologicalComplex.homologyMap
          (TernaryPoly.EquivariantSingularSmall.homPullback conePlane
            (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = 0 :=
  innerLine_lift n χ ξ hξ

/-- Inner plane classes of the stratum are plane components of classes of the cohomology of `∂M`. -/
theorem inner_plane_class_lifts (n : ℕ) (χ : RankOneCharacter) (ξ : StratumH2 n χ .plane)
    (hξ : InnerBoundary n χ .plane ξ) :
    ∃ κ : (TernaryPoly.EquivariantSingularSmall.homCochains coneR
        (coeffRep (rationalCoefficientComponent n χ))).homology 2,
      (HomologicalComplex.homologyMap
          (TernaryPoly.EquivariantSingularSmall.homPullback conePlane
            (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = planeCls n χ ξ ∧
      (HomologicalComplex.homologyMap
          (TernaryPoly.EquivariantSingularSmall.homPullback coneLine
            (coeffRep (rationalCoefficientComponent n χ))) 2).hom κ = 0 :=
  innerPlane_lift n χ ξ hξ

/-- **Rational coefficients.**  Every rational class of `H²(Γ(6); Sym^n)` on the point resolution has, after
complexification, face components of its geometric restriction equal to the model coordinates of a cocycle
of the cochain model. -/
theorem rational_class_face_components (n : ℕ)
    (x : (TernaryPoly.EquivariantSingularSmall.homCochains
      (TernaryPeriodPolynomials.Argument.TopHomology.prodComplex Γ6 RationalGL3 PUnit)
      (polyRep n (-1))).homology 2) :
    ∃ c : cocycles N6 (Ecoef n),
      ptCls (Ecoef n) c = (HomologicalComplex.homologyMap (homPost _ (complexifyHom n)) 2).hom x ∧
      (HomologicalComplex.homologyMap (homPost _ (complexifyHom n)) 2).hom
          ((HomologicalComplex.homologyMap
            (TernaryPoly.EquivariantSingularSmall.homPullback coneLine (polyRep n (-1))) 2).hom
            ((HomologicalComplex.homologyMap
              (TernaryPoly.EquivariantSingularSmall.homPullback coneToPt (polyRep n (-1))) 2).hom x)) =
        modelCls (Ecoef n) psiLine psiLine_smul (restrictCocycle (Ecoef n) (Flags .line) c) ∧
      (HomologicalComplex.homologyMap (homPost _ (complexifyHom n)) 2).hom
          ((HomologicalComplex.homologyMap
            (TernaryPoly.EquivariantSingularSmall.homPullback conePlane (polyRep n (-1))) 2).hom
            ((HomologicalComplex.homologyMap
              (TernaryPoly.EquivariantSingularSmall.homPullback coneToPt (polyRep n (-1))) 2).hom x)) =
        modelCls (Ecoef n) psiPlane psiPlane_smul (restrictCocycle (Ecoef n) (Flags .plane) c) :=
  rational_face_components n x

/-- Corner classes restrict to zero on both families of faces. -/
theorem corner_class_restricts_to_zero {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V]
    [IsScalarTower ℚ ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (e : (TernaryPeriodPolynomials.Argument.TopHomology.prodComplex Γ6 RationalGL3
      TernaryPoly.SymmetricSpaceBoundaryMV.Flag).X 1 ⟶ coeffRep ρ)
    (he : (TernaryPeriodPolynomials.Argument.TopHomology.prodComplex Γ6 RationalGL3
      TernaryPoly.SymmetricSpaceBoundaryMV.Flag).d 2 1 ≫ e = 0) :
    (HomologicalComplex.homologyMap
        (TernaryPoly.EquivariantSingularSmall.homPullback coneLine (coeffRep ρ)) 2).hom
        (cornerClass ρ e he) = 0 ∧
    (HomologicalComplex.homologyMap
        (TernaryPoly.EquivariantSingularSmall.homPullback conePlane (coeffRep ρ)) 2).hom
        (cornerClass ρ e he) = 0 :=
  ⟨cornerClass_line ρ e he, cornerClass_plane ρ e he⟩

/-- **The Shapiro coordinates of the cohomology of the open faces.**  For the permutation resolution of a
`Γ`-set `Z`, the product over orbit representatives of the Shapiro coordinates is an isomorphism onto the
product of the Mathlib group cohomologies of the stabilizers (degree two). -/
theorem shapiro_coordinates_bijective {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V]
    [MulAction Γ Z] (v₀ : V) (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (W : Rep.{0} ℚ Γ) :
    Function.Bijective (fun x : (TernaryPoly.EquivariantSingularSmall.homCochains
        (TernaryPeriodPolynomials.Argument.TopHomology.prodComplex Γ V Z) W).homology 2 =>
      fun o : TernaryPoly.BoundaryFaceResolutionComparison.labelOrbits Γ Z =>
        (TernaryPeriodPolynomials.Argument.TopHomology.faceCoord
          (TernaryPoly.BoundaryFaceResolutionComparison.stabilizer Γ o.out) W v₀ o.out
          (fun g => g.2) 2).hom x) :=
  faceCoord_product_bijective v₀ hfree W

/-- **The geometric restriction of the model is the singular restriction to the boundary (link L5).**  For every
rational representation `W` of `Γ(6)` and every degree `n`, a class `y` of the point resolution (a class of
`H^n(Γ(6); W)`) restricted to the model cone by `coneToPt` equals, after transport by the library's
quasi-isomorphism `modelBoundaryQuasiIso`, the singular restriction to the actual boundary of the corresponding
class of the singular cohomology of the bordification. -/
alias geoRestriction_is_singular_restriction := singular_restriction_eq_geoRestriction

/-- The same, transported to `H^n(∂M; W)` by `modelBoundary_cohomology_iso`. -/
alias geoRestriction_is_singular_restriction_iso := singular_restriction_eq_geoRestriction_iso

/-- Degree two, for the class of a cocycle of `N6`. -/
alias geoRestriction_of_cocycle_is_singular_restriction := geoRestriction_eq_singular_restriction

/-- **Corner-ambiguity independence of the cone cup pairing.** -/
alias cone_pairing_independent_of_corner := cone_pairing_corner_independent

/-- The plane-supported twin. -/
alias cone_pairingP_independent_of_corner := cone_pairingP_corner_independent

/-- **The face dictionary of the intertwiner `T₀` (K2).**  For any `T` with the graph property of `line_constant_term_comparison`, the graph of `T` on
inner classes is the set of pairs (plane component, line component) of the geometric restrictions of global classes with inner
coordinates. -/
alias T0_graph_geometric := TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.T0_graph_geometric

/-- **The face dictionary of the intertwiner `T₀` for the library's singular restriction (P2).**  The same, with the
geometric restriction replaced, by link L5, by the singular restriction `H²(M; E) → H²(∂M; E)` of the class of the global cocycle
(`singularFaceRestriction`). -/
alias T0_graph_singular := TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.T0_graph_singular

end TernaryPeriodPolynomials.Argument.Statements.FaceRestriction
