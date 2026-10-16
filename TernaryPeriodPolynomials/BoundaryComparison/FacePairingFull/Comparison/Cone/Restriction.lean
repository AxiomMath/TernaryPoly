module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Comparison
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.HomClass
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Desc

@[expose] public section


/-!
# The restriction from `Γ(6)` to the boundary cone

Let `ptMap Z : ℚ[V^{•+1} × Z] ⟶ ℚ[V^{•+1}]` be the chain map of the projection `Z → pt`.  The projections
of the flag, line and plane resolutions to the point resolution are compatible with the incidence maps, so
the signed cone `coneR` of the three model resolutions (the boundary complex of the arithmetic
bordification) maps to the point resolution (that of `Γ(6)` itself) by `coneToPt`, with zero homotopy on
the corner.  On `Hom(-, ρ|_{Γ(6)})` this is the geometric restriction `H^k(Γ(6); ρ) → H^k(∂M; ρ)`
(`geoRestriction` in degree two).  It restricts to the line and plane faces as the constant-on-flags
restriction of the cochain model:

* `geoRestriction_line`: the line component of the geometric restriction of a cocycle `c` of `N6` is the
  class `modelCls` of the stratum cocycle `restrictCocycle (Flags .line) c`;
* `geoRestriction_plane`: the same for planes;
* `geoRestriction_coordinates`: the cone coordinates are `(0, r_Q c, r_P c)` (zero on the corner).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)

/-- The chain map of the projection of the label set to a point. -/
def ptMap (Z : Type) [MulAction Γ6 Z] :
    prodComplex Γ6 RationalGL3 Z ⟶ prodComplex Γ6 RationalGL3 PUnit :=
  prodMapHom Γ6 RationalGL3 Z (fun _ => PUnit.unit) (fun _ _ => rfl)

theorem prodMapHom_comp_ptMap {Z Z' : Type} [MulAction Γ6 Z] [MulAction Γ6 Z'] (α : Z → Z')
    (hα : ∀ (γ : Γ6) (z : Z), α (γ • z) = γ • α z) :
    prodMapHom Γ6 RationalGL3 Z α hα ≫ ptMap Z' = ptMap Z := by
  apply HomologicalComplex.hom_ext
  intro k
  apply hom_ext_single ((Fin (k + 1) → RationalGL3) × Z)
  rintro ⟨x, z⟩
  have h1 := prodMapHom_f_single Γ6 RationalGL3 Z α hα k x z
  have h2 := prodMapHom_f_single Γ6 RationalGL3 Z' (fun _ => PUnit.unit) (fun _ _ => rfl) k x (α z)
  have h3 := prodMapHom_f_single Γ6 RationalGL3 Z (fun _ => PUnit.unit) (fun _ _ => rfl) k x z
  change ((ptMap Z').f k).hom (((prodMapHom Γ6 RationalGL3 Z α hα).f k).hom
      (MonoidAlgebra.single (x, z) 1)) = ((ptMap Z).f k).hom (MonoidAlgebra.single (x, z) 1)
  exact ((congrArg ((ptMap Z').f k).hom h1).trans h2).trans h3.symm

theorem flagLine_ptMap : flagLineHom.hom ≫ ptMap Line = ptMap Flag :=
  prodMapHom_comp_ptMap _ _

theorem flagPlane_ptMap : flagPlaneHom.hom ≫ ptMap Plane = ptMap Flag :=
  prodMapHom_comp_ptMap _ _

theorem line_plane_ptMap :
    flagLineHom.hom ≫ ptMap Line = flagPlaneHom.hom ≫ ptMap Plane :=
  flagLine_ptMap.trans flagPlane_ptMap.symm

/-- **The restriction of `Γ(6)` to the boundary cone**: the chain map from the cone of the three model
resolutions to the point resolution, with zero homotopy on the corner. -/
def coneToPt : coneR ⟶ prodComplex Γ6 RationalGL3 PUnit :=
  coneDesc flagLineHom.hom flagPlaneHom.hom (ptMap Line) (ptMap Plane) line_plane_ptMap

/-- The inclusion of the line resolution into the cone. -/
def coneLine : prodComplex Γ6 RationalGL3 Line ⟶ coneR :=
  biprod.inl ≫ homotopyCofiber.inr (signedArrow flagLineHom.hom flagPlaneHom.hom)

/-- The inclusion of the plane resolution into the cone. -/
def conePlane : prodComplex Γ6 RationalGL3 Plane ⟶ coneR :=
  biprod.inr ≫ homotopyCofiber.inr (signedArrow flagLineHom.hom flagPlaneHom.hom)

theorem coneLine_f (n : ℕ) :
    coneLine.f n = signedLineInclusion flagLineHom.hom flagPlaneHom.hom n := rfl

theorem conePlane_f (n : ℕ) :
    conePlane.f n = signedPlaneInclusion flagLineHom.hom flagPlaneHom.hom n := rfl

theorem coneLine_coneToPt : coneLine ≫ coneToPt = ptMap Line := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [comp_f, coneLine_f]
  exact signedLineInclusion_coneDesc _ _ _ _ line_plane_ptMap n

theorem conePlane_coneToPt : conePlane ≫ coneToPt = ptMap Plane := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [comp_f, conePlane_f]
  exact signedPlaneInclusion_coneDesc _ _ _ _ line_plane_ptMap n

section Coeff

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- A cochain of `N6` with values in `ρ`, viewed as a cochain with values in functions on `X` that is
constant on `X`. -/
def restrictCochain (X : Type) [MulAction RationalGL3 X] {k : ℕ} (f : cochains N6 ρ k) :
    cochains N6 (functionRepresentation ρ X) k :=
  ⟨fun x _ => f.1 x, by
    intro γ x
    funext e
    exact f.2 γ x⟩

/-- Constant-on-`X` restriction of an `N6`-cocycle (the cochain-model form of `r_s`). -/
def restrictCocycle (X : Type) [MulAction RationalGL3 X] (c : cocycles N6 ρ) :
    cocycles N6 (functionRepresentation ρ X) :=
  ⟨restrictCochain ρ X c.val, by
    have h : differentialTwo N6 ρ c.val = 0 := c.property
    change differentialTwo N6 (functionRepresentation ρ X) (restrictCochain ρ X c.val) = 0
    funext x
    funext e
    exact congrFun h x⟩

/-- The morphism out of the point resolution attached to a cochain of `N6`. -/
def ptHom {k : ℕ} (f : cochains N6 ρ k) :
    (prodComplex Γ6 RationalGL3 PUnit).X k ⟶ coeffRep ρ :=
  modelHomOf ρ (Equiv.refl PUnit) (fun _ _ => rfl) (restrictCochain ρ PUnit f)

theorem modelHomOf_restrictCochain {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z]
    (ψ : X ≃ Z) (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x) {k : ℕ}
    (f : cochains N6 ρ k) :
    modelHomOf ρ ψ hψ (restrictCochain ρ X f) = (ptMap Z).f k ≫ ptHom ρ f := by
  apply homFunA_injective
  funext y
  rw [homFunA_modelHomOf]
  obtain ⟨x, z⟩ := y
  have h := homFunA_comp_map (A := coeffRep ρ) (V := RationalGL3) (Γ := Γ6) (Z := Z)
    (Z' := PUnit) (fun _ => PUnit.unit) (fun _ _ => rfl) (ptHom ρ f) x z
  change _ = homFunA ((prodMapHom Γ6 RationalGL3 Z (fun _ => PUnit.unit) (fun _ _ => rfl)).f k ≫
    ptHom ρ f) (x, z)
  rw [h, ptHom, homFunA_modelHomOf]
  rfl

/-- The class of the constant-on-a-point restriction of an `N6`-cocycle: its class in `H²(Γ(6); ρ)`
computed on the point resolution. -/
def ptCls (c : cocycles N6 ρ) : (homK ρ (Z := PUnit)).homology 2 :=
  modelCls ρ (Equiv.refl PUnit) (fun _ _ => rfl) (restrictCocycle ρ PUnit c)

/-- **The geometric restriction of a class of `Γ(6)` to the boundary cone**, in degree two. -/
def geoRestriction (c : cocycles N6 ρ) : (homCochains coneR (coeffRep ρ)).homology 2 :=
  (homologyMap (homPullback coneToPt (coeffRep ρ)) 2).hom (ptCls ρ c)

theorem homologyMap_homPullback_comp {C D K : ChainComplex (Rep.{0} ℚ Γ6) ℕ} (f : C ⟶ D) (g : D ⟶ K)
    (W : Rep.{0} ℚ Γ6) (x : (homCochains K W).homology 2) :
    (homologyMap (homPullback f W) 2).hom ((homologyMap (homPullback g W) 2).hom x) =
      (homologyMap (homPullback (f ≫ g) W) 2).hom x := by
  rw [homPullback_comp, homologyMap_comp]
  rfl

/-- The face projection of the model class of a pulled-back cocycle. -/
theorem homologyMap_ptMap_ptCls {Z : Type} [MulAction Γ6 Z] {X : Type} [MulAction RationalGL3 X]
    (ψ : X ≃ Z) (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x) (c : cocycles N6 ρ) :
    (homologyMap (homPullback (ptMap Z) (coeffRep ρ)) 2).hom (ptCls ρ c) =
      modelCls ρ ψ hψ (restrictCocycle ρ X c) := by
  unfold ptCls modelCls
  refine (cls2_map (homK ρ (Z := PUnit)) (homPullback (ptMap Z) (coeffRep ρ)) _ _ ?_).trans ?_
  · exact map_cocycle (homK ρ (Z := PUnit)) (homPullback (ptMap Z) (coeffRep ρ)) _
      (modelHomOf_cocycle ρ (Equiv.refl PUnit) (fun _ _ => rfl) (restrictCocycle ρ PUnit c))
  refine cls2_congr _ _ _ ?_
  exact (modelHomOf_restrictCochain ρ ψ hψ c.val).symm

/-- **The line component of the geometric restriction is the constant-on-lines restriction of the cochain
model**, `r_Q`. -/
theorem geoRestriction_line (c : cocycles N6 ρ) :
    (homologyMap (homPullback coneLine (coeffRep ρ)) 2).hom (geoRestriction ρ c) =
      modelCls ρ psiLine psiLine_smul (restrictCocycle ρ (Flags .line) c) := by
  unfold geoRestriction
  rw [homologyMap_homPullback_comp, coneLine_coneToPt]
  exact homologyMap_ptMap_ptCls ρ psiLine psiLine_smul c

/-- The plane component of the geometric restriction is the constant-on-planes restriction `r_P`. -/
theorem geoRestriction_plane (c : cocycles N6 ρ) :
    (homologyMap (homPullback conePlane (coeffRep ρ)) 2).hom (geoRestriction ρ c) =
      modelCls ρ psiPlane psiPlane_smul (restrictCocycle ρ (Flags .plane) c) := by
  unfold geoRestriction
  rw [homologyMap_homPullback_comp, conePlane_coneToPt]
  exact homologyMap_ptMap_ptCls ρ psiPlane psiPlane_smul c

/-- **Cone coordinates of the geometric restriction**: a representative of `geoRestriction ρ c` is
`coneToPt.f 2 ≫ ptHom c`, whose cone coordinates are `(0, (r_Q c, r_P c))`: zero on the corner, the
constant-on-lines cochain on the line summand and the constant-on-planes cochain on the plane summand. -/
theorem geoRestriction_coordinates (c : cocycles N6 ρ) :
    signedConeHomSucc flagLineHom.hom flagPlaneHom.hom (coeffRep ρ) 1
        (coneToPt.f 2 ≫ ptHom ρ c.val) =
      (0, (modelHomOf ρ psiLine psiLine_smul (restrictCochain ρ (Flags .line) c.val),
        modelHomOf ρ psiPlane psiPlane_smul (restrictCochain ρ (Flags .plane) c.val))) := by
  refine (signedConeHomSucc_coneDesc flagLineHom.hom flagPlaneHom.hom (ptMap Line) (ptMap Plane)
    (coeffRep ρ) line_plane_ptMap 1 (ptHom ρ c.val)).trans ?_
  rw [modelHomOf_restrictCochain ρ psiLine psiLine_smul c.val,
    modelHomOf_restrictCochain ρ psiPlane psiPlane_smul c.val]

/-- The Shapiro coordinate at a flag of the model class of a morphism `c` out of the model resolution
is the restriction of `c` to the chains `V^{k+1} × {ψ F}` of the face of `F`. -/
theorem fixedPointCochain_cochainOfHom {X Z : Type} [MulAction RationalGL3 X] [MulAction Γ6 Z]
    (ψ : X ≃ Z) (hψ : ∀ (γ : Γ6) (x : X), ψ (iotaQ γ • x) = γ • ψ x) {k : ℕ}
    (c : (prodComplex Γ6 RationalGL3 Z).X k ⟶ coeffRep ρ) (F : X) (x : Fin (k + 1) → RationalGL3) :
    (TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers.fixedPointCochain
        N6 ρ F k (cochainOfHom ρ ψ hψ c)).val x = homFunA c (x, ψ F) := rfl

end Coeff

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
