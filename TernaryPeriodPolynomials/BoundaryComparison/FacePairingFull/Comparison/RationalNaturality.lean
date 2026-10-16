module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.T0Face
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Cone.Unique
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Coefficients

@[expose] public section


/-!
# The cone cohomology is natural in the coefficients: rational `polynomialCoefficients`

Postcomposition with a morphism `φ : W ⟶ W'` of rational representations of `Γ(6)` is a cochain map
`homPost φ : Hom(C, W) ⟶ Hom(C, W')` for every chain complex `C` of representations, and it commutes with
the pullbacks along chain maps.  Hence the geometric restriction to the boundary cone, the cone
inclusions of the line and plane faces and all their induced maps on cohomology are natural in the
coefficients (`homologyMap_homPost_natural`).

Applied to the complexification `complexifyHom n : polyRep n (-1) ⟶ coeffRep E` of the rational
coefficient system `Sym^n` of `Γ(6)` (Comparison.Coefficients; `E` the cochain-model coefficients of trivial
character), every rational class of `H²(Γ(6); polyRep n (-1))` complexifies to a class of the point
resolution which is `ptCls E c` for a cocycle `c` of the model (`ptCls_surjective`), and the face
components of its geometric restriction are the complexifications of the rational face components and the
model coordinates of `c` (`rational_face_components_plane/line`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Category Limits HomologicalComplex
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.SymmetricSpaceBoundaryFull TernaryPoly.EquivariantSingularSmall
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.IntegralGL3Congruence (principalSix)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

attribute [local instance] vertexAction

section Post

variable {G : Type} [Group G] (C : ChainComplex (Rep.{0} ℚ G) ℕ) {W W' : Rep.{0} ℚ G}

/-- Postcomposition with a morphism of coefficient representations, as a cochain map. -/
def homPost (φ : W ⟶ W') : homCochains C W ⟶ homCochains C W' where
  f n := ModuleCat.ofHom
    { toFun := fun c => c ≫ φ
      map_add' := fun c c' => Preadditive.add_comp _ _ _ c c' φ
      map_smul' := fun r c => by simp }
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change C.d j i ≫ (c ≫ φ) = (C.d j i ≫ c) ≫ φ
    exact (Category.assoc _ _ _).symm

theorem homPost_apply (φ : W ⟶ W') (n : ℕ) (c : C.X n ⟶ W) :
    ((homPost C φ).f n).hom c = c ≫ φ := rfl

/-- Pullback along a chain map commutes with postcomposition. -/
theorem homPost_homPullback {C D : ChainComplex (Rep.{0} ℚ G) ℕ} (f : C ⟶ D) (φ : W ⟶ W') :
    homPost D φ ≫ homPullback f W' = homPullback f W ≫ homPost C φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change f.f n ≫ (c ≫ φ) = (f.f n ≫ c) ≫ φ
  exact (Category.assoc _ _ _).symm

end Post

section Coeff

/-- The rational coefficient system `Sym^n ⊗ det^e` of `Γ(6)`. -/
abbrev polyRep (n : ℕ) (e : ℤ) : Rep.{0} ℚ Γ6 :=
  Rep.res principalSix.subtype (Rep.of (TernaryPoly.PolynomialGLAction.integralAction n e))

/-- The cochain-model coefficients of trivial character. -/
abbrev Ecoef (n : ℕ) : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  rationalCoefficientComponent n trivialCharacter

/-- **Complexification as a morphism of representations of `Γ(6)`.** -/
def complexifyHom (n : ℕ) : polyRep n (-1) ⟶ coeffRep (Ecoef n) :=
  Rep.ofHom ⟨complexify n, by
    intro γ
    apply LinearMap.ext
    intro v
    have h := rationalCoefficientComponent_integral n ⟨γ.val, principalSix_le_arithmeticLevel γ.2⟩
    have h2 := complexify_integralAction n (-1) γ.val v
    change complexify n (TernaryPoly.PolynomialGLAction.integralAction n (-1) γ.val v) =
      (Ecoef n) (iotaQ γ) (complexify n v)
    rw [h2]
    exact (congrArg (fun L => L (complexify n v)) h).symm⟩

end Coeff

section Natural

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ RationalGL3 V)

/-- The plain cocycle underlying a cocycle with values in functions on a point. -/
def unrestrictCocycle (f : cocycles N6 (functionRepresentation ρ PUnit)) : cocycles N6 ρ :=
  ⟨⟨fun x => f.1.1 x PUnit.unit, by
    intro γ x
    have h := congrFun (f.1.2 γ x) PUnit.unit
    exact h⟩, by
    have h : differentialTwo N6 (functionRepresentation ρ PUnit) f.1 = 0 := f.2
    funext x
    exact congrFun (congrFun h x) PUnit.unit⟩

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem restrictCocycle_unrestrictCocycle (f : cocycles N6 (functionRepresentation ρ PUnit)) :
    restrictCocycle ρ PUnit (unrestrictCocycle ρ f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x e
  exact congrArg (f.1.1 x) (Subsingleton.elim _ _)

/-- Every class of `H²(Γ(6); ρ)` computed on the point resolution is the class of a cocycle of `N6`. -/
theorem ptCls_surjective (y : (homK ρ (Z := PUnit)).homology 2) :
    ∃ c : cocycles N6 ρ, ptCls ρ c = y := by
  obtain ⟨f, rfl⟩ := modelCls_surjective ρ (Equiv.refl PUnit) (fun _ _ => rfl) y
  exact ⟨unrestrictCocycle ρ f, by
    unfold ptCls
    rw [restrictCocycle_unrestrictCocycle]⟩

variable {W W' : Rep.{0} ℚ Γ6} (φ : W ⟶ W')

/-- **Naturality of the geometric restriction in the coefficients.** -/
theorem homologyMap_homPost_geo (x : (homCochains (prodComplex Γ6 RationalGL3 PUnit) W).homology 2) :
    (homologyMap (homPost coneR φ) 2).hom
        ((homologyMap (homPullback coneToPt W) 2).hom x) =
      (homologyMap (homPullback coneToPt W') 2).hom
        ((homologyMap (homPost (prodComplex Γ6 RationalGL3 PUnit) φ) 2).hom x) := by
  have e : homologyMap (homPullback coneToPt W) 2 ≫ homologyMap (homPost coneR φ) 2 =
      homologyMap (homPost (prodComplex Γ6 RationalGL3 PUnit) φ) 2 ≫
        homologyMap (homPullback coneToPt W') 2 := by
    rw [← homologyMap_comp, ← homologyMap_comp, homPost_homPullback]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 e) x

theorem homologyMap_homPost_line (x : (homCochains coneR W).homology 2) :
    (homologyMap (homPullback coneLine W') 2).hom ((homologyMap (homPost coneR φ) 2).hom x) =
      (homologyMap (homPost (prodComplex Γ6 RationalGL3 Line) φ) 2).hom
        ((homologyMap (homPullback coneLine W) 2).hom x) := by
  have e : homologyMap (homPost coneR φ) 2 ≫ homologyMap (homPullback coneLine W') 2 =
      homologyMap (homPullback coneLine W) 2 ≫
        homologyMap (homPost (prodComplex Γ6 RationalGL3 Line) φ) 2 := by
    rw [← homologyMap_comp, ← homologyMap_comp, homPost_homPullback]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 e) x

theorem homologyMap_homPost_plane (x : (homCochains coneR W).homology 2) :
    (homologyMap (homPullback conePlane W') 2).hom ((homologyMap (homPost coneR φ) 2).hom x) =
      (homologyMap (homPost (prodComplex Γ6 RationalGL3 Plane) φ) 2).hom
        ((homologyMap (homPullback conePlane W) 2).hom x) := by
  have e : homologyMap (homPost coneR φ) 2 ≫ homologyMap (homPullback conePlane W') 2 =
      homologyMap (homPullback conePlane W) 2 ≫
        homologyMap (homPost (prodComplex Γ6 RationalGL3 Plane) φ) 2 := by
    rw [← homologyMap_comp, ← homologyMap_comp, homPost_homPullback]
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 e) x

end Natural

section Rational

/-- **The statements of `T0Face` for the rational coefficients `Sym^n` of `Γ(6)`.**  Let `x` be a class of
`H²(Γ(6); polyRep n (-1))` on the point resolution.  There is a cocycle `c` of the cochain model whose point
class is the complexification of `x`, and the line and plane components of the geometric restriction of `x`,
complexified, are the model coordinates `r_Q c`, `r_P c`. -/
theorem rational_face_components (n : ℕ)
    (x : (homCochains (prodComplex Γ6 RationalGL3 PUnit) (polyRep n (-1))).homology 2) :
    ∃ c : cocycles N6 (Ecoef n),
      ptCls (Ecoef n) c = (homologyMap (homPost _ (complexifyHom n)) 2).hom x ∧
      (homologyMap (homPost _ (complexifyHom n)) 2).hom
          ((homologyMap (homPullback coneLine (polyRep n (-1))) 2).hom
            ((homologyMap (homPullback coneToPt (polyRep n (-1))) 2).hom x)) =
        modelCls (Ecoef n) psiLine psiLine_smul (restrictCocycle (Ecoef n) (Flags .line) c) ∧
      (homologyMap (homPost _ (complexifyHom n)) 2).hom
          ((homologyMap (homPullback conePlane (polyRep n (-1))) 2).hom
            ((homologyMap (homPullback coneToPt (polyRep n (-1))) 2).hom x)) =
        modelCls (Ecoef n) psiPlane psiPlane_smul (restrictCocycle (Ecoef n) (Flags .plane) c) := by
  obtain ⟨c, hc⟩ := ptCls_surjective (Ecoef n)
    ((homologyMap (homPost _ (complexifyHom n)) 2).hom x)
  refine ⟨c, hc, ?_, ?_⟩
  · rw [← homologyMap_homPost_line (complexifyHom n), homologyMap_homPost_geo, ← hc]
    exact geoRestriction_line (Ecoef n) c
  · rw [← homologyMap_homPost_plane (complexifyHom n), homologyMap_homPost_geo, ← hc]
    exact geoRestriction_plane (Ecoef n) c

end Rational

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
