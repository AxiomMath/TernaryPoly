module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroAgreement
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProductHomology

@[expose] public section


/-!
# The product of the Shapiro coordinates over the orbits is an isomorphism

For the permutation resolution `R = prodResolution Γ V Z` of a `Γ`-set `Z` and any rational representation
`W` of `Γ`, the map
`H²(Hom_Γ(R, W)) ⟶ ∏_{o ∈ Z/Γ} groupCohomology (Res_{Stab(o)} W) 2`,
`x ↦ (faceCoord_o x)_o`, is bijective (`faceCoord_product_bijective`): it is the composite of the
isomorphisms induced by the library's comparison of the stabilizer resolution with `R`, by
`fullShapiroIso`, by the identification of `H²` of a product, and by `groupCohomologyIso`, and by
`stabCoord_homology_eq_subCoord` each of its coordinates is `faceCoord`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits Finsupp
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPoly.BoundaryFaceResolutionComparison TernaryPoly.EquivariantSingularSmall

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (v₀ : V)
  (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (W : Rep.{0} ℚ Γ)

/-- The comparison chain map from the library's stabilizer resolution to the permutation resolution. -/
def stabToProd : (stabilizerResolution Γ Z).complex ⟶ prodComplex Γ V Z :=
  (comparison (stabilizerResolution Γ Z) (prodResolution Γ V Z v₀ hfree)).hom

theorem stabToProd_aug :
    (stabToProd (Z := Z) v₀ hfree).f 0 ≫ (prodResolution Γ V Z v₀ hfree).π.f 0 =
      (stabilizerResolution Γ Z).π.f 0 := by
  have h := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.ofMulAction ℚ Γ Z))
    (stabilizerResolution Γ Z) (prodResolution Γ V Z v₀ hfree)
  exact h.trans (Category.comp_id _)

theorem fullShapiro_proj (o : labelOrbits Γ Z) :
    (fullShapiroIso Γ Z W).hom ≫ prodProj (fun o : labelOrbits Γ Z =>
        homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
          (Rep.res (stabilizer Γ o.out).subtype W)) o = subCoord W o := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

include hfree in
/-- **The product of the Shapiro coordinates over the orbits is an isomorphism** (degree two). -/
theorem faceCoord_product_bijective :
    Function.Bijective (fun x : (homCochains (prodComplex Γ V Z) W).homology 2 =>
      fun o : labelOrbits Γ Z =>
        (faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) 2).hom x) := by
  let κ := stabToProd (Z := Z) v₀ hfree
  have hq : QuasiIso (homPullback κ W) :=
    homPullback_quasiIso_of_homotopyEquiv
      (comparison (stabilizerResolution Γ Z) (prodResolution Γ V Z v₀ hfree)) W
  have : QuasiIsoAt (homPullback κ W) 2 := inferInstance
  have e1 : Function.Bijective (HomologicalComplex.homologyMap (homPullback κ W) 2).hom :=
    (isoOfQuasiIsoAt (homPullback κ W) 2).toLinearEquiv.bijective
  have e2 : Function.Bijective
      (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom 2).hom :=
    (HomologicalComplex.homologyMapIso (fullShapiroIso Γ Z W) 2).toLinearEquiv.bijective
  have e3 := prodHomologyMap_bijective (fun o : labelOrbits Γ Z =>
    homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
      (Rep.res (stabilizer Γ o.out).subtype W))
  have e4 := (LinearEquiv.piCongrRight (fun o : labelOrbits Γ Z =>
    (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) 2).symm.toLinearEquiv)).bijective
  have key : ∀ o : labelOrbits Γ Z,
      HomologicalComplex.homologyMap
        (stabCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2)) 2 =
      HomologicalComplex.homologyMap (homPullback κ W) 2 ≫
        (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom 2 ≫
          HomologicalComplex.homologyMap (prodProj (fun o : labelOrbits Γ Z =>
            homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
              (Rep.res (stabilizer Γ o.out).subtype W)) o) 2) := by
    intro o
    rw [stabCoord_homology_eq_subCoord v₀ W hfree o κ (stabToProd_aug v₀ hfree) 2,
      ← fullShapiro_proj, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have hf : ∀ o : labelOrbits Γ Z,
      faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) 2 =
        HomologicalComplex.homologyMap
          (stabCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2)) 2 ≫
          (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) 2).inv := by
    intro o
    unfold faceCoord fixCoordH stabCoord
    rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  have hfun : (fun x : (homCochains (prodComplex Γ V Z) W).homology 2 =>
      fun o : labelOrbits Γ Z =>
        (faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) 2).hom x) =
      (fun y => fun o : labelOrbits Γ Z =>
        (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) 2).inv.hom (y o)) ∘
        (prodHomologyMap (fun o : labelOrbits Γ Z =>
          homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
            (Rep.res (stabilizer Γ o.out).subtype W))) ∘
        (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom 2).hom ∘
        (HomologicalComplex.homologyMap (homPullback κ W) 2).hom := by
    funext x o
    rw [hf o, key o]
    rfl
  rw [hfun]
  exact e4.comp (e3.comp (e2.comp e1))

