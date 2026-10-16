module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ShapiroProduct
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.ProductHomologyS

@[expose] public section


/-!
# The product of the Shapiro coordinates over the orbits is an isomorphism

For the permutation resolution `R = prodResolution Γ V Z` of a `Γ`-set `Z` and any rational representation
`W` of `Γ`, the map
`H²(Hom_Γ(R, W)) ⟶ ∏_{o ∈ Z/Γ} groupCohomology (Res_{Stab(o)} W) 2`,
`x ↦ (faceCoord_o x)_o`, is bijective (`faceCoord_product_bijective_succ`): it is the composite of the
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

variable (m : ℕ) {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] (v₀ : V)
  (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (W : Rep.{0} ℚ Γ)

theorem fullShapiro_projS (o : labelOrbits Γ Z) :
    (fullShapiroIso Γ Z W).hom ≫ prodProjS (fun o : labelOrbits Γ Z =>
        homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
          (Rep.res (stabilizer Γ o.out).subtype W)) o = subCoord W o := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

include hfree in
/-- **The product of the Shapiro coordinates over the orbits is an isomorphism** (degree `m+1`). -/
theorem faceCoord_product_bijective_succ :
    Function.Bijective (fun x : (homCochains (prodComplex Γ V Z) W).homology (m+1) =>
      fun o : labelOrbits Γ Z =>
        (faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) (m+1)).hom x) := by
  let κ := stabToProd (Z := Z) v₀ hfree
  have hq : QuasiIso (homPullback κ W) :=
    homPullback_quasiIso_of_homotopyEquiv
      (comparison (stabilizerResolution Γ Z) (prodResolution Γ V Z v₀ hfree)) W
  have : QuasiIsoAt (homPullback κ W) (m+1) := inferInstance
  have e1 : Function.Bijective (HomologicalComplex.homologyMap (homPullback κ W) (m+1)).hom :=
    (isoOfQuasiIsoAt (homPullback κ W) (m+1)).toLinearEquiv.bijective
  have e2 : Function.Bijective
      (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom (m+1)).hom :=
    (HomologicalComplex.homologyMapIso (fullShapiroIso Γ Z W) (m+1)).toLinearEquiv.bijective
  have e3 := prodHomologyMapS_bijective m (fun o : labelOrbits Γ Z =>
    homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
      (Rep.res (stabilizer Γ o.out).subtype W))
  have e4 := (LinearEquiv.piCongrRight (fun o : labelOrbits Γ Z =>
    (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) (m+1)).symm.toLinearEquiv)).bijective
  have key : ∀ o : labelOrbits Γ Z,
      HomologicalComplex.homologyMap
        (stabCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2)) (m+1) =
      HomologicalComplex.homologyMap (homPullback κ W) (m+1) ≫
        (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom (m+1) ≫
          HomologicalComplex.homologyMap (prodProjS (fun o : labelOrbits Γ Z =>
            homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
              (Rep.res (stabilizer Γ o.out).subtype W)) o) (m+1)) := by
    intro o
    rw [stabCoord_homology_eq_subCoord v₀ W hfree o κ (stabToProd_aug v₀ hfree) (m+1),
      ← fullShapiro_projS, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  have hf : ∀ o : labelOrbits Γ Z,
      faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) (m+1) =
        HomologicalComplex.homologyMap
          (stabCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2)) (m+1) ≫
          (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) (m+1)).inv := by
    intro o
    unfold faceCoord fixCoordH stabCoord
    rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  have hfun : (fun x : (homCochains (prodComplex Γ V Z) W).homology (m+1) =>
      fun o : labelOrbits Γ Z =>
        (faceCoord (stabilizer Γ o.out) W v₀ o.out (fun g => g.2) (m+1)).hom x) =
      (fun y => fun o : labelOrbits Γ Z =>
        (gisoBar (Rep.res (stabilizer Γ o.out).subtype W) (m+1)).inv.hom (y o)) ∘
        (prodHomologyMapS m (fun o : labelOrbits Γ Z =>
          homCochains (Rep.barResolution ℚ (stabilizer Γ o.out)).complex
            (Rep.res (stabilizer Γ o.out).subtype W))) ∘
        (HomologicalComplex.homologyMap (fullShapiroIso Γ Z W).hom (m+1)).hom ∘
        (HomologicalComplex.homologyMap (homPullback κ W) (m+1)).hom := by
    funext x o
    rw [hf o, key o]
    rfl
  rw [hfun]
  exact e4.comp (e3.comp (e2.comp e1))

