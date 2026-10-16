module

public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.RestrictionBar
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.RestrictionComparison
public import TernaryPeriodPolynomials.Topology.Rational.Cohomology.Descent

@[expose] public section


noncomputable section

namespace TernaryPoly.RationalCohomologyRestriction
open CategoryTheory Rep Finsupp
open RationalCohomologyDescent

variable {G : Type} [Group G] (H : Subgroup G) (A : Rep.{0} ℚ G)

/-- The canonical comparison to the restricted bar resolution is inverted by
precomposition with the literal subgroup-bar inclusion. -/
theorem subgroup_resolution_comparison (n : ℕ) :
    (groupCohomologyIso (Rep.res H.subtype A) n
      ((Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℚ G))).hom ≫
        HomologicalComplex.homologyMap
          (resolutionPrecomp (barInclusion H) (Rep.res H.subtype A)) n =
      HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso (Rep.res H.subtype A)).hom n := by
  let P := Rep.barResolution ℚ H
  let Q : ProjectiveResolution (Rep.trivial ℚ H ℚ) := (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)
  let B := Rep.res H.subtype A
  have h := isoExt_precomp P Q (barInclusion H) (barInclusion_augmentation H) B n
  let I : groupCohomology B n ≅ (P.complex.linearYonedaObj ℚ B).homology n :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (groupCohomology.inhomogeneousCochainsIso B)
  let t : (Q.complex.linearYonedaObj ℚ B).homology n ⟶
      (P.complex.linearYonedaObj ℚ B).homology n :=
    HomologicalComplex.homologyMap (resolutionPrecomp (barInclusion H) B) n
  have hc : ((I.hom ≫ (P.isoExt n B).inv) ≫ (Q.isoExt n B).hom) ≫ t = I.hom := by
    rw [Category.assoc, Category.assoc, h, Iso.inv_hom_id, Category.comp_id]
  exact hc

/-- On literal bar generators, the coinduction unit followed by the adjunction
counit and subgroup-bar inclusion is the ordinary restriction of cochains. -/
theorem coindUnit_cochain_comparison :
    groupCohomology.cochainsMap (MonoidHom.id G) (coindUnit H A) ≫
      (groupCohomology.inhomogeneousCochainsIso
        (Rep.coind H.subtype (Rep.res H.subtype A))).hom ≫
      (groupCohomology.linearYonedaObjResProjectiveResolutionIso
        (Rep.barResolution ℚ G) (Rep.res H.subtype A)).inv ≫
      resolutionPrecomp (barInclusion H) (Rep.res H.subtype A) =
    groupCohomology.cochainsMap H.subtype (𝟙 _) ≫
      (groupCohomology.inhomogeneousCochainsIso (Rep.res H.subtype A)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((Fin n → G) → A) at z
  change barInclusionF H n ≫
      (Rep.resCoindHomEquiv.{0} H.subtype (Rep.free ℚ G (Fin n → G))
        (Rep.res H.subtype A)).symm
          (Rep.freeLift ℚ G _ (fun y => (coindUnit H A).hom (z y))) =
    Rep.freeLift ℚ H _ (fun y => z (H.subtype ∘ y))
  apply Rep.free_ext
  intro x
  change ((Rep.resCoindHomEquiv.{0} H.subtype (Rep.free ℚ G (Fin n → G))
      (Rep.res H.subtype A)).symm
        (Rep.freeLift ℚ G _ (fun y => (coindUnit H A).hom (z y)))).hom
          ((barInclusionF H n).hom (single x (MonoidAlgebra.single (1 : H) 1))) = _
  rw [barInclusionF_single]
  simp [Rep.resCoindHomEquiv, Rep.freeLift]
  change A.ρ 1 (z (H.subtype ∘ x)) = z (H.subtype ∘ x)
  simp only [map_one, Module.End.one_apply]

/-- Ordinary restriction is exactly the coinduction unit followed by Mathlib's
Shapiro isomorphism, in every degree. -/
theorem restriction_eq_coind_shapiro (n : ℕ) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) n =
      groupCohomology.map (MonoidHom.id G) (coindUnit H A) n ≫
        (groupCohomology.coindIso (Rep.res H.subtype A) n).hom := by
  let B := Rep.res H.subtype A
  let Q : ProjectiveResolution (Rep.trivial ℚ H ℚ) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)
  let E : groupCohomology B n ≅ (Q.complex.linearYonedaObj ℚ B).homology n :=
    groupCohomologyIso B n Q
  let V : groupCohomology B n ≅
      ((Rep.barResolution ℚ H).complex.linearYonedaObj ℚ B).homology n :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (groupCohomology.inhomogeneousCochainsIso B)
  let t : (Q.complex.linearYonedaObj ℚ B).homology n ⟶
      ((Rep.barResolution ℚ H).complex.linearYonedaObj ℚ B).homology n :=
    HomologicalComplex.homologyMap (resolutionPrecomp (barInclusion H) B) n
  let s : groupCohomology (Rep.coind H.subtype B) n ⟶
      (Q.complex.linearYonedaObj ℚ B).homology n :=
    HomologicalComplex.homologyMap
      ((groupCohomology.inhomogeneousCochainsIso (Rep.coind H.subtype B)).hom ≫
        (groupCohomology.linearYonedaObjResProjectiveResolutionIso
          (Rep.barResolution ℚ G) B).inv) n
  let u : groupCohomology A n ⟶ groupCohomology (Rep.coind H.subtype B) n :=
    groupCohomology.map (MonoidHom.id G) (coindUnit H A) n
  let r : groupCohomology A n ⟶ groupCohomology B n :=
    groupCohomology.map H.subtype (𝟙 B) n
  have hv : E.hom ≫ t = V.hom := subgroup_resolution_comparison H A n
  have hc : (u ≫ s) ≫ t = r ≫ V.hom := by
    let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n
    let C := groupCohomology.inhomogeneousCochains A
    let D := groupCohomology.inhomogeneousCochains (Rep.coind H.subtype B)
    let L := (Rep.barResolution ℚ G).complex.linearYonedaObj ℚ (Rep.coind H.subtype B)
    let Z := Q.complex.linearYonedaObj ℚ B
    let Y := (Rep.barResolution ℚ H).complex.linearYonedaObj ℚ B
    let CB := groupCohomology.inhomogeneousCochains B
    let c₁ : C ⟶ D := groupCohomology.cochainsMap (MonoidHom.id G) (coindUnit H A)
    let c₂ : D ⟶ L := (groupCohomology.inhomogeneousCochainsIso (Rep.coind H.subtype B)).hom
    let c₃ : L ⟶ Z := (groupCohomology.linearYonedaObjResProjectiveResolutionIso
      (Rep.barResolution ℚ G) B).inv
    let c₄ : Z ⟶ Y := resolutionPrecomp (barInclusion H) B
    let d₁ : C ⟶ CB := groupCohomology.cochainsMap H.subtype (𝟙 B)
    let d₂ : CB ⟶ Y := (groupCohomology.inhomogeneousCochainsIso B).hom
    have hchain : c₁ ≫ c₂ ≫ c₃ ≫ c₄ = d₁ ≫ d₂ := coindUnit_cochain_comparison H A
    have h := congrArg F.map hchain
    simp only [CategoryTheory.Functor.map_comp] at h
    have he : (F.map c₁ ≫ F.map (c₂ ≫ c₃)) ≫ F.map c₄ = F.map d₁ ≫ F.map d₂ := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
      exact h
    exact he
  have ht : E.inv ≫ V.hom = t := by
    rw [← hv, Iso.inv_hom_id_assoc]
  have hcalc : r = (u ≫ s) ≫ E.inv := by
    apply (cancel_mono V.hom).mp
    rw [Category.assoc, ht]
    exact hc.symm
  exact hcalc.trans (Category.assoc u s E.inv)

end TernaryPoly.RationalCohomologyRestriction
