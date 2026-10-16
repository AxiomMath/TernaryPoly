module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointTransport

@[expose] public section


/-!
# The point class of a localized chain

`cY_pointClass`: let `c` be a chain of the base `B` whose local class at `b₀ = pB p₀` is the orientation generator `oB b₀`, and let
`cY` be a chain of a chart `Y` (with a section `sec : Y ⟶ Space` into an open set `Tt` isolating the fibre) such that
`c = ι_# cY + cA + cB + ∂u` with `cA` over `UA`, `cB` over `UB`, `b₀ ∉ UA ∪ UB`, and `∂ cY` over `ι⁻¹ UA` and `ι⁻¹ UB`.  Then the chain
`(sec ≫ psi)_# cY` of `ℝ⁵` has class the Euclidean generator at `psi p₀`.

Formalized by Claude Sonnet 5.5.
-/

open SphereOddDegree SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace
open TernaryPeriodPolynomials.Argument.Lemma33.Locality
open TernaryPoly TernaryPoly.EuclideanLocalHomology TernaryPoly.ContractibleSingularHomology
  TernaryPoly.RationalRelativeSingular TernaryPoly.RationalManifoldCompact
  TernaryPoly.RationalLocalChartHomology TernaryPoly.RationalRelativeExcision TernaryPoly.RationalLocalMap
  TernaryPoly.RationalSingularAugmentation TernaryPoly.RationalLocalOrientation
open TernaryPoly.SingularLocalCap.Descent
open TernaryPoly.SymmetricSpacePositive

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport

theorem cY_pointClass {B : TopCat.{0}} [T1Space B] (pB : TopCat.of Space ⟶ B)
    (hpB : IsLocalHomeomorph pB.hom) (oB : ∀ b : B, (localChains b).homology 5)
    (hgen : ∀ S : Space, oB (pB.hom S) =
      localHomeomorphMap pB.hom hpB S 5 (SymmetricSpaceLocalOrientation.localGenerator S))
    (Tt : Opens Space) (p0 : Space) (hp0 : p0 ∈ Tt) (hiso : IsolatesFiber pB.hom p0 Tt)
    {Y : TopCat.{0}} (ιY : Y ⟶ B) (sec : Y ⟶ TopCat.of Space) (hsec : sec ≫ pB = ιY)
    (hom : Y ⟶ TopCat.of Tt) (hhom : hom ≫ TtInc Tt = sec)
    (UA UB : Set B) (hb0A : pB.hom p0 ∉ UA) (hb0B : pB.hom p0 ∉ UB)
    (c : singularChainGroup ℚ B (4 + 1)) (cY : singularChainGroup ℚ Y (4 + 1))
    (cA cB : singularChainGroup ℚ B (4 + 1)) (hcA : cA ∈ subChainSubmodule ℚ B UA (4 + 1))
    (hcB : cB ∈ subChainSubmodule ℚ B UB (4 + 1)) (u : singularChainGroup ℚ B (4 + 2))
    (hdec : c = (singularChainMap ℚ ιY (4 + 1)).hom cY + cA + cB + (singularBoundary ℚ B (4 + 1)).hom u)
    (aY bY : singularChainGroup ℚ Y 4) (haY : aY ∈ subChainSubmodule ℚ Y (ιY.hom ⁻¹' UA) 4)
    (hbY : bY ∈ subChainSubmodule ℚ Y (ιY.hom ⁻¹' UB) 4)
    (hbd : (singularBoundary ℚ Y 4).hom cY = aY + bY)
    (hcb : (singularBoundary ℚ B 4).hom c ∈ subChainSubmodule ℚ B ({pB.hom p0}ᶜ : Set B) 4)
    (hc0 : rcls (X := B) ({pB.hom p0}ᶜ : Set B) 4 c hcb = oB (pB.hom p0))
    (hE : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ (sec ≫ psiHom) (4 + 1)).hom cY) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4) :
    rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
      ((singularChainMap ℚ (sec ≫ psiHom) (4 + 1)).hom cY) hE = localGenerator 3 (psi p0) := by
  -- the chain of the neighbourhood `Tt`
  have hmapT : Set.MapsTo (TtInc Tt ≫ pB).hom ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) ({pB.hom p0}ᶜ : Set B) :=
    mapsTo_punct (X := TopCat.of Tt) (Y := B) (TtInc Tt ≫ pB) ⟨p0, hp0⟩ (pB.hom p0) rfl
      (fun z hz => Subtype.ext (hiso z.val z.property hz))
  have hmapE : Set.MapsTo (TtInc Tt ≫ psiHom).hom ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt)
      ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) :=
    mapsTo_punct (X := TopCat.of Tt) (Y := TopCat.of (EuclideanSpace ℝ (Fin 5))) (TtInc Tt ≫ psiHom)
      ⟨p0, hp0⟩ (psi p0) rfl (fun z hz => Subtype.ext (psi.injective hz))
  set γ : singularChainGroup ℚ (TopCat.of Tt) (4 + 1) := (singularChainMap ℚ hom (4 + 1)).hom cY with hγdef
  have hpush : ∀ {W : TopCat.{0}} (g : TopCat.of Tt ⟶ W),
      (singularChainMap ℚ g (4 + 1)).hom γ = (singularChainMap ℚ (hom ≫ g) (4 + 1)).hom cY := by
    intro W g
    rw [hγdef, singularChainMap_comp]; rfl
  have hsub : ιY.hom ⁻¹' UA ⊆ hom.hom ⁻¹' ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) ∧
      ιY.hom ⁻¹' UB ⊆ hom.hom ⁻¹' ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) := by
    have key : ∀ y, hom.hom y = ⟨p0, hp0⟩ → ιY.hom y = pB.hom p0 := by
      intro y hy
      have h1 : sec.hom y = p0 := by
        rw [← hhom]; exact congrArg Subtype.val hy
      rw [← hsec]
      exact congrArg pB.hom h1
    constructor
    · intro y hy hy'
      exact hb0A (key y hy' ▸ hy)
    · intro y hy hy'
      exact hb0B (key y hy' ▸ hy)
  have hγ : (singularBoundary ℚ (TopCat.of Tt) 4).hom γ ∈
      subChainSubmodule ℚ (TopCat.of Tt) ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) 4 := by
    have h1 := singularChainMap_boundary_apply ℚ hom 4 cY
    have h2 : (singularBoundary ℚ (TopCat.of Tt) 4).hom γ =
        (singularChainMap ℚ hom 4).hom ((singularBoundary ℚ Y 4).hom cY) := h1
    rw [h2, hbd, map_add]
    exact Submodule.add_mem _
      (singularChainMap_mem_sub hom _ 4 (subChainSubmodule_mono hsub.1 4 haY))
      (singularChainMap_mem_sub hom _ 4 (subChainSubmodule_mono hsub.2 4 hbY))
  have hB' := push_mem (TtInc Tt ≫ pB) _ _ hmapT 4 hγ
  have hcT : (singularChainMap ℚ (TtInc Tt ≫ pB) (4 + 1)).hom γ =
      (singularChainMap ℚ ιY (4 + 1)).hom cY := by
    rw [hpush, ← Category.assoc, hhom, hsec]
  -- the class of the localized chain agrees with that of `c`
  have hB : rcls (X := B) ({pB.hom p0}ᶜ : Set B) 4
      ((singularChainMap ℚ (TtInc Tt ≫ pB) (4 + 1)).hom γ) hB' = oB (pB.hom p0) := by
    rw [← hc0]
    have hUA' : UA ⊆ ({pB.hom p0}ᶜ : Set B) := by
      intro z hz hz0
      apply hb0A
      rw [← Set.mem_singleton_iff.mp hz0]
      exact hz
    have hUB' : UB ⊆ ({pB.hom p0}ᶜ : Set B) := by
      intro z hz hz0
      apply hb0B
      rw [← Set.mem_singleton_iff.mp hz0]
      exact hz
    have hw : cA + cB ∈ subChainSubmodule ℚ B ({pB.hom p0}ᶜ : Set B) (4 + 1) :=
      Submodule.add_mem _ (subChainSubmodule_mono hUA' _ hcA) (subChainSubmodule_mono hUB' _ hcB)
    refine (rcls_eq_of_decomp (X := B) ({pB.hom p0}ᶜ : Set B) 4 c _ hcb hB' (cA + cB) hw u ?_).symm
    rw [hcT, hdec]; abel
  have hE'' := push_mem (TtInc Tt ≫ psiHom) _ _ hmapE 4 hγ
  have key := point_class_of_orientation pB hpB oB hgen Tt p0 hp0 hiso γ hγ hB' hB hE''
  have hcomp : (singularChainMap ℚ (TtInc Tt ≫ psiHom) (4 + 1)).hom γ =
      (singularChainMap ℚ (sec ≫ psiHom) (4 + 1)).hom cY := by
    rw [hpush, ← Category.assoc, hhom]
  rw [rcls_congr _ _ _ _ hcomp hE'' hE] at key
  exact key

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
