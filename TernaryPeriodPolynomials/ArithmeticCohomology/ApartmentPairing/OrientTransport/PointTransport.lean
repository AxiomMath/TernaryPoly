module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.OrientTransport.PointClass

@[expose] public section


/-!
# Transport of the point class from the base to the product chart

If a chain of an open set `Tt` of the symmetric space maps, along a local homeomorphism `pB` of the symmetric space to a
base `B`, to a chain whose local class at `pB p₀` is the orientation generator `oB (pB p₀)` of `B`, and if `oB` is the pushforward
of the library local orientation of the symmetric space along `pB`, then the class of the chain at `p₀` is the library
local generator of the symmetric space, hence (`localGenerator_eq_psiGenerator`) its image under the product chart `psi` has class
the Euclidean generator of `ℝ⁵` at `psi p₀`.

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

/-- The product chart as a morphism of spaces. -/
def psiHom : TopCat.of Space ⟶ TopCat.of (EuclideanSpace ℝ (Fin 5)) :=
  TopCat.ofHom ⟨psi, psi.continuous⟩

/-- The inclusion of an open subset of the symmetric space. -/
abbrev TtInc (Tt : Opens Space) : TopCat.of Tt ⟶ TopCat.of Space :=
  sInclusion (X := TopCat.of Space) (Tt : Set Space)

/-- **Transport of the point class.** -/
theorem point_class_of_orientation {B : TopCat.{0}} [T1Space B] (pB : TopCat.of Space ⟶ B)
    (hpB : IsLocalHomeomorph pB.hom) (oB : ∀ b : B, (localChains b).homology 5)
    (hgen : ∀ S : Space, oB (pB.hom S) =
      localHomeomorphMap pB.hom hpB S 5 (SymmetricSpaceLocalOrientation.localGenerator S))
    (Tt : Opens Space) (p0 : Space) (hp0 : p0 ∈ Tt) (hiso : IsolatesFiber pB.hom p0 Tt)
    (γ : singularChainGroup ℚ (TopCat.of Tt) (4 + 1))
    (hγ : (singularBoundary ℚ (TopCat.of Tt) 4).hom γ ∈
      subChainSubmodule ℚ (TopCat.of Tt) ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) 4)
    (hB' : (singularBoundary ℚ B 4).hom ((singularChainMap ℚ (TtInc Tt ≫ pB) (4 + 1)).hom γ) ∈
      subChainSubmodule ℚ B ({pB.hom p0}ᶜ : Set B) 4)
    (hB : rcls (X := B) ({pB.hom p0}ᶜ : Set B) 4
      ((singularChainMap ℚ (TtInc Tt ≫ pB) (4 + 1)).hom γ) hB' = oB (pB.hom p0))
    (hE : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ (TtInc Tt ≫ psiHom) (4 + 1)).hom γ) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4) :
    rcls (X := TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4
      ((singularChainMap ℚ (TtInc Tt ≫ psiHom) (4 + 1)).hom γ) hE =
      localGenerator 3 (psi p0) := by
  -- the class of the chain at `p₀` in the symmetric space
  have hm : Set.MapsTo (TtInc Tt).hom ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) ({p0}ᶜ : Set Space) :=
    mapsTo_punct (X := TopCat.of Tt) (Y := TopCat.of Space) (TtInc Tt) ⟨p0, hp0⟩ p0 rfl
      (fun z hz => Subtype.ext hz)
  have hS : (singularBoundary ℚ (TopCat.of Space) 4).hom
      ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ) ∈
      subChainSubmodule ℚ (TopCat.of Space) ({p0}ᶜ : Set Space) 4 :=
    push_mem (TtInc Tt) ({(⟨p0, hp0⟩ : Tt)}ᶜ : Set Tt) ({p0}ᶜ : Set Space) hm 4 hγ
  have h1 := rcls_pointExcision (X := TopCat.of Space) p0 Tt hp0 4 γ hγ hS
  have h2 := localMap_rcls (X := TopCat.of Space) pB p0 Tt hp0 hiso 4 γ hγ hB'
  have h3 : localHomeomorphMap pB.hom hpB p0 5
      (rcls (X := TopCat.of Space) ({p0}ᶜ : Set Space) 4
        ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ) hS) =
      oB (pB.hom p0) := by
    rw [localHomeomorphMap_eq pB.hom hpB p0 Tt hp0 hiso, ← h1, h2]
    exact hB
  have h4 : rcls (X := TopCat.of Space) ({p0}ᶜ : Set Space) 4
      ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ) hS =
      SymmetricSpaceLocalOrientation.localGenerator p0 := by
    apply (ModuleCat.mono_iff_injective (localHomeomorphMap pB.hom hpB p0 5)).mp inferInstance
    rw [h3, hgen]
  have hcomp : (singularChainMap ℚ (TtInc Tt ≫ psiHom) (4 + 1)).hom γ =
      (singularChainMap ℚ psiHom (4 + 1)).hom ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ) := by
    rw [singularChainMap_comp]; rfl
  have hE' : (singularBoundary ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) 4).hom
      ((singularChainMap ℚ psiHom (4 + 1)).hom ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ)) ∈
      subChainSubmodule ℚ (TopCat.of (EuclideanSpace ℝ (Fin 5))) ({psi p0}ᶜ : Set (EuclideanSpace ℝ (Fin 5))) 4 := by
    rw [← hcomp]; exact hE
  rw [rcls_congr _ _ _ _ hcomp hE hE']
  have h5 := homeo_rcls (X := TopCat.of Space) (Y := TopCat.of (EuclideanSpace ℝ (Fin 5))) psi p0 4
    ((singularChainMap ℚ (TtInc Tt) (4 + 1)).hom γ) hS hE'
  refine h5.symm.trans ?_
  rw [h4, localGenerator_eq_psiGenerator p0]
  change (chartIso psi p0).hom ((chartIso psi p0).inv (localGenerator 3 (psi p0))) = _
  rw [Iso.inv_hom_id_apply]

end TernaryPeriodPolynomials.Argument.Lemma33.OrientTransport
