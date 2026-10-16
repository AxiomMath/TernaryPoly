module

public import TernaryPeriodPolynomials.SymmetricSpace.CoordinateIsotopy
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.OrientationNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceLocalOrientation
open CategoryTheory Limits HomologicalComplex
open SymmetricSpacePositive SymmetricSpaceEuclideanCoordinates
open RationalRelativeSingular RationalSingularAugmentation

/-- The literal local chains of the actual positive-form space at S. -/
abbrev localChainsAt (S : Space) := relativeChains ({S}ᶜ : Set Space)

/-- The global coordinate homeomorphism induces the actual local chain isomorphism. -/
def coordinateLocalIso (S : Space) :
    localChainsAt S ≅ EuclideanLocalHomology.localChainsAt 5 (spaceHomeomorph S) :=
  relativeHomeomorphIso spaceHomeomorph {S}ᶜ {spaceHomeomorph S}ᶜ (by
    intro T
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, spaceHomeomorph.injective.eq_iff])

/-- The genuine degree-five local homology comparison with the fixed Euclidean coordinates. -/
def coordinateLocalHomologyIso (S : Space) :
    (localChainsAt S).homology 5 ≅
      (EuclideanLocalHomology.localChainsAt 5 (spaceHomeomorph S)).homology 5 :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) 5).mapIso (coordinateLocalIso S)

/-- The actual nonzero local generator selected by the global Euclidean coordinates. -/
def localGenerator (S : Space) : (localChainsAt S).homology 5 :=
  (coordinateLocalHomologyIso S).inv (EuclideanLocalHomology.localGenerator 3 (spaceHomeomorph S))

theorem localGenerator_ne_zero (S : Space) : localGenerator S ≠ 0 := by
  intro h
  have hh := congrArg (fun z => (coordinateLocalHomologyIso S).hom z) h
  have hzero : EuclideanLocalHomology.localGenerator 3 (spaceHomeomorph S) = 0 := by
    simpa [localGenerator] using hh
  exact EuclideanLocalHomology.localGenerator_ne_zero 3 (spaceHomeomorph S) hzero

/-- The literal point-local map of the normalized real matrix action. -/
def actionLocalMap (g : RealGL) (S : Space) : localChainsAt S ⟶ localChainsAt (act g S) :=
  relativeMap (actionHomeomorph g).toHomotopyEquiv.toFun {S}ᶜ {act g S}ᶜ (by
    intro T hT
    exact fun he => hT ((actionHomeomorph g).injective he))

/-- The corresponding literal map of pairs in global Euclidean coordinates. -/
def coordinateRelativeMap (g : RealGL) (S : Space) :
    EuclideanLocalHomology.localChainsAt 5 (spaceHomeomorph S) ⟶
      EuclideanLocalHomology.localChainsAt 5 (spaceHomeomorph (act g S)) :=
  relativeMap (coordinateAction g).toHomotopyEquiv.toFun {spaceHomeomorph S}ᶜ
    {spaceHomeomorph (act g S)}ᶜ (by
      intro z hz
      change z ≠ spaceHomeomorph S at hz
      change coordinateAction g z ≠ spaceHomeomorph (act g S)
      rw [← show coordinateAction g (spaceHomeomorph S) = spaceHomeomorph (act g S) by simp]
      exact (coordinateAction g).injective.ne hz)

/-- The actual coordinate square commutes already on literal local chain complexes. -/
theorem actionLocalMap_coordinate (g : RealGL) (S : Space) :
    actionLocalMap g S ≫ (coordinateLocalIso (act g S)).hom =
      (coordinateLocalIso S).hom ≫ coordinateRelativeMap g S := by
  simp only [actionLocalMap, coordinateLocalIso, relativeHomeomorphIso_hom, coordinateRelativeMap]
  apply (cancel_epi (cokernel.π (inclusion ({S}ᶜ : Set Space)))).mp
  simp only [relativeMap, cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, ← chainMap_comp, ← Category.assoc, ← chainMap_comp]
  congr 2
  ext z
  simp [coordinateAction_apply, actionHomeomorph]

/-- The actual coordinate pair map carries the selected Euclidean local generators correctly. -/
theorem coordinateRelativeMap_generator {g : RealGL} (p : Path 1 g) (S : Space) :
    homologyMap (coordinateRelativeMap g S) 5
      (EuclideanLocalHomology.localGenerator 3 (spaceHomeomorph S)) =
      EuclideanLocalHomology.localGenerator 3 (spaceHomeomorph (act g S)) := by
  have hf : (coordinateAction g).toHomotopyEquiv.toFun (spaceHomeomorph S) =
      spaceHomeomorph (act g S) := by
    change spaceHomeomorph (act g (spaceHomeomorph.symm (spaceHomeomorph S))) = _
    rw [spaceHomeomorph.symm_apply_apply]
  exact EuclideanLocalHomology.pairMap_generator 3
    (coordinateAction g).toHomotopyEquiv.toFun (coordinateAction g).injective
    (coordinateActionHomotopy p) (coordinateActionHomotopy_injective p)
    (spaceHomeomorph S) (spaceHomeomorph (act g S)) hf _

/-- A path from identity in the real matrix group preserves the actual local homology
orientation generators of the positive-form space. -/
theorem actionLocalMap_generator {g : RealGL} (p : Path 1 g) (S : Space) :
    homologyMap (actionLocalMap g S) 5 (localGenerator S) = localGenerator (act g S) := by
  apply (ModuleCat.mono_iff_injective (coordinateLocalHomologyIso (act g S)).hom).mp inferInstance
  have h := congrArg (fun a => homologyMap a 5) (actionLocalMap_coordinate g S)
  rw [homologyMap_comp, homologyMap_comp] at h
  have hc : homologyMap (actionLocalMap g S) 5 ≫ (coordinateLocalHomologyIso (act g S)).hom =
      (coordinateLocalHomologyIso S).hom ≫ homologyMap (coordinateRelativeMap g S) 5 := h
  have hh := congrArg (fun a => a (localGenerator S)) hc
  have hg := coordinateRelativeMap_generator p S
  have hh' : (coordinateLocalHomologyIso (act g S)).hom
      (homologyMap (actionLocalMap g S) 5 (localGenerator S)) =
      homologyMap (coordinateRelativeMap g S) 5
        (EuclideanLocalHomology.localGenerator 3 (spaceHomeomorph S)) := by
    simpa [localGenerator] using hh
  simpa [localGenerator] using hh'.trans hg

end TernaryPoly.SymmetricSpaceLocalOrientation
