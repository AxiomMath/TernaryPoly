module

public import TernaryPeriodPolynomials.Topology.ContractibleSingularHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSingularAugmentation
open CategoryTheory Limits AlgebraicTopology HomologicalComplex ContractibleSingularHomology

/-- The actual rational singular chain map induced by a continuous map. -/
abbrev chainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) :
    chains X ⟶ chains Y :=
  ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of.{0} ℚ ℚ)).map
    (TopCat.ofHom f)

@[simp] theorem chainMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X,Y)) (g : C(Y,Z)) :
    chainMap (g.comp f) = chainMap f ≫ chainMap g :=
  Functor.map_comp _ _ _

@[simp] theorem chainMap_id (X : Type) [TopologicalSpace X] :
    chainMap (ContinuousMap.id X) = 𝟙 (chains X) := CategoryTheory.Functor.map_id _ _

/-- Augmentation is induced by the literal map to a point and the actual point H0
augmentation isomorphism. -/
def augmentation (X : Type) [TopologicalSpace X] :
    (chains X).homology 0 ⟶ ModuleCat.of.{0} ℚ ℚ :=
  homologyMap (chainMap (ContinuousMap.const X ())) 0 ≫
    (homologyZeroIso (X := Unit)).hom

/-- The augmentation is natural for every actual continuous map. -/
theorem naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) :
    homologyMap (chainMap f) 0 ≫ augmentation Y = augmentation X := by
  unfold augmentation
  rw [← Category.assoc, ← homologyMap_comp, ← chainMap_comp]

/-- A genuine homotopy equivalence preserves the augmentation. -/
theorem homotopyEquiv_naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ((chainHomotopyEquiv e).toHomologyIso 0).hom ≫ augmentation Y = augmentation X :=
  naturality e.toFun

/-- Every nonempty space has surjective actual augmentation: a point supplies a section. -/
theorem augmentation_surjective (X : Type) [TopologicalSpace X] [Nonempty X] :
    Function.Surjective (augmentation X).hom := by
  let f : C(Unit, X) := ContinuousMap.const Unit (Classical.arbitrary X)
  have h : homologyMap (chainMap f) 0 ≫ augmentation X =
      (homologyZeroIso (X := Unit)).hom := by
    rw [naturality]
    simp [augmentation, show ContinuousMap.const Unit () = ContinuousMap.id Unit from by ext]
  have hs : Function.Surjective (homologyZeroIso (X := Unit)).hom.hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  intro q
  obtain ⟨u, hu⟩ := hs q
  exact ⟨homologyMap (chainMap f) 0 u, (congrArg (fun g => g u) h).trans hu⟩

/-- The actual augmentation is an isomorphism for contractible spaces. -/
instance augmentation_isIso (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsIso (augmentation X) := by
  let e := (ContractibleSpace.hequiv_unit X).some
  have he : e.toFun = ContinuousMap.const X () := by ext
  have h : augmentation X = ((chainHomotopyEquiv e).toHomologyIso 0).hom ≫
      (homologyZeroIso (X := Unit)).hom := by
    change homologyMap (chainMap (ContinuousMap.const X ())) 0 ≫ _ =
      homologyMap (chainMap e.toFun) 0 ≫ _
    rw [he]
  rw [h]
  infer_instance

end TernaryPoly.RationalSingularAugmentation
