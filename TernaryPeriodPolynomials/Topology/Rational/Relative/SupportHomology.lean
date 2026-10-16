module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportLiteral
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {X : Type} [TopologicalSpace X]

/-- The actual comparison on the first homology term. -/
def firstHomologyIso (U V : Set X) (k : ℕ) :
    (quotientChainRow U V).X₁.homology k ≅ (relativeChains (U ∩ V)).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso (firstComparisonIso U V)

/-- The actual middle homology isomorphism, including the prescribed second-component sign. -/
def middleHomologyIso (U V : Set X) (k : ℕ) :
    (quotientChainRow U V).X₂.homology k ≅ (relativeChains U).homology k ⊞ (relativeChains V).homology k :=
  (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapIso (middleComparisonIso U V) ≪≫
    (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k).mapBiprod _ _

/-- Actual small-chain excision identifies the third homology term with literal relative homology. -/
def thirdHomologyIso (U V : Opens X) (k : ℕ) :
    (quotientChainRow (U : Set X) (V : Set X)).X₃.homology k ≅
      (relativeChains ((U : Set X) ∪ V)).homology k := by
  change (cokernel (supportedSmallSumInclusion (U : Set X) (V : Set X))).homology k ≅ _
  have : QuasiIso (smallRelativeComparison (U : Set X) (V : Set X)) := smallRelativeComparison_quasiIso U V
  have : IsIso (homologyMap (smallRelativeComparison (U : Set X) (V : Set X)) k) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact asIso (homologyMap (smallRelativeComparison (U : Set X) (V : Set X)) k)

/-- The literal unsigned restriction pair on rational relative homology. -/
def homologyRestrictionPair (U V : Set X) (k : ℕ) :
    (relativeChains (U ∩ V)).homology k ⟶ (relativeChains U).homology k ⊞ (relativeChains V).homology k :=
  biprod.lift (homologyMap (relativeInclusion (U ∩ V) U Set.inter_subset_left) k)
    (homologyMap (relativeInclusion (U ∩ V) V Set.inter_subset_right) k)

/-- The literal difference of restriction maps on rational relative homology. -/
def homologyRestrictionDifference (U V : Set X) (k : ℕ) :
    (relativeChains U).homology k ⊞ (relativeChains V).homology k ⟶ (relativeChains (U ∪ V)).homology k :=
  biprod.desc (homologyMap (relativeInclusion U (U ∪ V) Set.subset_union_left) k)
    (-(homologyMap (relativeInclusion V (U ∪ V) Set.subset_union_right) k))

/-- Homology carries the first chain comparison to the literal restriction-pair square. -/
theorem firstHomology_comm (U V : Set X) (k : ℕ) :
    homologyMap (quotientChainRow U V).f k ≫ (middleHomologyIso U V k).hom =
      (firstHomologyIso U V k).hom ≫ homologyRestrictionPair U V k := by
  let F := homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k
  change F.map _ ≫ F.map _ ≫ (F.mapBiprod _ _).hom = F.map _ ≫ _
  rw [← Category.assoc, ← F.map_comp, firstComparison_comm, F.map_comp, Category.assoc]
  congr 1
  exact biprod.map_lift_mapBiprod F _ _ _ _

/-- Homology carries the second chain comparison to the literal difference square. -/
theorem middleHomology_comm (U V : Opens X) (k : ℕ) :
    homologyMap (quotientChainRow (U : Set X) (V : Set X)).g k ≫ (thirdHomologyIso U V k).hom =
      (middleHomologyIso (U : Set X) (V : Set X) k).hom ≫ homologyRestrictionDifference (U : Set X) (V : Set X) k := by
  let F := homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) k
  change F.map _ ≫ F.map _ = (F.map _ ≫ (F.mapBiprod _ _).hom) ≫ _
  erw [← F.map_comp, middleComparison_comm (U : Set X) (V : Set X), F.map_comp, Category.assoc]
  congr 1
  simpa only [restrictionDifference, homologyRestrictionDifference, F, homologyFunctor, homologyMap_neg] using
    (biprod.mapBiprod_hom_desc F (relativeChains (U : Set X)) (relativeChains (V : Set X))
      (relativeInclusion (U : Set X) ((U : Set X) ∪ V) Set.subset_union_left)
      (-(relativeInclusion (V : Set X) ((U : Set X) ∪ V) Set.subset_union_right))).symm

end TernaryPoly.RationalRelativeSupport
