module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportComparison

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual relative chain map associated to inclusion of the excluded subspace. -/
def relativeInclusion (S T : Set X) (hST : S ⊆ T) : relativeChains S ⟶ relativeChains T :=
  relativeMap (ContinuousMap.id X) S T hST

/-- Literal relative inclusions preserve the absolute quotient projection. -/
theorem relativeInclusion_projection (S T : Set X) (hST : S ⊆ T) :
    cokernel.π (inclusion S) ≫ relativeInclusion S T hST = cokernel.π (inclusion T) := by
  simp [relativeInclusion, relativeMap, cokernel.map, RationalSingularAugmentation.chainMap_id]

/-- Negation on a categorical object is a literal involutive automorphism. -/
def negativeIso {C : Type*} [Category C] [Preadditive C] (M : C) : M ≅ M where
  hom := -(𝟙 M)
  inv := -(𝟙 M)
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The first quotient is the literal relative complex of the intersection of exclusions. -/
def firstComparisonIso (U V : Set X) :
    (quotientChainRow U V).X₁ ≅ relativeChains (U ∩ V) := supportedRelativeIso (U ∩ V)

/-- The middle comparison changes the second sign so that restrictions are unsigned. -/
def middleComparisonIso (U V : Set X) :
    (quotientChainRow U V).X₂ ≅ relativeChains U ⊞ relativeChains V :=
  cokernelBiprodIso (supportedInclusion U) (supportedInclusion V) ≪≫
    biprod.mapIso (supportedRelativeIso U) (supportedRelativeIso V) ≪≫
      biprod.mapIso (Iso.refl _) (negativeIso _)

/-- The signed middle comparison sends absolute pairs to their literal relative quotients. -/
theorem middleComparisonIso_projection (U V : Set X) :
    cokernel.π (biprod.map (supportedInclusion U) (supportedInclusion V)) ≫
      (middleComparisonIso U V).hom =
        biprod.map (cokernel.π (inclusion U)) (-(cokernel.π (inclusion V))) := by
  change cokernel.π _ ≫ (cokernelBiprodIso (supportedInclusion U) (supportedInclusion V)).hom ≫
    (biprod.mapIso (supportedRelativeIso U) (supportedRelativeIso V)).hom ≫
      (biprod.mapIso (Iso.refl _) (negativeIso _)).hom = _
  rw [← Category.assoc, cokernelBiprodIso_projection]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [biprod.mapIso_hom, Category.assoc, supportedRelativeIso_projection, negativeIso]

/-- The actual unsigned pair of restrictions. -/
def restrictionPair (U V : Set X) : relativeChains (U ∩ V) ⟶ relativeChains U ⊞ relativeChains V :=
  biprod.lift (relativeInclusion (U ∩ V) U Set.inter_subset_left)
    (relativeInclusion (U ∩ V) V Set.inter_subset_right)

/-- The actual difference of restriction maps. -/
def restrictionDifference (U V : Set X) : relativeChains U ⊞ relativeChains V ⟶ relativeChains (U ∪ V) :=
  biprod.desc (relativeInclusion U (U ∪ V) Set.subset_union_left)
    (-(relativeInclusion V (U ∪ V) Set.subset_union_right))

/-- The first quotient map transports to the literal unsigned restriction pair. -/
theorem firstComparison_comm (U V : Set X) :
    (quotientChainRow U V).f ≫ (middleComparisonIso U V).hom =
      (firstComparisonIso U V).hom ≫ restrictionPair U V := by
  apply (cancel_epi (cokernel.π (supportedInclusion (U ∩ V)))).mp
  dsimp only [quotientChainRow, quotientRow]
  erw [cokernel.map, cokernel.π_desc_assoc]
  change biprod.lift (𝟙 (chains X)) (-(𝟙 (chains X))) ≫ cokernel.π _ ≫ (middleComparisonIso U V).hom = _
  erw [middleComparisonIso_projection U V]
  change biprod.lift (𝟙 (chains X)) (-(𝟙 (chains X))) ≫
    biprod.map (cokernel.π (inclusion U)) (-(cokernel.π (inclusion V))) =
      (cokernel.π (supportedInclusion (U ∩ V)) ≫ (supportedRelativeIso (U ∩ V)).hom) ≫
        restrictionPair U V
  rw [supportedRelativeIso_projection]
  apply biprod.hom_ext <;>
    simp [restrictionPair, Category.assoc, relativeInclusion_projection]

/-- The second quotient map transports to the literal difference of restrictions. -/
theorem middleComparison_comm (U V : Set X) :
    (quotientChainRow U V).g ≫ smallRelativeComparison U V =
      (middleComparisonIso U V).hom ≫ restrictionDifference U V := by
  apply (cancel_epi (cokernel.π (biprod.map (supportedInclusion U) (supportedInclusion V)))).mp
  dsimp only [quotientChainRow, quotientRow]
  erw [cokernel.map, cokernel.π_desc_assoc]
  change biprod.desc (𝟙 (chains X)) (𝟙 (chains X)) ≫ cokernel.π _ ≫ smallRelativeComparison U V = _
  erw [smallRelativeComparison_projection, ← Category.assoc, middleComparisonIso_projection]
  apply biprod.hom_ext' <;>
    simp [restrictionDifference, relativeInclusion_projection]

end TernaryPoly.RationalRelativeSupport
