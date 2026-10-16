module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportQuotientMap

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- Literal relative inclusion maps compose as the corresponding inclusions of excluded subspaces. -/
theorem relativeInclusion_comp (S T W : Set X) (hST : S ⊆ T) (hTW : T ⊆ W) :
    relativeInclusion S T hST ≫ relativeInclusion T W hTW = relativeInclusion S W (hST.trans hTW) := by
  apply (cancel_epi (cokernel.π (inclusion S))).mp
  simp only [← Category.assoc, relativeInclusion_projection]

/-- The first actual quotient comparison is natural under inclusions of both exclusions. -/
theorem firstComparison_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    (quotientChainMap U V U' V' hU hV).τ₁ ≫ (firstComparisonIso U' V').hom =
      (firstComparisonIso U V).hom ≫
        relativeInclusion (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV) := by
  apply (cancel_epi (cokernel.π (supportedInclusion (U ∩ V)))).mp
  erw [← Category.assoc, quotientChainMap_projection₁ U V U' V' hU hV]
  change cokernel.π _ ≫ (supportedRelativeIso (U' ∩ V')).hom =
    cokernel.π _ ≫ (supportedRelativeIso (U ∩ V)).hom ≫ _
  rw [supportedRelativeIso_projection, ← Category.assoc, supportedRelativeIso_projection,
    relativeInclusion_projection]

/-- The signed middle quotient comparison is natural under inclusions of both exclusions. -/
theorem middleComparison_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    (quotientChainMap U V U' V' hU hV).τ₂ ≫ (middleComparisonIso U' V').hom =
      (middleComparisonIso U V).hom ≫ biprod.map (relativeInclusion U U' hU) (relativeInclusion V V' hV) := by
  apply (cancel_epi (cokernel.π (biprod.map (supportedInclusion U) (supportedInclusion V)))).mp
  erw [← Category.assoc, quotientChainMap_projection₂ U V U' V' hU hV,
    middleComparisonIso_projection U' V', ← Category.assoc, middleComparisonIso_projection U V]
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [relativeInclusion_projection]

/-- The actual small-relative comparison is natural under inclusions of both exclusions. -/
theorem thirdComparison_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    (quotientChainMap U V U' V' hU hV).τ₃ ≫ smallRelativeComparison U' V' =
      smallRelativeComparison U V ≫ relativeInclusion (U ∪ V) (U' ∪ V') (Set.union_subset_union hU hV) := by
  apply (cancel_epi (cokernel.π (supportedSmallSumInclusion U V))).mp
  erw [← Category.assoc, quotientChainMap_projection₃ U V U' V' hU hV,
    smallRelativeComparison_projection, ← Category.assoc, smallRelativeComparison_projection,
    relativeInclusion_projection]

end TernaryPoly.RationalRelativeSupport
