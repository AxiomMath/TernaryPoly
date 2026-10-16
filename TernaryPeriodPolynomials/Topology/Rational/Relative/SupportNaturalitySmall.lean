module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportLiteral

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The signed supported diagonal is natural under a pair of literal support inclusions. -/
theorem supportedDiagonal_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    supportedDiagonal U V ≫ biprod.map
      (subChainInclusion (R := ℚ) (X := TopCat.of X) U U' hU)
      (subChainInclusion (R := ℚ) (X := TopCat.of X) V V' hV) =
    subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV) ≫
      supportedDiagonal U' V' := by
  apply biprod.hom_ext <;>
    simp only [supportedDiagonal, Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
      Preadditive.neg_comp, Preadditive.comp_neg]
  · ext n c
    rfl
  · congr 1

/-- The actual small-sum map induced by increasing both allowed open subsets. -/
def smallSumMap (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    supportedSmallSum U V ⟶ supportedSmallSum U' V' :=
  cokernel.map (supportedDiagonal U V) (supportedDiagonal U' V')
    (subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV))
    (biprod.map (subChainInclusion (R := ℚ) (X := TopCat.of X) U U' hU)
      (subChainInclusion (R := ℚ) (X := TopCat.of X) V V' hV))
    (supportedDiagonal_natural U V U' V' hU hV)

/-- The small-sum map preserves the actual inclusion into the ambient chain complex. -/
theorem smallSumMap_inclusion (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    smallSumMap U V U' V' hU hV ≫ supportedSmallSumInclusion U' V' = supportedSmallSumInclusion U V := by
  apply (cancel_epi (cokernel.π (supportedDiagonal U V))).mp
  simp only [smallSumMap, cokernel.map, cokernel.π_desc_assoc, Category.assoc,
    supportedSmallSumInclusion, cokernel.π_desc]
  apply biprod.hom_ext' <;>
    simp only [supportedSum, biprod.inl_map_assoc, biprod.inr_map_assoc,
      biprod.inl_desc, biprod.inr_desc]
  · exact subChainInclusion_supportedInclusion U U' hU
  · exact subChainInclusion_supportedInclusion V V' hV

/-- The supported intersection/sum short exact sequences carry actual inclusion maps. -/
def smallRowMap (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    smallRow U V ⟶ smallRow U' V' where
  τ₁ := subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV)
  τ₂ := biprod.map (subChainInclusion (R := ℚ) (X := TopCat.of X) U U' hU)
    (subChainInclusion (R := ℚ) (X := TopCat.of X) V V' hV)
  τ₃ := smallSumMap U V U' V' hU hV
  comm₁₂ := (supportedDiagonal_natural U V U' V' hU hV).symm
  comm₂₃ := by simp [smallRow, RelativeChainSequence.sequence, smallSumMap, cokernel.map]

/-- The supported inclusion diagram lies over the identity on the ambient diagonal sequence. -/
theorem smallRowMap_toDiagonal (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') :
    smallRowMap U V U' V' hU hV ≫ smallToDiagonal U' V' = smallToDiagonal U V := by
  apply ShortComplex.Hom.ext
  · exact subChainInclusion_supportedInclusion (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV)
  · change biprod.map _ _ ≫ biprod.map _ _ = biprod.map _ _
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [subChainInclusion_supportedInclusion]
  · exact smallSumMap_inclusion U V U' V' hU hV

end TernaryPoly.RationalRelativeSupport
