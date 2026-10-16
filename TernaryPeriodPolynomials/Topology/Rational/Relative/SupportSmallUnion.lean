module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSmallCover

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology TopologicalSpace
open SphereOddDegree RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual small sum maps by inclusion to the chains supported on the union. -/
def smallSumToUnion (U V : Set X) : supportedSmallSum U V ⟶ subChainComplex ℚ (TopCat.of X) (U ∪ V) :=
  cokernel.desc (supportedDiagonal U V)
    (biprod.desc (subChainInclusion (R := ℚ) (X := TopCat.of X) U (U ∪ V) Set.subset_union_left)
      (subChainInclusion (R := ℚ) (X := TopCat.of X) V (U ∪ V) Set.subset_union_right)) (by
        rw [supportedDiagonal, biprod.lift_desc, Preadditive.neg_comp]
        have h : subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) U Set.inter_subset_left ≫
            subChainInclusion (R := ℚ) (X := TopCat.of X) U (U ∪ V) Set.subset_union_left =
          subChainInclusion (R := ℚ) (X := TopCat.of X) (U ∩ V) V Set.inter_subset_right ≫
            subChainInclusion (R := ℚ) (X := TopCat.of X) V (U ∪ V) Set.subset_union_right := by
          ext n c
          rfl
        rw [h, add_neg_cancel])

/-- Inclusion of the union-supported chains recovers the same actual small-sum inclusion. -/
theorem smallSumToUnion_inclusion (U V : Set X) :
    smallSumToUnion U V ≫ supportedInclusion (U ∪ V) = supportedSmallSumInclusion U V := by
  apply (cancel_epi (cokernel.π (supportedDiagonal U V))).mp
  rw [← Category.assoc, smallSumToUnion, cokernel.π_desc, supportedSmallSumInclusion, cokernel.π_desc]
  apply biprod.hom_ext' <;> simp only [supportedSum, biprod.inl_desc_assoc,
    biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc]
  · exact subChainInclusion_supportedInclusion U (U ∪ V) Set.subset_union_left
  · exact subChainInclusion_supportedInclusion V (U ∪ V) Set.subset_union_right

/-- Restrict an actual ambient open subset to a literal subspace. -/
def restrictedOpen (U : Opens X) (W : Set X) : Opens W :=
  ⟨inside (U : Set X) W, U.isOpen.preimage continuous_subtype_val⟩

/-- The two open complements cover their actual union subspace. -/
theorem restrictedOpen_union_cover (U V : Opens X) :
    restrictedOpen U ((U : Set X) ∪ V) ⊔ restrictedOpen V ((U : Set X) ∪ V) = ⊤ := by
  ext x
  change (x.val ∈ (U : Set X) ∨ x.val ∈ (V : Set X)) ↔ True
  exact ⟨fun _ => trivial, fun _ => x.property⟩

/-- The literal small-sum to union map factors through the established small chains of the union subspace. -/
theorem smallSumToUnion_factorization (U V : Set X) :
    smallSumToUnion U V =
      (smallSumTransportIso U V (U ∪ V) Set.subset_union_left Set.subset_union_right).inv ≫
        supportedSmallSumInclusion (inside U (U ∪ V)) (inside V (U ∪ V)) ≫
          subChainCorestrict ℚ (TopCat.of X) (U ∪ V) := by
  apply (cancel_mono (supportedInclusion (U ∪ V))).mp
  rw [smallSumToUnion_inclusion]
  simp only [Category.assoc]
  rw [corestrict_supportedInclusion, ← smallSumTransportIso_inclusion U V (U ∪ V) Set.subset_union_left Set.subset_union_right]
  rw [Iso.inv_hom_id_assoc]

/-- The actual small-sum to union inclusion is a quasi-isomorphism for two ambient open subsets. -/
theorem smallSumToUnion_quasiIso (U V : Opens X) : QuasiIso (smallSumToUnion (U : Set X) (V : Set X)) := by
  rw [smallSumToUnion_factorization]
  have : QuasiIso (supportedSmallSumInclusion (inside (U : Set X) ((U : Set X) ∪ V))
      (inside (V : Set X) ((U : Set X) ∪ V))) :=
    supportedSmallSumInclusion_quasiIso (restrictedOpen U ((U : Set X) ∪ V))
      (restrictedOpen V ((U : Set X) ∪ V)) (restrictedOpen_union_cover U V)
  infer_instance

end TernaryPoly.RationalRelativeSupport
