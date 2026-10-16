module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportTransport
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSequence

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual supported-intersection transports commute with the signed diagonal relation. -/
theorem supportedTransport_diagonal (U V W : Set X) (hUW : U ⊆ W) (hVW : V ⊆ W) :
    supportedDiagonal (inside U W) (inside V W) ≫
      (biprod.mapIso (supportedTransportIso U W hUW) (supportedTransportIso V W hVW)).hom =
    (supportedTransportIso (U ∩ V) W (Set.inter_subset_left.trans hUW)).hom ≫ supportedDiagonal U V := by
  apply biprod.hom_ext
  · simp only [supportedDiagonal, biprod.mapIso_hom, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc]
    erw [Category.assoc, biprod.lift_fst]
    exact (supportedTransportIso_natural (U ∩ V) U W Set.inter_subset_left hUW).symm
  · simp only [supportedDiagonal, biprod.mapIso_hom, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.neg_comp]
    erw [Category.assoc, biprod.lift_snd, Preadditive.comp_neg]
    exact congrArg Neg.neg (supportedTransportIso_natural (U ∩ V) V W Set.inter_subset_right hVW).symm

/-- The actual small sums are invariant under viewing the same supported chains inside a subspace. -/
def smallSumTransportIso (U V W : Set X) (hUW : U ⊆ W) (hVW : V ⊆ W) :
    supportedSmallSum (inside U W) (inside V W) ≅ supportedSmallSum U V :=
  cokernel.mapIso (supportedDiagonal (inside U W) (inside V W)) (supportedDiagonal U V)
    (supportedTransportIso (U ∩ V) W (Set.inter_subset_left.trans hUW))
    (biprod.mapIso (supportedTransportIso U W hUW) (supportedTransportIso V W hVW))
    (supportedTransport_diagonal U V W hUW hVW)

/-- The small-sum isomorphism preserves the literal quotient projections. -/
theorem smallSumTransportIso_projection (U V W : Set X) (hUW : U ⊆ W) (hVW : V ⊆ W) :
    cokernel.π (supportedDiagonal (inside U W) (inside V W)) ≫ (smallSumTransportIso U V W hUW hVW).hom =
      (biprod.mapIso (supportedTransportIso U W hUW) (supportedTransportIso V W hVW)).hom ≫
        cokernel.π (supportedDiagonal U V) := by
  simp [smallSumTransportIso, cokernel.mapIso, cokernel.map]

/-- The small-sum isomorphism commutes with literal inclusions into full ambient chains. -/
theorem smallSumTransportIso_inclusion (U V W : Set X) (hUW : U ⊆ W) (hVW : V ⊆ W) :
    (smallSumTransportIso U V W hUW hVW).hom ≫ supportedSmallSumInclusion U V =
      supportedSmallSumInclusion (inside U W) (inside V W) ≫ inclusion W := by
  apply (cancel_epi (cokernel.π (supportedDiagonal (inside U W) (inside V W)))).mp
  rw [← Category.assoc, smallSumTransportIso_projection, Category.assoc,
    supportedSmallSumInclusion, cokernel.π_desc,
    ← Category.assoc, supportedSmallSumInclusion, cokernel.π_desc]
  apply biprod.hom_ext' <;>
    simp only [biprod.mapIso_hom, biprod.inl_map_assoc, biprod.inr_map_assoc,
      supportedSum, biprod.inl_desc, biprod.inr_desc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc]
  · exact supportedTransportIso_inclusion U W hUW
  · exact supportedTransportIso_inclusion V W hVW

end TernaryPoly.RationalRelativeSupport
