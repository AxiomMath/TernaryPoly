module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportSupportedExact

@[expose] public section

noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree RationalRelativeExcision RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- The actual nested subspace of a larger subset is homeomorphic to the original smaller subset. -/
def insideSubsetHomeomorph (S W : Set X) (hSW : S ⊆ W) : inside S W ≃ₜ S where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hSW x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The literal subspace-chain comparison commutes with inclusion into the ambient chains. -/
theorem corestrict_supportedInclusion (S : Set X) :
    subChainCorestrict ℚ (TopCat.of X) S ≫ supportedInclusion S = inclusion S := by
  ext n c
  rfl

/-- Supported chains in a subspace identify to the same actual chains in the original ambient space. -/
def supportedTransportIso (S W : Set X) (hSW : S ⊆ W) :
    subChainComplex ℚ (TopCat.of W) (inside S W) ≅ subChainComplex ℚ (TopCat.of X) S :=
  (asIso (subChainCorestrict ℚ (TopCat.of W) (inside S W))).symm ≪≫
    chainHomeomorphIso (insideSubsetHomeomorph S W hSW) ≪≫
    asIso (subChainCorestrict ℚ (TopCat.of X) S)

/-- The supported-chain transport preserves the actual inclusion into full ambient chains. -/
theorem supportedTransportIso_inclusion (S W : Set X) (hSW : S ⊆ W) :
    (supportedTransportIso S W hSW).hom ≫ supportedInclusion S =
      supportedInclusion (inside S W) ≫ inclusion W := by
  apply (cancel_epi (subChainCorestrict ℚ (TopCat.of W) (inside S W))).mp
  simp only [supportedTransportIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, corestrict_supportedInclusion, corestrict_supportedInclusion]
  change RationalSingularAugmentation.chainMap _ ≫ RationalSingularAugmentation.chainMap _ =
    RationalSingularAugmentation.chainMap _ ≫ RationalSingularAugmentation.chainMap _
  rw [← RationalSingularAugmentation.chainMap_comp, ← RationalSingularAugmentation.chainMap_comp]
  rfl

/-- Literal supported inclusions compose with the actual ambient inclusion. -/
theorem subChainInclusion_supportedInclusion (S T : Set X) (hST : S ⊆ T) :
    subChainInclusion (R := ℚ) (X := TopCat.of X) S T hST ≫ supportedInclusion T = supportedInclusion S := by
  ext n c
  rfl

/-- Supported transport is natural under inclusion of the smaller support. -/
theorem supportedTransportIso_natural (S T W : Set X) (hST : S ⊆ T) (hTW : T ⊆ W) :
    (supportedTransportIso S W (hST.trans hTW)).hom ≫ subChainInclusion (R := ℚ) (X := TopCat.of X) S T hST =
      subChainInclusion (R := ℚ) (X := TopCat.of W) (inside S W) (inside T W) (fun _ hx => hST hx) ≫
        (supportedTransportIso T W hTW).hom := by
  apply (cancel_mono (supportedInclusion T)).mp
  rw [Category.assoc, subChainInclusion_supportedInclusion,
    Category.assoc, supportedTransportIso_inclusion, supportedTransportIso_inclusion,
    ← Category.assoc]
  erw [subChainInclusion_supportedInclusion]

end TernaryPoly.RationalRelativeSupport
