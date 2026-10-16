module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionAlgebra
public import TernaryPeriodPolynomials.Topology.Rational.Relative.ExcisionMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace ContractibleSingularHomology
open RationalRelativeSingular SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {X : Type} [TopologicalSpace X] (U V : Opens X) (hUV : U ⊔ V = ⊤)

/-- The actual square from intersection/V-supported chains to U/cover-small chains induces this cokernel map. -/
def supportedSmallMap :
    cokernel (mvInclUV_V ℚ (X := TopCat.of X) U V) ⟶
      cokernel (mvInclU_small ℚ (X := TopCat.of X) U V hUV) :=
  cokernel.map (mvInclUV_V ℚ (X := TopCat.of X) U V)
    (mvInclU_small ℚ (X := TopCat.of X) U V hUV) (mvInclUV_U ℚ (X := TopCat.of X) U V) (mvInclV_small ℚ (X := TopCat.of X) U V hUV) (mvIncl_comp_eq ℚ (X := TopCat.of X) U V hUV).symm

/-- The actual supported small relative map is an isomorphism, by the proved signed Mayer-Vietoris sequence. -/
instance supportedSmallMap_isIso : IsIso (supportedSmallMap U V hUV) :=
  RelativeExcisionAlgebra.cokernel_map_isIso_of_shortExact
    (mvInclUV_U ℚ (X := TopCat.of X) U V) (mvInclUV_V ℚ (X := TopCat.of X) U V)
    (mvInclU_small ℚ (X := TopCat.of X) U V hUV) (mvInclV_small ℚ (X := TopCat.of X) U V hUV)
    (mvIncl_comp_eq ℚ (X := TopCat.of X) U V hUV).symm (mvShortComplex_shortExact ℚ (X := TopCat.of X) U V hUV)

/-- The inclusion of U-supported chains into cover-small chains is a genuine chain monomorphism. -/
instance supportedToSmall_mono : Mono (mvInclU_small ℚ (X := TopCat.of X) U V hUV) := by
  apply mono_of_mono_f
  intro n
  apply (ModuleCat.mono_iff_injective _).mpr
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : smallChainSubmodule ℚ (TopCat.of X) (twoSetCover U V hUV) n => z.val) h

/-- The literal small-to-full inclusion commutes with the actual U subspace-chain comparison. -/
theorem smallToFull_square :
    mvInclU_small ℚ (X := TopCat.of X) U V hUV ≫ smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV) =
      inv (subChainCorestrict ℚ (TopCat.of X) U) ≫ inclusion (U : Set X) := by
  rw [← cancel_epi (subChainCorestrict ℚ (TopCat.of X) U)]
  simp only [IsIso.hom_inv_id_assoc]
  ext n c
  rfl

/-- The actual map from the small relative quotient to the full literal relative chain complex. -/
def smallRelativeMap : cokernel (mvInclU_small ℚ (X := TopCat.of X) U V hUV) ⟶ relativeChains (U : Set X) :=
  cokernel.map _ _ (inv (subChainCorestrict ℚ (TopCat.of X) U))
    (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV)) (smallToFull_square U V hUV)

/-- Small-chain quasi-isomorphism passes to the actual relative cokernel by the homology-sequence comparison. -/
instance smallRelativeMap_quasiIso : QuasiIso (smallRelativeMap U V hUV) :=
by
  have : QuasiIso (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV)) :=
    smallChains_inclusion_quasiIso ℚ (TopCat.of X) (twoSetCover U V hUV)
  exact @RelativeExcisionAlgebra.cokernel_map_quasiIso _ _ _ _
    (mvInclU_small ℚ (X := TopCat.of X) U V hUV) (inclusion (U : Set X))
    inferInstance inferInstance (inv (subChainCorestrict ℚ (TopCat.of X) U))
    (smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV)) (smallToFull_square U V hUV)
    inferInstance this

/-- The literal nested subtype intersection has its actual supported-chain identification. -/
def insideSupportedIso : chains (inside (U : Set X) (V : Set X)) ≅
    subChainComplex ℚ (TopCat.of X) ((U : Set X) ∩ (V : Set X)) :=
  chainHomeomorphIso (insideHomeomorph (U : Set X) (V : Set X)) ≪≫ asIso (subChainCorestrict ℚ (TopCat.of X) _)

/-- The intersection/subspace comparison preserves the actual inclusion into V. -/
theorem insideSupported_square :
    inclusion (inside (U : Set X) (V : Set X)) ≫ subChainCorestrict ℚ (TopCat.of X) V =
      (insideSupportedIso U V).hom ≫ mvInclUV_V ℚ (X := TopCat.of X) U V := by
  simp only [insideSupportedIso,Iso.trans_hom,asIso_hom,Category.assoc]
  unfold mvInclUV_V
  rw [RationalSingularAugmentation.corestrict_inclusion]
  change RationalSingularAugmentation.chainMap _ ≫ _ =
    RationalSingularAugmentation.chainMap _ ≫ RationalSingularAugmentation.chainMap _ ≫ _
  rw [← Category.assoc,← RationalSingularAugmentation.chainMap_comp]
  rfl

/-- The actual relative chains of the literal pair identify with the supported intersection/V quotient. -/
def insideRelativeMap : relativeChains (inside (U : Set X) (V : Set X)) ⟶
    cokernel (mvInclUV_V ℚ (X := TopCat.of X) U V) :=
  cokernel.map _ _ (insideSupportedIso U V).hom (subChainCorestrict ℚ (TopCat.of X) V)
    (insideSupported_square U V)

instance insideRelativeMap_isIso : IsIso (insideRelativeMap U V) := by
  unfold insideRelativeMap
  infer_instance

/-- Factoring through supported and small chains preserves precisely the actual pair-inclusion map. -/
theorem excisionMap_factorization :
    excisionMap (U : Set X) (V : Set X) =
      insideRelativeMap U V ≫ supportedSmallMap U V hUV ≫ smallRelativeMap U V hUV := by
  apply (cancel_epi (cokernel.π (inclusion (inside (U : Set X) (V : Set X))))).mp
  rw [excisionMap_projection]
  simp only [insideRelativeMap,supportedSmallMap,smallRelativeMap,cokernel.map,
    cokernel.π_desc_assoc,Category.assoc]
  erw [cokernel.π_desc]
  have hf : subChainCorestrict ℚ (TopCat.of X) V ≫
      mvInclV_small ℚ (X := TopCat.of X) U V hUV ≫
      smallChainsInclusion ℚ (TopCat.of X) (twoSetCover U V hUV) = inclusion (V : Set X) := by
    ext n c
    rfl
  erw [← Category.assoc,← Category.assoc,Category.assoc (subChainCorestrict ℚ (TopCat.of X) V),hf]

include hUV in
/-- Rational singular excision: the actual pair-inclusion map is a quasi-isomorphism in all degrees. -/
theorem excisionMap_quasiIso : QuasiIso (excisionMap (U : Set X) (V : Set X)) := by
  rw [excisionMap_factorization U V hUV]
  infer_instance

/-- The actual relative homology isomorphism induced by pair inclusion for the open cover. -/
def excisionHomologyIso (n : ℕ) :
    (relativeChains (inside (U : Set X) (V : Set X))).homology n ≅
      (relativeChains (U : Set X)).homology n :=
by
  have := excisionMap_quasiIso U V hUV
  exact asIso (homologyMap (excisionMap (U : Set X) (V : Set X)) n)

/-- The homology isomorphism is the homology map of the literal excision inclusion. -/
theorem excisionHomologyIso_hom (n : ℕ) :
    (excisionHomologyIso U V hUV n).hom = homologyMap (excisionMap (U : Set X) (V : Set X)) n := rfl

end TernaryPoly.RationalRelativeExcision
