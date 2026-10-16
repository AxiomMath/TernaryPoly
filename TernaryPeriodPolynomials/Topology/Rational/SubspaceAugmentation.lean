module

public import TernaryPeriodPolynomials.Topology.Rational.SingularAugmentation
public import TernaryPeriodPolynomials.Topology.Singular.SubdivisionMayerVietoris

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalSingularAugmentation
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
variable (X : Type) [TopologicalSpace X]

/-- Literal inclusion of one subspace into a larger one. -/
def inclusion (S T : Set X) (h : S ⊆ T) : C(S,T) :=
  ⟨Set.inclusion h, by fun_prop⟩

/-- The actual subspace-to-supported-chain comparison respects inclusions. -/
theorem corestrict_inclusion (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict ℚ (TopCat.of X) S ≫ subChainInclusion (R := ℚ) (X := TopCat.of X) S T h =
      chainMap (inclusion X S T h) ≫ subChainCorestrict ℚ (TopCat.of X) T := by
  ext n c
  apply Subtype.ext
  exact congrArg (fun f => f.hom c)
    (singularChainMap_comp ℚ (TopCat.ofHom (inclusion X S T h)) (sInclusion (X := TopCat.of X) T) n)

/-- The actual H0 augmentation of supported chains is transported from the literal subspace. -/
def supportedAugmentation (S : Set X) :
    (subChainComplex ℚ (TopCat.of X) S).homology 0 ⟶ ModuleCat.of ℚ ℚ :=
  (SingularSubdivision.supportedHomologyIso X S 0).hom ≫ augmentation S

instance supportedAugmentation_isIso (S : Set X) [ContractibleSpace S] :
    IsIso (supportedAugmentation X S) := by
  unfold supportedAugmentation
  infer_instance

/-- Naturality of the supported augmentation for actual subspace inclusions. -/
theorem supportedAugmentation_naturality (S T : Set X) (h : S ⊆ T) :
    homologyMap (subChainInclusion (R := ℚ) (X := TopCat.of X) S T h) 0 ≫ supportedAugmentation X T =
      supportedAugmentation X S := by
  have hh : subChainInclusion (R := ℚ) (X := TopCat.of X) S T h ≫ inv (subChainCorestrict ℚ (TopCat.of X) T) =
      inv (subChainCorestrict ℚ (TopCat.of X) S) ≫ chainMap (inclusion X S T h) := by
    rw [← cancel_epi (subChainCorestrict ℚ (TopCat.of X) S),
      ← cancel_mono (subChainCorestrict ℚ (TopCat.of X) T)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.hom_inv_id_assoc, corestrict_inclusion]
  change homologyMap (subChainInclusion (R := ℚ) (X := TopCat.of X) S T h) 0 ≫
      homologyMap (inv (subChainCorestrict ℚ (TopCat.of X) T)) 0 ≫ augmentation T =
    homologyMap (inv (subChainCorestrict ℚ (TopCat.of X) S)) 0 ≫ augmentation S
  rw [← Category.assoc, ← homologyMap_comp, hh, homologyMap_comp, Category.assoc,
    naturality]

end TernaryPoly.RationalSingularAugmentation
