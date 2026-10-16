module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVMaps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVKernelAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex SingularLocalSupport EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The genuine pair of cochain restrictions to the two support complements. -/
def jointRestriction (K L : Set B) := biprod.lift (localRestriction p Kᶜ V) (localRestriction p Lᶜ V)

/-- The actual support sum retains the sum of ambient cochain inclusions. -/
theorem supportSum_inclusion (K L : Set B) :
    biprod.desc (supportInclusion p V K) (supportInclusion p V L) =
      supportSum p V K L ≫ supportInclusion p V (K ∪ L) := by
  apply biprod.hom_ext'
  · simp only [supportSum,biprod.inl_desc,biprod.inl_desc_assoc,supportMap_inclusion]
  · simp only [supportSum,biprod.inr_desc,biprod.inr_desc_assoc,supportMap_inclusion]

/-- The actual joint-restriction kernel identifies with the support-sum kernel by the signed pair. -/
def jointKernelIso (K L : Set B) : kernel (jointRestriction p V K L) ≅ kernel (supportSum p V K L) :=
  kernelPairSumIso (localRestriction p Kᶜ V) (localRestriction p Lᶜ V) ≪≫
    kernelIsoOfEq (supportSum_inclusion p V K L) ≪≫ kernelCompMono (supportSum p V K L) (supportInclusion p V (K ∪ L))

/-- The signed comparison of the two kernels retains its actual cochain components. -/
theorem jointKernelIso_inclusion (K L : Set B) :
    (jointKernelIso p V K L).hom ≫ kernel.ι (supportSum p V K L) =
      biprod.lift (kernelPairLeft (localRestriction p Kᶜ V) (localRestriction p Lᶜ V))
        (-kernelPairRight (localRestriction p Kᶜ V) (localRestriction p Lᶜ V)) := by
  change (kernelPairToSum (localRestriction p Kᶜ V) (localRestriction p Lᶜ V) ≫
    (kernelIsoOfEq (supportSum_inclusion p V K L)).hom ≫
      (kernelCompMono (supportSum p V K L) (supportInclusion p V (K ∪ L))).hom) ≫
        kernel.ι (supportSum p V K L) = _
  rw [Category.assoc,Category.assoc,kernelCompMono_hom,kernel.lift_ι,kernelIsoOfEq_hom_comp_ι]
  exact kernel.lift_ι _ _ _

/-- Actual intersection-support cochains map into the joint complement-restriction kernel. -/
def jointComparison (K L : Set B) : supportCochains p V (K ∩ L) ⟶ kernel (jointRestriction p V K L) :=
  kernel.lift _ (supportInclusion p V (K ∩ L)) (by
    apply biprod.hom_ext
    · change (supportInclusion p V (K ∩ L) ≫ jointRestriction p V K L) ≫ biprod.fst = 0 ≫ biprod.fst
      rw [Category.assoc,jointRestriction,biprod.lift_fst,zero_comp]
      rw [← supportMap_inclusion p V (K ∩ L) K Set.inter_subset_left,Category.assoc,kernel.condition,comp_zero]
    · change (supportInclusion p V (K ∩ L) ≫ jointRestriction p V K L) ≫ biprod.snd = 0 ≫ biprod.snd
      rw [Category.assoc,jointRestriction,biprod.lift_snd,zero_comp]
      rw [← supportMap_inclusion p V (K ∩ L) L Set.inter_subset_right,Category.assoc,kernel.condition,comp_zero])

/-- The joint comparison retains the actual left support enlargement. -/
theorem jointComparison_left (K L : Set B) :
    jointComparison p V K L ≫ kernelPairLeft (localRestriction p Kᶜ V) (localRestriction p Lᶜ V) =
      supportMap p V (K ∩ L) K Set.inter_subset_left := by
  apply (cancel_mono (supportInclusion p V K)).mp
  dsimp only [jointComparison, jointRestriction, supportInclusion, supportCochains]
  rw [Category.assoc,kernelPairLeft,kernel.lift_ι]
  erw [kernel.lift_ι]
  exact (supportMap_inclusion p V (K ∩ L) K Set.inter_subset_left).symm

/-- The joint comparison retains the actual right support enlargement. -/
theorem jointComparison_right (K L : Set B) :
    jointComparison p V K L ≫ kernelPairRight (localRestriction p Kᶜ V) (localRestriction p Lᶜ V) =
      supportMap p V (K ∩ L) L Set.inter_subset_right := by
  apply (cancel_mono (supportInclusion p V L)).mp
  dsimp only [jointComparison, jointRestriction, supportInclusion, supportCochains]
  rw [Category.assoc,kernelPairRight,kernel.lift_ι]
  erw [kernel.lift_ι]
  exact (supportMap_inclusion p V (K ∩ L) L Set.inter_subset_right).symm

/-- The actual intersection comparison factors through the joint kernel and its signed isomorphism. -/
theorem intersectionComparison_factor (K L : Set B) :
    jointComparison p V K L ≫ (jointKernelIso p V K L).hom = intersectionComparison p V K L := by
  apply (cancel_mono (kernel.ι (supportSum p V K L))).mp
  rw [Category.assoc,jointKernelIso_inclusion,intersectionComparison_inclusion]
  dsimp only [jointComparison, jointRestriction, supportCochains] at *
  apply biprod.hom_ext
  · rw [Category.assoc,biprod.lift_fst,supportDiagonal,biprod.lift_fst]
    exact jointComparison_left p V K L
  · rw [Category.assoc,biprod.lift_snd,supportDiagonal,biprod.lift_snd,Preadditive.comp_neg]
    exact congrArg Neg.neg (jointComparison_right p V K L)

end TernaryPoly.SingularLocalCompactMV
