module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Excision

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularCoverNaturality EquivariantSingularSmall SingularLocalCochainExcision

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Literal restriction of local cochains composes for three nested subsets. -/
theorem nestedLocalRestriction_comp (A D U : Set B) (hAD : A ⊆ D) (hDU : D ⊆ U) :
    nestedLocalRestriction p D U hDU V ≫ nestedLocalRestriction p A D hAD V =
      nestedLocalRestriction p A U (hAD.trans hDU) V := by
  unfold nestedLocalRestriction
  erw [← localPullback_comp]
  rfl

/-- The genuine flattened kernel comparison retains the actual ambient cochain. -/
theorem nestedKernelIso_inclusion (A D : Set B) :
    (nestedKernelIso p V A D).hom ≫ kernel.ι (localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V) =
      kernel.ι (nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V) := by
  unfold nestedKernelIso
  erw [kernel.lift_ι,Category.comp_id]

/-- The inverse flattened kernel comparison retains the actual ambient cochain. -/
theorem nestedKernelIso_inv_inclusion (A D : Set B) :
    (nestedKernelIso p V A D).inv ≫ kernel.ι (nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V) =
      kernel.ι (localRestriction (restrictedProjection p D) (Subtype.val ⁻¹' A) V) := by
  rw [← nestedKernelIso_inclusion p V A D,Iso.inv_hom_id_assoc]

/-- Actual restriction between two neighborhood relative-cochain kernels. -/
def neighborhoodRestriction (A D U : Set B) (hDU : D ⊆ U) :
    neighborhoodCochains p V A U ⟶ neighborhoodCochains p V A D :=
  kernel.map _ _ (nestedLocalRestriction p D U hDU V)
    (nestedLocalRestriction p (A ∩ D) (A ∩ U) (fun _ h => ⟨h.1,hDU h.2⟩) V) (by
      exact (nestedLocalRestriction_comp p V (A ∩ D) (A ∩ U) U
        (fun _ h => ⟨h.1,hDU h.2⟩) Set.inter_subset_right).trans
        (nestedLocalRestriction_comp p V (A ∩ D) D U Set.inter_subset_right hDU).symm)

/-- The neighborhood-kernel restriction retains literal restriction of cochains. -/
theorem neighborhoodRestriction_inclusion (A D U : Set B) (hDU : D ⊆ U) :
    neighborhoodRestriction p V A D U hDU ≫ kernel.ι (nestedLocalRestriction p (A ∩ D) D Set.inter_subset_right V) =
      kernel.ι (nestedLocalRestriction p (A ∩ U) U Set.inter_subset_right V) ≫ nestedLocalRestriction p D U hDU V :=
  kernel.lift_ι _ _ _

/-- The genuine fixed-support restriction between two nested subsets of one ambient covering. -/
def supportBetweenRestriction (D U : Set B) (hDU : D ⊆ U) (K : Set B) :
    supportCochains (restrictedProjection p U) V (Subtype.val ⁻¹' K) ⟶
      supportCochains (restrictedProjection p D) V (Subtype.val ⁻¹' K) :=
  (nestedKernelIso p V Kᶜ U).inv ≫ neighborhoodRestriction p V Kᶜ D U hDU ≫
    (nestedKernelIso p V Kᶜ D).hom

/-- Fixed-support restriction between nested subsets is the literal local-cochain restriction. -/
theorem supportBetweenRestriction_inclusion (D U : Set B) (hDU : D ⊆ U) (K : Set B) :
    supportBetweenRestriction p V D U hDU K ≫
      supportInclusion (restrictedProjection p D) V (Subtype.val ⁻¹' K) =
    supportInclusion (restrictedProjection p U) V (Subtype.val ⁻¹' K) ≫ nestedLocalRestriction p D U hDU V := by
  have hD : (nestedKernelIso p V Kᶜ D).hom ≫
      supportInclusion (restrictedProjection p D) V (Subtype.val ⁻¹' K) =
      kernel.ι (nestedLocalRestriction p (Kᶜ ∩ D) D Set.inter_subset_right V) :=
    nestedKernelIso_inclusion p V Kᶜ D
  have hU : (nestedKernelIso p V Kᶜ U).inv ≫
      kernel.ι (nestedLocalRestriction p (Kᶜ ∩ U) U Set.inter_subset_right V) =
      supportInclusion (restrictedProjection p U) V (Subtype.val ⁻¹' K) :=
    nestedKernelIso_inv_inclusion p V Kᶜ U
  unfold supportBetweenRestriction
  rw [Category.assoc,Category.assoc,hD,
    neighborhoodRestriction_inclusion,← Category.assoc,hU]

/-- Restriction through an intermediate neighborhood equals direct support restriction. -/
theorem supportToOpen_between (D U : Set B) (hDU : D ⊆ U) (K : Set B) :
    supportToOpen p V U K ≫ supportBetweenRestriction p V D U hDU K = supportToOpen p V D K := by
  apply (cancel_mono (supportInclusion (restrictedProjection p D) V (Subtype.val ⁻¹' K))).mp
  rw [Category.assoc,supportBetweenRestriction_inclusion,← Category.assoc,supportToOpen_inclusion,
    Category.assoc,localRestriction_nested,supportToOpen_inclusion]

/-- On actual support cohomology, nested restriction is inverse ambient excision followed by
actual restriction to the smaller neighborhood. -/
theorem supportBetweenRestriction_homology (D U : Opens B) (hDU : D ≤ U) (K : Set B)
    (hK : IsClosed K) (hKD : K ⊆ D) (k : ℕ) :
    homologyMap (supportBetweenRestriction p V D U hDU K) k =
      (supportExcisionIso p V U K hK (hKD.trans hDU) k).inv ≫
        (supportExcisionIso p V D K hK hKD k).hom := by
  apply (cancel_epi (supportExcisionIso p V U K hK (hKD.trans hDU) k).hom).mp
  rw [Iso.hom_inv_id_assoc]
  change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k
  erw [← homologyMap_comp,supportToOpen_between]

end TernaryPoly.SingularLocalSupport
