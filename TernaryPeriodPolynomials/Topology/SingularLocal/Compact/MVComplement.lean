module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVCoverKernel
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVIncluded
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVJoint
public import TernaryPeriodPolynomials.Topology.Singular.CochainKernelComparison
public import TernaryPeriodPolynomials.Topology.SingularLocal.RestrictionSurjective

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalCoefficient SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

/-- The left complement is contained in the complement of the intersection. -/
theorem complementLeft_subset (K L : Set B) : Kᶜ ⊆ (K ∩ L)ᶜ := fun _ hx h => hx h.1

/-- The right complement is contained in the complement of the intersection. -/
theorem complementRight_subset (K L : Set B) : Lᶜ ⊆ (K ∩ L)ᶜ := fun _ hx h => hx h.2

/-- The actual left complement, open inside the complement of the intersected supports. -/
def complementLeftOpen (K L : Set B) (hK : IsClosed K) : Opens ((K ∩ L)ᶜ : Set B) :=
  ⟨Subtype.val ⁻¹' Kᶜ,hK.isOpen_compl.preimage continuous_subtype_val⟩

/-- The actual right complement, open inside the complement of the intersected supports. -/
def complementRightOpen (K L : Set B) (hL : IsClosed L) : Opens ((K ∩ L)ᶜ : Set B) :=
  ⟨Subtype.val ⁻¹' Lᶜ,hL.isOpen_compl.preimage continuous_subtype_val⟩

/-- These two actual complement opens cover their full ambient complement subspace. -/
theorem complementOpen_cover (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) :
    complementLeftOpen K L hK ⊔ complementRightOpen K L hL = ⊤ := by
  ext x
  change (x.val ∈ Kᶜ ∨ x.val ∈ Lᶜ) ↔ True
  simp only [iff_true]
  exact not_and_or.mp x.property

variable (W : Rep.{0} ℚ G) (K L : Set B) (hK : IsClosed K) (hL : IsClosed L)

/-- The actual Mayer–Vietoris cochain sequence on the complement of the intersected supports. -/
abbrev complementSequence := localSmallSequence (restrictedProjection p (K ∩ L)ᶜ)
  (complementLeftOpen K L hK) (complementRightOpen K L hL) (complementOpen_cover K L hK hL) W

/-- Actual ambient restriction followed by the genuine small-cover kernel comparison. -/
def smallJointRestriction : localCochains p hp.out W ⟶ kernel (complementSequence p W K L hK hL).g :=
  localRestriction p (K ∩ L)ᶜ W ≫
    coverKernelComparison (restrictedProjection p (K ∩ L)ᶜ) W
      (complementLeftOpen K L hK) (complementRightOpen K L hL) (complementOpen_cover K L hK hL)

/-- The actual small joint restriction is epi in every cochain degree. -/
instance smallJointRestriction_epi : Epi (smallJointRestriction p W K L hK hL) := by
  unfold smallJointRestriction
  infer_instance

/-- Actual support cochains compare to the kernel of the small joint restriction. -/
def complementComparison : supportCochains p W (K ∩ L) ⟶ kernel (smallJointRestriction p W K L hK hL) :=
  kernel.map (localRestriction p (K ∩ L)ᶜ W) (smallJointRestriction p W K L hK hL) (𝟙 _)
    (coverKernelComparison (restrictedProjection p (K ∩ L)ᶜ) W
      (complementLeftOpen K L hK) (complementRightOpen K L hL) (complementOpen_cover K L hK hL))
    (by rw [Category.id_comp]; rfl)

/-- The genuine relative small-cochain comparison is a quasi-isomorphism, including degree zero. -/
instance complementComparison_quasiIso : QuasiIso (complementComparison p W K L hK hL) := by
  unfold complementComparison
  apply CochainExcisionAlgebra.kernel_map_quasiIso

/-- The direct complement cochains identify with the actual iterated complement-cover cochains. -/
def complementPairIso :
    localCochains (restrictedProjection p Kᶜ) (restrictedQuotientCovering p Kᶜ) W ⊞
      localCochains (restrictedProjection p Lᶜ) (restrictedQuotientCovering p Lᶜ) W ≅
        (complementSequence p W K L hK hL).X₂ :=
  biprod.mapIso (includedCochainIso p Kᶜ (K ∩ L)ᶜ (complementLeft_subset K L) W)
    (includedCochainIso p Lᶜ (K ∩ L)ᶜ (complementRight_subset K L) W)

/-- The small joint restriction is the actual pair of complement restrictions under the literal flattening maps. -/
theorem smallJointRestriction_pair :
    smallJointRestriction p W K L hK hL ≫ kernel.ι (complementSequence p W K L hK hL).g =
      jointRestriction p W K L ≫ (complementPairIso p W K L hK hL).hom := by
  rw [smallJointRestriction,Category.assoc,coverKernelComparison_inclusion]
  change localRestriction p (K ∩ L)ᶜ W ≫
    biprod.lift (localRestriction (restrictedProjection p (K ∩ L)ᶜ) (Subtype.val ⁻¹' Kᶜ) W)
      (localRestriction (restrictedProjection p (K ∩ L)ᶜ) (Subtype.val ⁻¹' Lᶜ) W) =
    biprod.lift (localRestriction p Kᶜ W) (localRestriction p Lᶜ W) ≫
      biprod.map (includedCochainIso p Kᶜ (K ∩ L)ᶜ (complementLeft_subset K L) W).hom
        (includedCochainIso p Lᶜ (K ∩ L)ᶜ (complementRight_subset K L) W).hom
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.lift_fst,biprod.map_fst,biprod.lift_fst_assoc]
    exact includedCochainIso_ambient p Kᶜ (K ∩ L)ᶜ (complementLeft_subset K L) W
  · simp only [Category.assoc,biprod.lift_snd,biprod.map_snd,biprod.lift_snd_assoc]
    exact includedCochainIso_ambient p Lᶜ (K ∩ L)ᶜ (complementRight_subset K L) W

/-- The genuine small-restriction kernel is the genuine joint-restriction kernel. -/
def smallJointKernelIso : kernel (smallJointRestriction p W K L hK hL) ≅ kernel (jointRestriction p W K L) :=
  (kernelCompMono (smallJointRestriction p W K L hK hL) (kernel.ι (complementSequence p W K L hK hL).g)).symm ≪≫
    kernelIsoOfEq (smallJointRestriction_pair p W K L hK hL) ≪≫
      kernelCompMono (jointRestriction p W K L) (complementPairIso p W K L hK hL).hom

/-- The actual small-to-joint kernel isomorphism retains each ambient cochain. -/
theorem smallJointKernelIso_inclusion :
    (smallJointKernelIso p W K L hK hL).hom ≫ kernel.ι (jointRestriction p W K L) =
      kernel.ι (smallJointRestriction p W K L hK hL) := by
  simp only [smallJointKernelIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    kernelCompMono_hom,kernelCompMono_inv,kernel.lift_ι,kernelIsoOfEq_hom_comp_ι]

/-- The genuine intersection-to-joint comparison is the small-relative comparison followed by the literal kernel isomorphism. -/
theorem jointComparison_factor :
    complementComparison p W K L hK hL ≫ (smallJointKernelIso p W K L hK hL).hom =
      jointComparison p W K L := by
  apply (cancel_mono (kernel.ι (jointRestriction p W K L))).mp
  rw [Category.assoc,smallJointKernelIso_inclusion]
  simp only [complementComparison,kernel.map,kernel.lift_ι,Category.comp_id,jointComparison]

include hK hL in
/-- The actual comparison from intersection support to joint restriction is a quasi-isomorphism. -/
theorem jointComparison_quasiIso : QuasiIso (jointComparison p W K L) := by
  rw [← jointComparison_factor p W K L hK hL]
  infer_instance

include hK hL in
/-- The actual signed intersection-support map identifies support cochains with the sum kernel on cohomology. -/
theorem intersectionComparison_quasiIso : QuasiIso (intersectionComparison p W K L) := by
  have := jointComparison_quasiIso p W K L hK hL
  rw [← intersectionComparison_factor]
  infer_instance

end TernaryPoly.SingularLocalCompactMV
