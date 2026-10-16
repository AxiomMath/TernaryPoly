module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.MVProductQuotient

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryMV
open Topology OrdinaryIncidence SymmetricSpaceRationalGluing SymmetricSpaceBoundaryFaces
  SymmetricSpaceBoundaryFaceTopology SingularBoundaryRestriction IntegralGL3Congruence
  SymmetricSpaceBordifiedQuotient
open scoped Pointwise

theorem boundaryProjection_mem_corner (x : BoundaryCover) :
    boundaryProjection x ∈ cornerBase ↔ x ∈ cornerLocus := by
  rw [cornerBase_eq_preimage, cornerLocus_eq_preimage]
  change projection principalSix x.val ∈ projection principalSix '' allCorners ↔ x.val ∈ allCorners
  exact Set.ext_iff.mp projection_allCorners_preimage x.val

theorem flagCollarParam_corner (F : Flag) (x : flagFace F) (t : ℝ) :
    flagCollarParam F (x,t) ∈ cornerLocus ↔ t=0 :=
  signedParam_cornerLocus (chosenFrame F) ((flagCoordinates F).symm x,t)

theorem flagCollarBase_corner (F : Flag) (x : FlagFaceOrbit F) (t : ℝ) :
    flagCollarBase F (x,t) ∈ cornerBase ↔ t=0 := by
  induction x using Quotient.inductionOn with | _ x =>
  exact (boundaryProjection_mem_corner _).trans (flagCollarParam_corner F x t)

def flagBase (F : Flag) : Set BoundaryBase := Set.range (fun x : FlagFaceOrbit F => flagCollarBase F (x,0))

theorem flagBase_eq_preimage (F : Flag) :
    flagBase F = Subtype.val ⁻¹' (projection principalSix '' flagFace F) := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    induction x using Quotient.inductionOn with | _ x =>
    refine ⟨x.val,x.property,?_⟩
    change projection principalSix x.val = projection principalSix (flagCollarParam F (x,0)).val
    rw [flagCollarParam_zero]
  · rintro ⟨x,hx,he⟩
    refine ⟨RestrictedQuotient.faceProjection (flagFace F) ⟨x,hx⟩,Subtype.ext ?_⟩
    change projection principalSix (flagCollarParam F (⟨x,hx⟩,0)).val = y.val
    simpa only [flagCollarParam_zero] using he

theorem flagBase_nonempty (F : Flag) : (flagBase F).Nonempty := by
  obtain ⟨x,hx⟩ := flagFace_nonempty F
  exact ⟨_,⟨RestrictedQuotient.faceProjection (flagFace F) ⟨x,hx⟩,rfl⟩⟩

theorem flagBase_subset_corner (F : Flag) : flagBase F ⊆ cornerBase := by
  rintro _ ⟨x,rfl⟩
  exact (flagCollarBase_corner F x 0).mpr rfl

theorem flagBase_smul (a : principalSix) (F : Flag) : flagBase (flagAction a F)=flagBase F := by
  rw [flagBase_eq_preimage,flagBase_eq_preimage,←flagFace_image,Set.image_image]
  congr 1
  congr 1
  funext x
  exact projection_smul principalSix a x

theorem flagBase_eq_of_mem {F G : Flag} {x : BoundaryBase}
    (hF : x∈flagBase F) (hG : x∈flagBase G) : flagBase F=flagBase G := by
  rw [flagBase_eq_preimage] at hF hG
  obtain ⟨y,hy,he⟩ := hF
  have hyG : y∈projection principalSix ⁻¹' (projection principalSix '' flagFace G) := by
    change projection principalSix y ∈ projection principalSix '' flagFace G
    rw [he]
    exact hG
  rw [projection_flagFace_preimage] at hyG
  obtain ⟨⟨H,a,rfl⟩,hH⟩ := Set.mem_iUnion.mp hyG
  have h := flagFace_unique hy hH
  rw [h,flagBase_smul]

theorem cornerBase_covered : cornerBase=⋃ F : Flag,flagBase F := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨F,hF⟩ := (cornerLocus_iff y).mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨F,?_⟩
    rw [flagBase_eq_preimage]
    exact ⟨y.val,hF,rfl⟩
  · intro hx
    obtain ⟨F,hF⟩ := Set.mem_iUnion.mp hx
    exact flagBase_subset_corner F hF

abbrev CornerComponent := Set.range flagBase

def componentFlag (C : CornerComponent) : Flag := C.property.choose

theorem componentFlag_spec (C : CornerComponent) : flagBase (componentFlag C)=C.val :=
  C.property.choose_spec

abbrev CornerSource := Σ C : CornerComponent, FlagFaceOrbit (componentFlag C)

def assembledSumCollar : (Σ C : CornerComponent, FlagFaceOrbit (componentFlag C) × ℝ) → BoundaryBase :=
  fun p => flagCollarBase (componentFlag p.1) p.2

def assembledCollar : CornerSource × ℝ → BoundaryBase :=
  assembledSumCollar ∘ (Homeomorph.sigmaProdDistrib
    (X := fun C => FlagFaceOrbit (componentFlag C)) (Y := ℝ))

theorem assembledCollar_continuous : Continuous assembledCollar := by
  have h : Continuous assembledSumCollar :=
    continuous_sigma (fun C => flagCollarBase_continuous (componentFlag C))
  exact h.comp (Homeomorph.sigmaProdDistrib
    (X := fun C => FlagFaceOrbit (componentFlag C)) (Y := ℝ)).continuous

theorem assembledCollar_open : IsOpenMap assembledCollar := by
  have h : IsOpenMap assembledSumCollar :=
    isOpenMap_sigma.mpr (fun C => flagCollarBase_open (componentFlag C))
  exact h.comp (Homeomorph.sigmaProdDistrib
    (X := fun C => FlagFaceOrbit (componentFlag C)) (Y := ℝ)).isOpenMap

theorem assembledCollar_corner (x : CornerSource) (t : ℝ) :
    assembledCollar (x,t) ∈ cornerBase ↔ t=0 :=
  flagCollarBase_corner _ _ _

def cornerSourceToBase : CornerSource → cornerBase :=
  fun x => ⟨assembledCollar (x,0),(assembledCollar_corner x 0).mpr rfl⟩

theorem cornerSourceToBase_continuous : Continuous cornerSourceToBase :=
  (assembledCollar_continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

theorem cornerSourceToBase_injective : Function.Injective cornerSourceToBase := by
  rintro ⟨C,x⟩ ⟨D,y⟩ he
  have he' := congrArg Subtype.val he
  have hC : assembledCollar (⟨C,x⟩,0) ∈ flagBase (componentFlag C) := ⟨x,rfl⟩
  have hD : assembledCollar (⟨C,x⟩,0) ∈ flagBase (componentFlag D) := ⟨y,he'.symm⟩
  have hCD : C=D := Subtype.ext (by
    rw [←componentFlag_spec C,←componentFlag_spec D]
    exact flagBase_eq_of_mem hC hD)
  subst D
  exact congrArg (Sigma.mk C) (flagCollarBase_zero_injective _ he')

theorem cornerSourceToBase_surjective : Function.Surjective cornerSourceToBase := by
  rintro ⟨x,hx⟩
  rw [cornerBase_covered] at hx
  obtain ⟨F,hF⟩ := Set.mem_iUnion.mp hx
  let C : CornerComponent := ⟨flagBase F,⟨F,rfl⟩⟩
  have hc : x∈flagBase (componentFlag C) := by rw [componentFlag_spec]; exact hF
  obtain ⟨q,hq⟩ := hc
  exact ⟨⟨C,q⟩,Subtype.ext hq⟩

/-- The zero map is open in the corner subspace because the product map is open and its
preimage of the actual corner locus is precisely its zero section. -/
theorem cornerSourceToBase_open : IsOpenMap cornerSourceToBase := by
  intro U hU
  have he : cornerSourceToBase '' U = Subtype.val ⁻¹'
      (assembledCollar '' (U ×ˢ Set.univ)) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(y,0),⟨hy,Set.mem_univ _⟩,rfl⟩
    · rintro ⟨⟨y,t⟩,⟨hy,_⟩,ht⟩
      have hz : t=0 := (assembledCollar_corner y t).mp (ht ▸ x.property)
      subst t
      exact ⟨y,hy,Subtype.ext ht⟩
  rw [he]
  exact (assembledCollar_open _ (hU.prod isOpen_univ)).preimage continuous_subtype_val

def cornerSourceHomeomorph : CornerSource ≃ₜ cornerBase :=
  (Equiv.ofBijective cornerSourceToBase
    ⟨cornerSourceToBase_injective,cornerSourceToBase_surjective⟩).toHomeomorphOfContinuousOpen
      cornerSourceToBase_continuous cornerSourceToBase_open

instance cornerSource_compact : CompactSpace CornerSource := by
  let := isCompact_iff_compactSpace.mp cornerBase_compact
  exact cornerSourceHomeomorph.symm.compactSpace

theorem assembledCollar_locallyInjective : IsLocallyInjective assembledCollar := by
  rintro ⟨⟨C,x⟩,t⟩
  obtain ⟨V,hV,hxt,hi⟩ := flagCollarBase_locallyInjective (componentFlag C) (x,t)
  let i : FlagFaceOrbit (componentFlag C) × ℝ → CornerSource × ℝ :=
    Prod.map (@Sigma.mk CornerComponent (fun C => FlagFaceOrbit (componentFlag C)) C) id
  have ho : IsOpenMap i := isOpenMap_sigmaMk.prodMap IsOpenMap.id
  refine ⟨i '' V,ho V hV,⟨(x,t),hxt,rfl⟩,?_⟩
  rintro _ ⟨p,hp,rfl⟩ _ ⟨q,hq,rfl⟩ he
  exact congrArg i (hi hp hq he)

/-- A single positive radius gives a global embedded collar of all actual corner orbits. -/
theorem assembledCollar_exists_strip :
    ∃ ε : ℝ, 0 < ε ∧
      IsOpenEmbedding ((Set.univ ×ˢ Set.Ioo (-ε) ε).domRestrict assembledCollar) := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  apply CompactEmbeddingNeighborhood.exists_strip_open_embedding assembledCollar
    assembledCollar_continuous assembledCollar_open
  · intro x y h
    exact cornerSourceToBase_injective (Subtype.ext h)
  · intro x
    exact assembledCollar_locallyInjective (x,0)

end TernaryPoly.SymmetricSpaceBoundaryMV
