module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.SymmetricSpaceBoundaryFaceTopologyConsumer
public import Mathlib.Topology.LocalAtTarget

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaceTopology.RestrictedQuotient
open Topology
open scoped Pointwise
variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- The literal set stabilizer acts on its preserved subset. -/
instance subsetAction (F : Set X) : MulAction (MulAction.stabilizer G F) F where
  smul a x := ⟨a.val • x.val, by
    have h : a.val • F = F := a.property
    exact h.subset ⟨x.val, x.property, rfl⟩⟩
  one_smul x := Subtype.ext (one_smul G x.val)
  mul_smul a b x := Subtype.ext (mul_smul a.val b.val x.val)

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
@[simp] theorem subset_smul_val (F : Set X) (a : MulAction.stabilizer G F) (x : F) :
    (a • x).val = a.val • x.val := rfl

instance subsetContinuousAction (F : Set X) : ContinuousConstSMul (MulAction.stabilizer G F) F :=
  ⟨fun a => (continuous_const_smul a.val).comp continuous_subtype_val |>.subtype_mk _⟩

abbrev AmbientOrbit := Quotient (MulAction.orbitRel G X)
abbrev FaceOrbit (F : Set X) := Quotient (MulAction.orbitRel (MulAction.stabilizer G F) F)

def ambientProjection : X → AmbientOrbit (G := G) (X := X) := Quotient.mk _
def faceProjection (F : Set X) : F → FaceOrbit (G := G) F := Quotient.mk _

/-- Map from the actual subset into its literal image in the ambient orbit quotient. -/
def imageProjection (F : Set X) : F → (ambientProjection (G := G) '' F) :=
  fun x => ⟨ambientProjection x.val, x.val, x.property, rfl⟩

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem imageProjection_surjective (F : Set X) : Function.Surjective (imageProjection (G := G) F) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [ContinuousConstSMul G X] in
theorem imageProjection_continuous (F : Set X) : Continuous (imageProjection (G := G) F) :=
  (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _

def saturation (F : Set X) : Set X :=
  ambientProjection (G := G) ⁻¹' (ambientProjection (G := G) '' F)

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem subset_saturation (F : Set X) : F ⊆ saturation (G := G) F :=
  fun x hx => ⟨x, hx, rfl⟩

/-- An open subset of its saturation maps openly to its ambient quotient image. -/
theorem imageProjection_open (F : Set X)
    (hF : IsOpen (Subtype.val ⁻¹' F : Set (saturation (G := G) F))) :
    IsOpenMap (imageProjection (G := G) F) := by
  have hq : IsOpenQuotientMap (ambientProjection (G := G) (X := X)) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact ((hq.restrictPreimage _).isOpenMap.comp
    (IsOpenEmbedding.inclusion (subset_saturation (G := G) F) hF).isOpenMap)

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- A block subset has exactly the same induced orbit relation as its set-stabilizer action. -/
theorem imageProjection_eq_iff (F : Set X)
    (hblock : ∀ (a : G) (x : X), x ∈ F → a • x ∈ F → a ∈ MulAction.stabilizer G F)
    (x y : F) : imageProjection (G := G) F x = imageProjection F y ↔
      MulAction.orbitRel (MulAction.stabilizer G F) F x y := by
  constructor
  · intro he
    obtain ⟨a, ha⟩ := Quotient.exact (congrArg Subtype.val he)
    change a • y.val = x.val at ha
    have hm : a • y.val ∈ F := by rw [ha]; exact x.property
    exact ⟨⟨a, hblock a y.val y.property hm⟩, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    exact Subtype.ext (Quotient.sound ⟨a.val, congrArg Subtype.val ha⟩)

/-- Inclusion-induced map on the literal set-stabilizer quotient. -/
def quotientToImage (F : Set X) : FaceOrbit (G := G) F → (ambientProjection (G := G) '' F) :=
  Quotient.lift (imageProjection F) (by
    intro x y h
    obtain ⟨a, ha⟩ := h
    exact Subtype.ext (Quotient.sound ⟨a.val, congrArg Subtype.val ha⟩))

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
@[simp] theorem quotientToImage_mk (F : Set X) (x : F) :
    quotientToImage (G := G) F (faceProjection F x) = imageProjection F x := rfl

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem quotientToImage_bijective (F : Set X)
    (hblock : ∀ (a : G) (x : X), x ∈ F → a • x ∈ F → a ∈ MulAction.stabilizer G F) :
    Function.Bijective (quotientToImage (G := G) F) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    intro h
    exact Quotient.sound ((imageProjection_eq_iff F hblock _ _).mp h)
  · intro y
    obtain ⟨x, rfl⟩ := imageProjection_surjective F y
    exact ⟨faceProjection F x, rfl⟩

omit [ContinuousConstSMul G X] in
theorem quotientToImage_continuous (F : Set X) : Continuous (quotientToImage (G := G) F) :=
  continuous_quot_lift _ (imageProjection_continuous F)

theorem quotientToImage_open (F : Set X)
    (hF : IsOpen (Subtype.val ⁻¹' F : Set (saturation (G := G) F))) :
    IsOpenMap (quotientToImage (G := G) F) := by
  intro U hU
  have he : quotientToImage (G := G) F '' U =
      imageProjection F '' (faceProjection F ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
      exact ⟨x, hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨faceProjection F x, hx, rfl⟩
  rw [he]
  exact imageProjection_open F hF _ (hU.preimage continuous_quot_mk)

/-- The genuine topological comparison for a subset open in its saturation whose translates
are equal or disjoint. -/
def quotientImageHomeomorph (F : Set X)
    (hblock : ∀ (a : G) (x : X), x ∈ F → a • x ∈ F → a ∈ MulAction.stabilizer G F)
    (hF : IsOpen (Subtype.val ⁻¹' F : Set (saturation (G := G) F))) :
    FaceOrbit (G := G) F ≃ₜ (ambientProjection (G := G) '' F) :=
  (Equiv.ofBijective (quotientToImage F) (quotientToImage_bijective F hblock)).toHomeomorphOfContinuousOpen
    (quotientToImage_continuous F) (quotientToImage_open F hF)

@[simp] theorem quotientImageHomeomorph_mk (F : Set X)
    (hblock : ∀ (a : G) (x : X), x ∈ F → a • x ∈ F → a ∈ MulAction.stabilizer G F)
    (hF : IsOpen (Subtype.val ⁻¹' F : Set (saturation (G := G) F))) (x : F) :
    (quotientImageHomeomorph F hblock hF (faceProjection F x)).val = ambientProjection x.val := rfl

end TernaryPoly.SymmetricSpaceBoundaryFaceTopology.RestrictedQuotient
