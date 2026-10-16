module

public import TernaryPeriodPolynomials.SymmetricSpace.Plane.BordificationRadial
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.DenseEmbedding

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpacePlaneBordification
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates

abbrev HalfLine := Set.Ici (0 : ℝ)
/-- The actual one-plane partial bordification, with the reciprocal-square-root radial coordinate. -/
abbrev PlaneBordification := Vec2 × (BinarySpace × HalfLine)

def interior : Set PlaneBordification := {p | 0<p.2.2.val}
def boundary : Set PlaneBordification := {p | p.2.2.val=0}
abbrev PlaneInterior := interior
abbrev PlaneBoundary := boundary

theorem continuous_parameter : Continuous (fun p : PlaneBordification => p.2.2.val) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_snd)

theorem isOpen_interior : IsOpen interior := isOpen_lt continuous_const continuous_parameter

theorem isClosed_boundary : IsClosed boundary := isClosed_eq continuous_parameter continuous_const

theorem interior_or_boundary (p : PlaneBordification) : p∈interior ∨ p∈boundary := by
  have ht : 0≤p.2.2.val := p.2.2.property
  rcases ht.eq_or_lt with h|h
  · exact Or.inr h.symm
  · exact Or.inl h

/-- Forgetting only the redundant half-line membership proof identifies the positive interior. -/
def interiorProductHomeomorph : PlaneInterior ≃ₜ (Vec2 × (BinarySpace × PositiveScale)) where
  toFun p := (p.val.1,(p.val.2.1,⟨p.val.2.2.val,p.property⟩))
  invFun p := ⟨(p.1,(p.2.1,⟨p.2.2.val,show (0 : ℝ)≤p.2.2.val from le_of_lt p.2.2.property⟩)),p.2.2.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The exact original symmetric space is the t>0 interior of the partial bordification. -/
def spaceInteriorHomeomorph : Space ≃ₜ PlaneInterior :=
  (fullHorosphericalHomeomorph.trans
    ((Homeomorph.refl Vec2).prodCongr ((Homeomorph.refl BinarySpace).prodCongr radialHomeomorph))).trans
    interiorProductHomeomorph.symm

def embedding (S : Space) : PlaneBordification := (spaceInteriorHomeomorph S).val

@[simp] theorem embedding_unipotent (S : Space) : (embedding S).1=unipotent S.val := rfl
@[simp] theorem embedding_shape (S : Space) :
    (embedding S).2.1.val=binaryNormalize (schur S.val) := rfl
@[simp] theorem embedding_parameter (S : Space) :
    (embedding S).2.2.val=(Real.sqrt (schur S.val).trace)⁻¹ := rfl

theorem continuous_embedding : Continuous embedding :=
  continuous_subtype_val.comp spaceInteriorHomeomorph.continuous

theorem embedding_injective : Function.Injective embedding :=
  Subtype.val_injective.comp spaceInteriorHomeomorph.injective

theorem range_embedding : Set.range embedding=interior := by
  ext p
  constructor
  · rintro ⟨S,rfl⟩
    exact (spaceInteriorHomeomorph S).property
  · intro hp
    exact ⟨spaceInteriorHomeomorph.symm ⟨p,hp⟩,
      congrArg Subtype.val (spaceInteriorHomeomorph.apply_symm_apply ⟨p,hp⟩)⟩

/-- The zero-radial-coordinate boundary is exactly the unipotent vector and binary shape. -/
def boundaryHomeomorph : PlaneBoundary ≃ₜ (Vec2 × BinarySpace) where
  toFun p := (p.val.1,p.val.2.1)
  invFun p := ⟨(p.1,(p.2,⟨0,show (0 : ℝ)≤0 from le_rfl⟩)),rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact p.property.symm
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem dense_positive_halfLine : Dense {t : HalfLine | 0<t.val} := by
  intro t
  rw [closure_subtype]
  have heq : (Subtype.val : HalfLine → ℝ) '' {s : HalfLine | 0<s.val}=Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact hs
    · intro hx
      exact ⟨⟨x,show (0 : ℝ)≤x from le_of_lt hx⟩,hx,rfl⟩
  rw [heq,closure_Ioi]
  exact t.property

/-- The positive interior is dense in the actual partial bordification. -/
theorem dense_interior : Dense interior := by
  have heq : interior=(Set.univ : Set Vec2) ×ˢ
      ((Set.univ : Set BinarySpace) ×ˢ {t : HalfLine | 0<t.val}) := by
    ext p
    simp [interior]
  rw [heq]
  exact (dense_univ : Dense (Set.univ : Set Vec2)).prod
    ((dense_univ : Dense (Set.univ : Set BinarySpace)).prod dense_positive_halfLine)

theorem denseRange_embedding : DenseRange embedding :=
  dense_interior.denseRange_val.comp spaceInteriorHomeomorph.surjective.denseRange
    continuous_subtype_val

end TernaryPoly.SymmetricSpacePlaneBordification
