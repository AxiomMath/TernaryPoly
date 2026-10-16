module

public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesRoots
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.DenseEmbedding

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceFlagCoordinates
open SymmetricSpacePositive SymmetricSpaceParabolicCoordinates
open Topology Set

abbrev HalfLine := Set.Ici (0 : ℝ)
abbrev Corner := Vec3 × (HalfLine × HalfLine)

/-- The two open simple-root inequalities in the concrete closed quadrant. -/
def cornerInterior : Set Corner := {p | 0<p.2.1.val ∧ 0<p.2.2.val}

/-- The literal positive half-line inside the closed half-line. -/
def positiveHalf : Set HalfLine := {t | 0<t.val}

theorem positiveHalf_dense : Dense positiveHalf := by
  rw [Subtype.dense_iff]
  have himage : (Subtype.val '' positiveHalf : Set ℝ)=Set.Ioi 0 := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ht
    · intro hr; exact ⟨⟨r,show (0 : ℝ)≤r from le_of_lt hr⟩,hr,rfl⟩
  rw [himage,closure_Ioi]

theorem cornerInterior_open : IsOpen cornerInterior := by
  exact (isOpen_lt continuous_const
    (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).inter
    (isOpen_lt continuous_const
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

/-- Both simple roots can approach zero independently, and the positive locus is dense. -/
theorem cornerInterior_dense : Dense cornerInterior := by
  have heq : cornerInterior=(Set.univ : Set Vec3) ×ˢ (positiveHalf ×ˢ positiveHalf) := by
    ext p
    simp [cornerInterior,positiveHalf]
  rw [heq]
  exact dense_univ.prod (positiveHalf_dense.prod positiveHalf_dense)

/-- Positive simple-root parameters are exactly the open interior of the literal quadrant. -/
def positiveCornerHomeomorph : RootParameters ≃ₜ cornerInterior where
  toFun p := ⟨(p.1,(⟨p.2.1.val,show (0 : ℝ)≤p.2.1.val from le_of_lt p.2.1.property⟩,⟨p.2.2.val,show (0 : ℝ)≤p.2.2.val from le_of_lt p.2.2.property⟩)),
    p.2.1.property,p.2.2.property⟩
  invFun p := (p.val.1,(⟨p.val.2.1.val,p.property.1⟩,⟨p.val.2.2.val,p.property.2⟩))
  left_inv p := rfl
  right_inv p := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A single full-flag corner model has actual Space as its open dense interior. -/
def cornerHomeomorph : Space ≃ₜ cornerInterior := rootHomeomorph.trans positiveCornerHomeomorph

def cornerEmbedding (S : Space) : Corner := (cornerHomeomorph S).val

@[simp] theorem cornerEmbedding_unipotent (S : Space) :
    (cornerEmbedding S).1=(rootHomeomorph S).1 := rfl

@[simp] theorem cornerEmbedding_t1 (S : Space) :
    (cornerEmbedding S).2.1.val=(rootHomeomorph S).2.1.val := rfl

@[simp] theorem cornerEmbedding_t2 (S : Space) :
    (cornerEmbedding S).2.2.val=(rootHomeomorph S).2.2.val := rfl

theorem cornerEmbedding_range : Set.range cornerEmbedding=cornerInterior := by
  ext p
  constructor
  · rintro ⟨S,rfl⟩; exact (cornerHomeomorph S).property
  · intro hp
    obtain ⟨S,hS⟩ := cornerHomeomorph.surjective ⟨p,hp⟩
    exact ⟨S,congrArg Subtype.val hS⟩

theorem cornerEmbedding_isOpenEmbedding : IsOpenEmbedding cornerEmbedding :=
  cornerInterior_open.isOpenEmbedding_subtypeVal.comp cornerHomeomorph.isOpenEmbedding

theorem cornerEmbedding_denseRange : DenseRange cornerEmbedding := by
  rw [DenseRange,cornerEmbedding_range]
  exact cornerInterior_dense

end TernaryPoly.SymmetricSpaceFlagCoordinates
