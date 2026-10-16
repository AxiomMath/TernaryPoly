module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.Action
public import TernaryPeriodPolynomials.SymmetricSpace.Flag.CoordinatesCorner

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceRationalCharts
open SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction
open Topology

/-- The actual interior coordinates associated to a rational full-frame chart. -/
def chartHomeomorph (g : RationalGL) : Space ≃ₜ cornerInterior :=
  (rationalHomeomorph g⁻¹).trans cornerHomeomorph

/-- The rational chart's literal embedding of the actual symmetric space into Corner. -/
def chartEmbedding (g : RationalGL) (S : Space) : Corner := (chartHomeomorph g S).val

@[simp] theorem chartEmbedding_apply (g : RationalGL) (S : Space) :
    chartEmbedding g S=cornerEmbedding (act (realRational g⁻¹) S) := rfl

/-- Every rational chart has exactly the same actual positive interior. -/
theorem chartEmbedding_range (g : RationalGL) : Set.range (chartEmbedding g)=cornerInterior := by
  ext x
  constructor
  · rintro ⟨S,rfl⟩; exact (chartHomeomorph g S).property
  · intro hx
    obtain ⟨S,hS⟩ := (chartHomeomorph g).surjective ⟨x,hx⟩
    exact ⟨S,congrArg Subtype.val hS⟩

theorem chartEmbedding_isOpenEmbedding (g : RationalGL) : IsOpenEmbedding (chartEmbedding g) :=
  cornerInterior_open.isOpenEmbedding_subtypeVal.comp (chartHomeomorph g).isOpenEmbedding

theorem chartEmbedding_denseRange (g : RationalGL) : DenseRange (chartEmbedding g) := by
  rw [DenseRange,chartEmbedding_range]
  exact cornerInterior_dense

/-- The exact interior transition from chart g to chart h. -/
def interiorTransition (g h : RationalGL) : cornerInterior ≃ₜ cornerInterior :=
  (chartHomeomorph g).symm.trans (chartHomeomorph h)

@[simp] theorem interiorTransition_chart (g h : RationalGL) (S : Space) :
    interiorTransition g h (chartHomeomorph g S)=chartHomeomorph h S :=
  congrArg (chartHomeomorph h) ((chartHomeomorph g).symm_apply_apply S)

/-- The transition is literally normalized congruence by h⁻¹g in standard corner coordinates. -/
theorem interiorTransition_formula (g h : RationalGL) (x : cornerInterior) :
    interiorTransition g h x=
      cornerHomeomorph (act (realRational (h⁻¹*g)) (cornerHomeomorph.symm x)) := by
  change cornerHomeomorph (act (realRational h⁻¹)
      (act (realRational g⁻¹)⁻¹ (cornerHomeomorph.symm x)))=_
  rw [←act_mul,←map_inv,inv_inv,←map_mul]

/-- The actual interior chart transitions satisfy the cocycle equation. -/
theorem interiorTransition_cocycle (g h k : RationalGL) (x : cornerInterior) :
    interiorTransition h k (interiorTransition g h x)=interiorTransition g k x :=
  congrArg (chartHomeomorph k) ((chartHomeomorph h).symm_apply_apply
    ((chartHomeomorph g).symm x))

/-- Arithmetic left multiplication agrees exactly with the rational chart indexing. -/
theorem chartEmbedding_left_action (a g : RationalGL) (S : Space) :
    chartEmbedding (a*g) (act (realRational a) S)=chartEmbedding g S := by
  simp only [chartEmbedding_apply,mul_inv_rev,map_mul,map_inv,←act_mul]
  rw [mul_assoc,inv_mul_cancel,mul_one]

end TernaryPoly.SymmetricSpaceRationalCharts
