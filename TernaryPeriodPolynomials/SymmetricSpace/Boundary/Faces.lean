module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FacesStabilizers

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFaces
open OrdinaryIncidence SymmetricSpacePositive SymmetricSpaceFlagCoordinates
open SymmetricSpaceRationalAction SymmetricSpaceRationalCharts SymmetricSpaceRationalGluing

/-- The direct-frame label convention agrees exactly with the original normalized real action. -/
theorem chart_frame_action (g : RationalGL) (S : Space) :
    chart g (cornerEmbedding S)=embedding (act (realRational g) S) := by
  have hc : chart 1 (cornerEmbedding S)=embedding S := by
    change chart 1 (cornerEmbedding S)=chart 1 (chartEmbedding 1 S)
    rw [chartEmbedding_apply]
    simp
  calc
    chart g (cornerEmbedding S)=leftAction g (chart 1 (cornerEmbedding S)) := by
      rw [leftAction_chart,mul_one]
    _=embedding (act (realRational g) S) := by rw [hc,leftAction_embedding]

/-- Exact standard-coordinate preimage of every intrinsic rational line-face. -/
theorem lineFace_chart_preimage (L : Line) (g : RationalGL) :
    chart g ⁻¹' lineFace L={p : Corner | p.2.1.val=0 ∧ lineLabel g=L} :=
  Set.ext (lineFace_chart_iff L g)

/-- Exact standard-coordinate preimage of every intrinsic rational plane-face. -/
theorem planeFace_chart_preimage (P : Plane) (g : RationalGL) :
    chart g ⁻¹' planeFace P={p : Corner | p.2.2.val=0 ∧ planeLabel g=P} :=
  Set.ext (planeFace_chart_iff P g)

/-- The literal full-flag intersection criterion combines both zero roots and both rational labels. -/
theorem flagFace_chart_preimage (L : Line) (P : Plane) (g : RationalGL) :
    chart g ⁻¹' (lineFace L ∩ planeFace P)=
      {p : Corner | (p.2.1.val=0 ∧ p.2.2.val=0) ∧ lineLabel g=L ∧ planeLabel g=P} := by
  ext p
  change (chart g p∈lineFace L ∧ chart g p∈planeFace P) ↔
    (p.2.1.val=0 ∧ p.2.2.val=0) ∧ lineLabel g=L ∧ planeLabel g=P
  rw [lineFace_chart_iff,planeFace_chart_iff]
  tauto

/-- These closed rational faces cover precisely the actual boundary of the gluing. -/
theorem boundary_eq_face_union : (Set.range embedding)ᶜ=
    (⋃ L : Line,lineFace L) ∪ (⋃ P : Plane,planeFace P) := by
  ext x
  simpa only [Set.mem_compl_iff,Set.mem_union,Set.mem_iUnion] using boundary_iff_faces x

end TernaryPoly.SymmetricSpaceBoundaryFaces
