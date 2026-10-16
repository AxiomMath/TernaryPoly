module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticRelativeGraphs
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.ProperFinite

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalGluing
open SymmetricSpaceRationalAction SymmetricSpaceRationalCharts SymmetricSpaceCornerSeparation
open Topology

/-- A compact set contained in the actual chart interior pulls back to a compact set in Space. -/
theorem compact_chart_interior_preimage (a : RationalGL) (K : Set Corner)
    (hK : IsCompact K) (hKi : K⊆cornerInterior) :
    IsCompact ((chartHomeomorph a).symm '' ((Subtype.val : cornerInterior → Corner) ⁻¹' K)) := by
  have hcompact : IsCompact ((Subtype.val : cornerInterior → Corner) ⁻¹' K) :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      hK (by simpa only [Subtype.range_coe] using hKi)
  exact hcompact.image (chartHomeomorph a).symm.continuous

/-- The exact global point represented by positive chart coordinates. -/
theorem chart_interior_point (a : RationalGL) (p : cornerInterior) :
    embedding ((chartHomeomorph a).symm p)=chart a p.val := by
  have he : chartEmbedding a ((chartHomeomorph a).symm p)=p.val :=
    congrArg Subtype.val ((chartHomeomorph a).apply_symm_apply p)
  rw [←chart_embedding a,he]

/-- Arithmetic equality in positive charts is the literal original action on actual Space. -/
theorem interior_chart_action (a b : RationalGL) (g : IntegralGL) (p q : cornerInterior)
    (he : integralAction g (chart a p.val)=chart b q.val) :
    act (SymmetricSpaceArithmeticProper.realIntegral g) ((chartHomeomorph a).symm p)=
      (chartHomeomorph b).symm q := by
  apply embedding_injective
  change embedding (act (GeneralLinearGroup.map (Int.castRingHom ℝ) g) _) = _
  rw [←integralAction_embedding,chart_interior_point,chart_interior_point]
  exact he

/-- Compact source and target corner sets wholly inside the actual interior have finite transporters. -/
theorem compact_interior_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) (hKi : K⊆cornerInterior) (hLi : L⊆cornerInterior) :
    {g : IntegralGL | ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  let C := (chartHomeomorph a).symm '' ((Subtype.val : cornerInterior → Corner) ⁻¹' K)
  let D := (chartHomeomorph b).symm '' ((Subtype.val : cornerInterior → Corner) ⁻¹' L)
  have hC : IsCompact C := compact_chart_interior_preimage a K hK hKi
  have hD : IsCompact D := compact_chart_interior_preimage b L hL hLi
  refine (SymmetricSpaceArithmeticProper.compact_transporter_finite C D hC hD).subset ?_
  rintro g ⟨p,hp,q,hq,he⟩
  let P : cornerInterior := ⟨p,hKi hp⟩
  let Q : cornerInterior := ⟨q,hLi hq⟩
  refine ⟨(chartHomeomorph a).symm P,⟨P,hp,rfl⟩,?_⟩
  rw [interior_chart_action a b g P Q he]
  exact ⟨Q,hq,rfl⟩

end TernaryPoly.SymmetricSpaceGluedArithmetic
