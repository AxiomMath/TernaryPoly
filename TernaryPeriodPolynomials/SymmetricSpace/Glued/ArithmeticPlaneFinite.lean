module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticRelativeGraphs

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction SymmetricSpaceCornerSeparation

/-- Compact-chart arithmetic transporters with actual plane relative matrix are finite. -/
theorem compact_plane_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | realRational (relative a b g)∈planeStabilizer ∧
      ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  obtain ⟨d,hd,hden⟩ := relative_hasIntegralDenominator a b
  let D := |(realRational b⁻¹).val.det| * |(realRational a).val.det|
  have hD : 0<D := mul_pos (abs_pos.mpr (realRational b⁻¹).det_ne_zero)
    (abs_pos.mpr (realRational a).det_ne_zero)
  obtain ⟨M,hM,hbox⟩ := compact_corner_bound K L hK hL
  obtain ⟨R,hR⟩ := real_plane_entry_bound d hd D M hD hM
  refine (finite_relative_entry_bound a b R).subset ?_
  rintro g ⟨hr,p,hp,q,hq,he⟩
  obtain ⟨hdom,ht⟩ := (integral_chart_eq_iff_graph a b g p q).mp he
  have hpB := hbox p (Or.inl hp)
  have hqB := hbox q (Or.inr hq)
  have hdet : |(realRational (relative a b g)).val.det|≤D := (relative_det_abs a b g).le
  have hb := hR ⟨realRational (relative a b g),hr⟩ ⟨p,hdom⟩ (hden g) hdet hpB.1
    (by simpa only [ht] using hqB.1) hpB.2.1 (by simpa only [ht] using hqB.2.1)
  exact hb

end TernaryPoly.SymmetricSpaceGluedArithmetic
