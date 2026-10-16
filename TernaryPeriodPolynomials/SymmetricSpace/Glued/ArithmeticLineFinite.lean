module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticPlaneFinite

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceBorelCorner
open SymmetricSpaceRationalGluing SymmetricSpaceRationalAction SymmetricSpaceCornerSeparation
open SymmetricSpaceLineBordification

/-- Bounding inverse relative arithmetic matrices also gives a finite set of original matrices. -/
theorem finite_inverse_relative_entry_bound (a b : RationalGL) (R : ℝ) :
    {g : IntegralGL | ∀ i j,|((relative b a g⁻¹).val i j : ℝ)|≤R}.Finite := by
  refine Set.Finite.of_injOn (f := fun g : IntegralGL => g⁻¹) ?_ inv_injective.injOn
    (finite_relative_entry_bound b a R)
  intro g hg
  exact hg

/-- Compact-chart arithmetic transporters in the actual line subgroup are finite. -/
theorem compact_line_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | realRational (relative a b g)∈lineStabilizer ∧
      ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  obtain ⟨d,hd,hden⟩ := relative_hasIntegralDenominator b a
  let D := |(realRational a⁻¹).val.det| * |(realRational b).val.det|
  have hD : 0<D := mul_pos (abs_pos.mpr (realRational a⁻¹).det_ne_zero)
    (abs_pos.mpr (realRational b).det_ne_zero)
  obtain ⟨M,hM,hbox⟩ := compact_corner_bound K L hK hL
  let N := M^2+M
  have hMN : M≤N := by dsimp [N]; nlinarith only [sq_nonneg M]
  obtain ⟨R,hR⟩ := real_plane_entry_bound d hd D N hD (hM.trans hMN)
  refine (finite_inverse_relative_entry_bound a b R).subset ?_
  rintro g ⟨hr,p,hp,q,hq,he⟩
  let r := realRational (relative a b g)
  have hinv : r⁻¹=realRational (relative b a g⁻¹) := by
    change (realRational (relative a b g))⁻¹=_
    rw [←map_inv,relative_inv]
  have hddual : HasIntegralDenominator d (dualGL r) :=
    dualGL_hasIntegralDenominator d r (by rw [hinv]; exact hden g⁻¹)
  have hdetdual : |(dualGL r).val.det|≤D := by
    rw [dualGL_det_abs,hinv,relative_det_abs]
  have hplane : dualGL r∈planeStabilizer :=
    (mem_planeStabilizer_iff _).mpr ((dualGL_plane_iff_line r).mpr hr)
  obtain ⟨hdom,ht⟩ := fullGraph_dual r ((integral_chart_eq_iff_graph a b g p q).mp he)
  change (transition (dualGL r) ⟨dualCorner p,hdom⟩).val=dualCorner q at ht
  have hpB := hbox p (Or.inl hp)
  have hqB := hbox q (Or.inr hq)
  have hpd := dualCorner_coordinate_bound M (zero_le_one.trans hM) p hpB.1
  have hqd := dualCorner_coordinate_bound M (zero_le_one.trans hM) q hqB.1
  have hb := hR ⟨dualGL r,hplane⟩ ⟨dualCorner p,hdom⟩ hddual hdetdual hpd
    (by simpa only [ht] using hqd) (hpB.2.2.trans hMN)
    (by change (transition (dualGL r) ⟨dualCorner p,hdom⟩).val.2.1.val≤N
        rw [ht]; exact hqB.2.2.trans hMN)
  intro i j
  have hh := hb j.rev i.rev
  change |(dualGL r).val j.rev i.rev|≤R at hh
  rw [dualGL_entry,Fin.rev_rev,Fin.rev_rev,hinv] at hh
  exact hh

end TernaryPoly.SymmetricSpaceGluedArithmetic
