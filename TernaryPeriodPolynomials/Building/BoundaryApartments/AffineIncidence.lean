module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.AffineTriangles

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem incident_firstColumn_weight (plane_frame line_frame : RationalGL3) (edge : Edges)
    (plane_eq : endpoint .plane edge = QuotientGroup.mk plane_frame)
    (line_eq : endpoint .line edge = QuotientGroup.mk line_frame) :
    (plane_frame⁻¹ * line_frame).val 2 0 = 0 := by
  induction edge using Quotient.inductionOn with
  | _ representative =>
    change (QuotientGroup.mk representative : Flags .plane) = QuotientGroup.mk plane_frame at plane_eq
    change (QuotientGroup.mk representative : Flags .line) = QuotientGroup.mk line_frame at line_eq
    have plane_entries := QuotientGroup.eq.mp plane_eq.symm
    change (plane_frame⁻¹ * representative).val 2 0 = 0 ∧
      (plane_frame⁻¹ * representative).val 2 1 = 0 at plane_entries
    obtain ⟨scalar, columns⟩ := firstColumn_multiple_of_line_eq representative line_frame line_eq
    have scaled : (plane_frame⁻¹ * line_frame).val 2 0 =
        scalar * (plane_frame⁻¹ * representative).val 2 0 := by
      simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, columns]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    rw [scaled, plane_entries.1, mul_zero]

theorem affinePair_of_incident_edges (first_edge second_edge : Edges)
    (same_plane : endpoint .plane first_edge = endpoint .plane second_edge)
    (first second : AffinePoint)
    (first_line : endpoint .line first_edge = affineLine first)
    (second_line : endpoint .line second_edge = affineLine second) :
    affinePair first second = Finsupp.single first_edge 1 - Finsupp.single second_edge 1 := by
  by_cases same : first = second
  · have edges_same : first_edge = second_edge :=
      edge_eq_of_same_endpoints same_plane (first_line.trans (same ▸ second_line.symm))
    rw [same, affinePair_self, edges_same, sub_self]
  induction first_edge using Quotient.inductionOn with
  | _ representative =>
    let frame := affinePairFrame first second same
    have first_column := (affinePairFrame_columns first second same).1
    have second_column := (affinePairFrame_columns first second same).2
    have first_weight := incident_firstColumn_weight representative (affineFrame first)
      (QuotientGroup.mk representative) rfl first_line
    have second_weight := incident_firstColumn_weight representative (affineFrame second)
      second_edge same_plane.symm second_line
    have plane_eq : (QuotientGroup.mk representative : Flags .plane) = QuotientGroup.mk frame := by
      apply QuotientGroup.eq.mpr
      constructor
      · calc
          (representative⁻¹ * frame).val 2 0 =
              (representative⁻¹ * affineFrame first).val 2 0 := by
            simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, first_column,
              affineFrame_firstColumn, frame]
          _ = 0 := first_weight
      · calc
          (representative⁻¹ * frame).val 2 1 =
              (representative⁻¹ * affineFrame second).val 2 0 := by
            simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, second_column,
              affineFrame_firstColumn, frame]
          _ = 0 := second_weight
    have frame_first_line : (QuotientGroup.mk frame : Flags .line) = affineLine first := by
      symm
      apply line_flag_eq_of_column 1
      intro row
      rw [one_mul, affineFrame_firstColumn]
      exact first_column row
    have frame_second_line : (QuotientGroup.mk (frame * swapFirstTwo) : Flags .line) =
        affineLine second := by
      symm
      apply line_flag_eq_of_column 1
      intro row
      rw [one_mul, affineFrame_firstColumn, frame_swap_firstColumn]
      exact second_column row
    have first_edge_eq : (QuotientGroup.mk frame : Edges) = QuotientGroup.mk representative := by
      apply edge_eq_of_same_endpoints
      · exact plane_eq.symm
      · exact frame_first_line.trans first_line.symm
    have second_edge_eq : (QuotientGroup.mk (frame * swapFirstTwo) : Edges) = second_edge := by
      apply edge_eq_of_same_endpoints
      · change (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane) = endpoint .plane second_edge
        rw [plane_flag_swap, ← plane_eq]
        exact same_plane
      · exact frame_second_line.trans second_line.symm
    rw [affinePair, dite_eq_left same]
    change framePair frame = _
    rw [framePair, first_edge_eq, second_edge_eq]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
