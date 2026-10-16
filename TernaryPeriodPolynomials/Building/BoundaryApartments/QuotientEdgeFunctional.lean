module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.LineRepresentatives

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def goodVectorBase : NormalizedGoodVector := ⟨![0, 0, 1], by decide⟩

def apartmentQuotientEdgeValue (edge : Edges) : ApartmentQuotient :=
  goodTripleValue (goodLineRepresentative (endpoint .line edge),
    goodLineRepresentative (endpoint .line (goodPlaneEdge (endpoint .plane edge))), goodVectorBase)

def apartmentQuotientEdgeMap : EdgeChains →ₗ[ℂ] ApartmentQuotient :=
  Finsupp.linearCombination ℂ apartmentQuotientEdgeValue

theorem apartmentQuotientEdgeMap_single (edge : Edges) :
    apartmentQuotientEdgeMap (Finsupp.single edge 1) = apartmentQuotientEdgeValue edge := by
  simp only [apartmentQuotientEdgeMap, Finsupp.linearCombination_single, one_smul]

theorem apartmentQuotientEdgeMap_incident_pair (first second : Edges)
    (first_good : GoodFlag .line (endpoint .line first))
    (second_good : GoodFlag .line (endpoint .line second))
    (plane_good : GoodFlag .plane (endpoint .plane first))
    (same_plane : endpoint .plane second = endpoint .plane first) :
    apartmentQuotientEdgeMap (Finsupp.single first 1 - Finsupp.single second 1) =
      goodTripleValue (goodLineRepresentative (endpoint .line first),
        goodLineRepresentative (endpoint .line second), goodVectorBase) := by
  let plane_edge := goodPlaneEdge (endpoint .plane first)
  have plane_edge_spec := goodPlaneEdge_spec (endpoint .plane first) plane_good
  have zero := goodTripleValue_zero _ (goodTripleHeight_same_plane first second plane_edge
    first_good second_good plane_edge_spec.2 same_plane plane_edge_spec.1)
  let a := goodLineRepresentative (endpoint .line first)
  let b := goodLineRepresentative (endpoint .line second)
  let c := goodLineRepresentative (endpoint .line plane_edge)
  have relation := goodTripleValue_relation a b c goodVectorBase
  change goodTripleValue (a, b, c) = 0 at zero
  rw [zero, sub_zero] at relation
  rw [map_sub, apartmentQuotientEdgeMap_single, apartmentQuotientEdgeMap_single]
  simp only [apartmentQuotientEdgeValue, same_plane]
  change goodTripleValue (a, c, goodVectorBase) - goodTripleValue (b, c, goodVectorBase) =
    goodTripleValue (a, b, goodVectorBase)
  calc
    _ = goodTripleValue (a, b, goodVectorBase) -
        (goodTripleValue (b, c, goodVectorBase) - goodTripleValue (a, c, goodVectorBase) +
          goodTripleValue (a, b, goodVectorBase)) := by abel
    _ = _ := by rw [relation, sub_zero]

theorem apartmentQuotientEdgeMap_framePair (frame : RationalGL3) (a b : NormalizedGoodVector)
    (first_column : ∀ row, (a.val row : ℚ) = frame.val row 0)
    (second_column : ∀ row, (b.val row : ℚ) = frame.val row 1) :
    apartmentQuotientEdgeMap (framePair frame) = goodTripleValue (a, b, goodVectorBase) := by
  have first_good := normalizedGoodVector_firstColumn_good frame a first_column .line
  have plane_good := normalizedGoodVector_firstColumn_good frame a first_column .plane
  have swapped_column (row : Fin 3) : (b.val row : ℚ) = (frame * swapFirstTwo).val row 0 := by
    rw [frame_swap_firstColumn]
    exact second_column row
  have second_good := normalizedGoodVector_firstColumn_good (frame * swapFirstTwo) b swapped_column .line
  rw [framePair, apartmentQuotientEdgeMap_incident_pair (QuotientGroup.mk frame)
    (QuotientGroup.mk (frame * swapFirstTwo)) first_good second_good plane_good
    (plane_flag_swap frame)]
  change goodTripleValue (goodLineRepresentative (QuotientGroup.mk frame),
    goodLineRepresentative (QuotientGroup.mk (frame * swapFirstTwo)), goodVectorBase) = _
  obtain ⟨first_scale, first_scaled⟩ := goodLineRepresentative_multiple frame first_good
  obtain ⟨second_scale, second_scaled⟩ := goodLineRepresentative_multiple (frame * swapFirstTwo) second_good
  rw [goodTripleValue_scale_first a _ _ _ first_scale (by
    intro row
    rw [first_scaled, first_column])]
  apply goodTripleValue_scale_second a b _ goodVectorBase second_scale
  intro row
  rw [second_scaled, swapped_column]

theorem apartmentQuotientEdgeMap_apartment (frame : RationalGL3) (a b c : NormalizedGoodVector)
    (first_column : ∀ row, (a.val row : ℚ) = frame.val row 0)
    (second_column : ∀ row, (b.val row : ℚ) = frame.val row 1)
    (third_column : ∀ row, (c.val row : ℚ) = frame.val row 2) :
    apartmentQuotientEdgeMap (apartment frame) = goodTripleValue (a, b, c) := by
  rw [apartment_eq_framePairs, map_add, map_add,
    apartmentQuotientEdgeMap_framePair frame a b first_column second_column,
    apartmentQuotientEdgeMap_framePair (frame * Adelic.weyl) b c
      (by intro row; rw [frame_weyl_firstColumn]; exact second_column row)
      (by intro row; rw [frame_weyl_secondColumn]; exact third_column row),
    apartmentQuotientEdgeMap_framePair (frame * Adelic.weyl ^ 2) c a
      (by intro row; rw [frame_weylSquared_firstColumn]; exact third_column row)
      (by intro row; rw [frame_weylSquared_secondColumn]; exact first_column row),
    goodTripleValue_swap a c goodVectorBase]
  have relation := goodTripleValue_relation a b c goodVectorBase
  calc
    _ = goodTripleValue (a, b, c) +
        (goodTripleValue (b, c, goodVectorBase) - goodTripleValue (a, c, goodVectorBase) +
          goodTripleValue (a, b, goodVectorBase) - goodTripleValue (a, b, c)) := by abel
    _ = _ := by rw [relation, add_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
