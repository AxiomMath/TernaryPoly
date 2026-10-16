module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.VectorDescent

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem normalized_good_vector_in_line (line : Flags .line) (good : GoodFlag .line line) :
    ∃ vector : NormalizedGoodVector, IntegralVectorInFlag .line line vector.val := by
  obtain ⟨vector, ⟨frame, same, weights, weights_zero, combination⟩, vector_good⟩ := good
  obtain ⟨sign, normalized⟩ := nonzero_modThree_sign (vector 2) vector_good
  refine ⟨⟨fun row => (sign : ℤ) * vector row, ?_⟩,
    frame, same, ((sign : ℤ) : ℚ) • weights, ?_, ?_⟩
  · simpa only [Int.cast_mul, mul_comm] using normalized
  · simp only [Pi.smul_apply, smul_eq_mul, weights_zero, mul_zero, and_self]
  · rw [Matrix.mulVec_smul, combination]
    ext row
    simp

def goodLineRepresentative (line : Flags .line) : NormalizedGoodVector := by
  classical
  exact if good : GoodFlag .line line then Classical.choose (normalized_good_vector_in_line line good)
  else ⟨![0, 0, 1], by decide⟩

theorem goodLineRepresentative_in_line (line : Flags .line) (good : GoodFlag .line line) :
    IntegralVectorInFlag .line line (goodLineRepresentative line).val := by
  rw [goodLineRepresentative, dite_eq_left good]
  exact Classical.choose_spec (normalized_good_vector_in_line line good)

theorem goodLineRepresentative_multiple (frame : RationalGL3)
    (good : GoodFlag .line (QuotientGroup.mk frame)) :
    ∃ scalar : ℚ, ∀ row,
      ((goodLineRepresentative (QuotientGroup.mk frame)).val row : ℚ) = scalar * frame.val row 0 := by
  obtain ⟨representative, same, weights, weights_zero, combination⟩ :=
    goodLineRepresentative_in_line (QuotientGroup.mk frame) good
  obtain ⟨scalar, columns⟩ := firstColumn_multiple_of_line_eq frame representative same.symm
  refine ⟨weights 0 * scalar, ?_⟩
  intro row
  have entry := congrFun combination row
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, weights_zero.1, weights_zero.2,
    mul_zero, add_zero, columns] at entry
  rw [← entry]
  ring

theorem goodLineRepresentative_plane_coordinates (frame : RationalGL3) (edge : Edges)
    (plane : endpoint .plane edge = QuotientGroup.mk frame)
    (good : GoodFlag .line (endpoint .line edge)) :
    goodVectorCoordinates frame (goodLineRepresentative (endpoint .line edge)) 2 = 0 := by
  obtain ⟨representative, same, weights, weights_zero, combination⟩ :=
    goodLineRepresentative_in_line (endpoint .line edge) good
  have incident := incident_firstColumn_weight frame representative edge plane same.symm
  rw [goodVectorCoordinates, ← combination, Matrix.mulVec_mulVec]
  change ((frame⁻¹ * representative).val *ᵥ weights) 2 = 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, weights_zero.1, weights_zero.2,
    incident, zero_mul, mul_zero, add_zero]

theorem goodTripleHeight_singular (triple : OrderedTriple NormalizedGoodVector)
    (singular : ((goodTripleMatrix triple).map (Int.castRingHom ℚ)).det = 0) :
    goodTripleHeight triple = 0 := by
  have cast_height := goodTripleHeight_cast triple
  rw [singular, abs_zero] at cast_height
  exact_mod_cast cast_height

theorem goodTripleHeight_same_plane (first second third : Edges)
    (first_good : GoodFlag .line (endpoint .line first))
    (second_good : GoodFlag .line (endpoint .line second))
    (third_good : GoodFlag .line (endpoint .line third))
    (second_plane : endpoint .plane second = endpoint .plane first)
    (third_plane : endpoint .plane third = endpoint .plane first) :
    goodTripleHeight (goodLineRepresentative (endpoint .line first),
      goodLineRepresentative (endpoint .line second), goodLineRepresentative (endpoint .line third)) = 0 := by
  induction first using Quotient.inductionOn with
  | _ frame =>
    have first_zero := goodLineRepresentative_plane_coordinates frame (QuotientGroup.mk frame) rfl first_good
    have second_zero := goodLineRepresentative_plane_coordinates frame second second_plane second_good
    have third_zero := goodLineRepresentative_plane_coordinates frame third third_plane third_good
    have formula := goodTripleHeight_coordinates frame
      (goodLineRepresentative (endpoint .line (QuotientGroup.mk frame)))
      (goodLineRepresentative (endpoint .line second)) (goodLineRepresentative (endpoint .line third))
    have determinant : (vectorTripleMatrix
        (goodVectorCoordinates frame (goodLineRepresentative (endpoint .line (QuotientGroup.mk frame))),
          goodVectorCoordinates frame (goodLineRepresentative (endpoint .line second)),
          goodVectorCoordinates frame (goodLineRepresentative (endpoint .line third)))).det = 0 := by
      simp [vectorTripleMatrix, Matrix.det_fin_three, first_zero, second_zero, third_zero]
    rw [determinant, abs_zero, zero_mul] at formula
    exact_mod_cast formula

theorem goodTripleHeight_scaled_pair (a a' b : NormalizedGoodVector) (scalar : ℚ)
    (scaled : ∀ row, (a'.val row : ℚ) = scalar * (a.val row : ℚ)) :
    goodTripleHeight (a, a', b) = 0 := by
  apply goodTripleHeight_singular
  simp [goodTripleMatrix, vectorTripleMatrix, Matrix.det_fin_three, scaled]
  ring

theorem goodTripleValue_scale_first (a a' b c : NormalizedGoodVector) (scalar : ℚ)
    (scaled : ∀ row, (a'.val row : ℚ) = scalar * (a.val row : ℚ)) :
    goodTripleValue (a', b, c) = goodTripleValue (a, b, c) := by
  have relation := goodTripleValue_relation a a' b c
  rw [goodTripleValue_zero _ (goodTripleHeight_scaled_pair a a' c scalar scaled),
    goodTripleValue_zero _ (goodTripleHeight_scaled_pair a a' b scalar scaled), add_zero, sub_zero] at relation
  exact sub_eq_zero.mp relation

theorem goodTripleValue_scale_second (a b b' c : NormalizedGoodVector) (scalar : ℚ)
    (scaled : ∀ row, (b'.val row : ℚ) = scalar * (b.val row : ℚ)) :
    goodTripleValue (a, b', c) = goodTripleValue (a, b, c) := by
  rw [← goodTripleValue_cyclic a b' c, goodTripleValue_scale_first b b' c a scalar scaled,
    goodTripleValue_cyclic a b c]

theorem normalizedGoodVector_firstColumn_good (frame : RationalGL3) (vector : NormalizedGoodVector)
    (column : ∀ row, (vector.val row : ℚ) = frame.val row 0) (side : Side) :
    GoodFlag side (QuotientGroup.mk frame) := by
  refine ⟨vector.val, ⟨frame, rfl, Pi.single 0 1, ?_, ?_⟩, ?_⟩
  · cases side with
    | plane => rfl
    | line => exact ⟨rfl, rfl⟩
  · rw [Matrix.mulVec_single_one]
    ext row
    exact (column row).symm
  · rw [vector.property]
    exact one_ne_zero

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
