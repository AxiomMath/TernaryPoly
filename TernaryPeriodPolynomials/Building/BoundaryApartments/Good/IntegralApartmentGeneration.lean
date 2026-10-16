module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.FullSubdivision
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.DeterminantReduction
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.IntegralNormalization

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

/-- Every integral frame with good columns reduces to normalized unimodular apartments. -/
theorem good_integral_matrixApartment_in_presentation (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (columns_good : ∀ column, (matrix 2 column : ZMod 3) ≠ 0) :
    ∃ symbols : ApartmentSymbols, (apartmentPresentationMap symbols).val =
      matrixApartment (matrix.map (Int.castRingHom ℚ)) := by
  apply good_integer_frame_induction
    (fun candidate => ∃ symbols : ApartmentSymbols, (apartmentPresentationMap symbols).val =
      matrixApartment (candidate.map (Int.castRingHom ℚ))) _ _ _ matrix columns_good
  · intro candidate singular
    refine ⟨0, ?_⟩
    rw [map_zero, matrixApartment_singular]
    · rfl
    · rw [← integer_matrix_det_cast, singular, Int.cast_zero]
  · intro candidate unit good
    obtain ⟨frame, rfl⟩ := unit
    obtain ⟨symbols, value⟩ := good_unimodular_apartment_in_presentation frame good
    refine ⟨symbols, ?_⟩
    change (apartmentPresentationMap symbols).val =
      matrixApartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame).val
    rw [matrixApartment_frame]
    exact value
  · intro candidate vector _ vector_good replacements
    by_cases singular : candidate.det = 0
    · refine ⟨0, ?_⟩
      rw [map_zero, matrixApartment_singular]
      · rfl
      · rw [← integer_matrix_det_cast, singular, Int.cast_zero]
    have rational_nonzero : (candidate.map (Int.castRingHom ℚ)).det ≠ 0 := by
      rw [← integer_matrix_det_cast]
      exact_mod_cast singular
    let frame := GeneralLinearGroup.mkOfDetNeZero
      (candidate.map (Int.castRingHom ℚ)) rational_nonzero
    have vector_nonzero : (fun index => (vector index : ℚ)) ≠ 0 := by
      intro zero_vector
      have entry := congrFun zero_vector 2
      change (vector 2 : ℚ) = 0 at entry
      have entry_zero : vector 2 = 0 := by exact_mod_cast entry
      exact vector_good (by rw [entry_zero, Int.cast_zero])
    have subdivision := matrixApartment_subdivision frame
      (fun index => (vector index : ℚ)) vector_nonzero
    obtain ⟨first, first_value⟩ := replacements 0
    obtain ⟨second, second_value⟩ := replacements 1
    obtain ⟨third, third_value⟩ := replacements 2
    refine ⟨first + second + third, ?_⟩
    simp only [map_add, Submodule.coe_add, first_value, second_value, third_value,
      Matrix.map_updateCol]
    exact subdivision.symm

theorem good_integral_apartment_in_presentation (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (frame : RationalGL3) (entries : frame.val = matrix.map (Int.castRingHom ℚ))
    (columns_good : ∀ column, (matrix 2 column : ZMod 3) ≠ 0) :
    ∃ symbols : ApartmentSymbols, (apartmentPresentationMap symbols).val = apartment frame := by
  obtain ⟨symbols, value⟩ := good_integral_matrixApartment_in_presentation matrix columns_good
  refine ⟨symbols, ?_⟩
  rw [← entries, matrixApartment_frame] at value
  exact value

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
