module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Scaling
public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Presentation
public import TernaryPeriodPolynomials.Building.BoundaryApartments.BadEdgeOrbit

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def integralColumnSigns (signs : Fin 3 → ℤˣ) : IntegralGL3 :=
  integralUpperDiagonal (signs 0, signs 1) * lastColumnSign (signs 2)

theorem integralColumnSigns_apply (frame : IntegralGL3) (signs : Fin 3 → ℤˣ)
    (row column : Fin 3) :
    (frame * integralColumnSigns signs).val row column =
      (signs column : ℤ) * frame.val row column := by
  fin_cases column <;>
    simp [integralColumnSigns, integralUpperDiagonal, lastColumnSign,
      Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem good_integral_frame_normalization (frame : IntegralGL3)
    (columns_good : ∀ column, (frame.val 2 column : ZMod 3) ≠ 0) :
    ∃ normalized : IntegralGL3,
      (∀ column, (normalized.val 2 column : ZMod 3) = 1) ∧
      apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) normalized) =
        apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) := by
  choose signs signs_property using fun column =>
    nonzero_modThree_sign (frame.val 2 column) (columns_good column)
  refine ⟨frame * integralColumnSigns signs, ?_, ?_⟩
  · intro column
    rw [integralColumnSigns_apply, Int.cast_mul, mul_comm]
    exact signs_property column
  · symm
    apply apartment_eq_of_scaled_columns _ _ (fun column => ((signs column : ℤ) : ℚ))
    intro row column
    change (((frame * integralColumnSigns signs).val row column : ℤ) : ℚ) =
      ((signs column : ℤ) : ℚ) * (frame.val row column : ℚ)
    rw [integralColumnSigns_apply, Int.cast_mul]

theorem good_unimodular_apartment_in_presentation (frame : IntegralGL3)
    (columns_good : ∀ column, (frame.val 2 column : ZMod 3) ≠ 0) :
    ∃ symbols : ApartmentSymbols,
      (apartmentPresentationMap symbols).val =
        apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame) := by
  obtain ⟨normalized, normalized_columns, apartment_eq⟩ :=
    good_integral_frame_normalization frame columns_good
  refine ⟨Finsupp.single (frameTransition normalized normalized_columns) 1, ?_⟩
  simp only [apartmentPresentationMap, Finsupp.linearCombination_single, one_smul]
  have orbit := normalizedApartmentCycle_orbit normalized normalized_columns
  change normalizedApartmentCycle normalized normalized_columns =
    translateGoodCycle (frameTransition normalized normalized_columns) referenceApartment at orbit
  rw [← orbit]
  exact apartment_eq

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
