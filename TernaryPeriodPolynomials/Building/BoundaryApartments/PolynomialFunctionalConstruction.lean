module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.QuotientEdgeFunctional

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def normalizedFrameTriple (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) : OrderedTriple NormalizedGoodVector :=
  (⟨frame.val.col 0, normalized 0⟩, ⟨frame.val.col 1, normalized 1⟩, ⟨frame.val.col 2, normalized 2⟩)

theorem normalizedFrameTriple_matrix (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    goodTripleMatrix (normalizedFrameTriple frame normalized) = frame.val := by
  ext row column
  fin_cases column <;> rfl

theorem normalizedFrameTriple_height (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    goodTripleHeight (normalizedFrameTriple frame normalized) = 1 := by
  rw [goodTripleHeight, normalizedFrameTriple_matrix]
  exact Int.isUnit_iff_natAbs_eq.mp ((Matrix.isUnit_iff_isUnit_det _).mp frame.isUnit)

theorem goodTripleInitial_normalizedFrame (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    goodTripleInitial (normalizedFrameTriple frame normalized) = normalizedApartmentClass frame normalized := by
  let change_frame := goodTripleChange (normalizedFrameTriple frame normalized)
    (normalizedFrameTriple_height frame normalized)
  have change_entries : change_frame.val.val = referenceFrame.inv * frame.val := by
    rw [goodTripleChange_val, normalizedFrameTriple_matrix]
  have change_eq : change_frame.val = referenceFrame⁻¹ * frame := by
    apply Units.ext
    exact change_entries
  rw [goodTripleInitial, normalizedFrameTriple_matrix,
    normalizedMatrixClass_eq 1 _ change_frame change_entries, frameChangeClass, one_mul,
    normalizedApartmentClass]
  congr 1
  apply Subtype.ext
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (frameConjugate change_frame.val) =
    GeneralLinearGroup.map (Int.castRingHom ℚ) (frame * referenceFrame⁻¹)
  rw [change_eq, frameConjugate, mul_inv_cancel_left]

theorem apartmentQuotientEdgeMap_normalizedFrame (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    apartmentQuotientEdgeMap (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame)) =
      normalizedApartmentClass frame normalized := by
  let triple := normalizedFrameTriple frame normalized
  rw [apartmentQuotientEdgeMap_apartment _ triple.1 triple.2.1 triple.2.2
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
    goodTripleValue_initial triple (by rw [normalizedFrameTriple_height]),
    goodTripleInitial_normalizedFrame]

theorem apartmentQuotientValue_normalizedFrame {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) (frame : IntegralGL3)
    (normalized : ∀ column, (frame.val 2 column : ZMod 3) = 1) :
    apartmentQuotientValue solution (normalizedApartmentClass frame normalized) =
      framePolynomial degree frame polynomial := by
  change apartmentSymbolValue polynomial (Finsupp.single (frameTransition frame normalized) 1) = _
  rw [apartmentSymbolValue, Finsupp.linearCombination_single, one_smul,
    ← framePolynomial_orbit]

def polynomialEdgeFunctional {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) : EdgeChains →ₗ[ℂ] HomogeneousPoly degree :=
  (apartmentQuotientValue solution).comp apartmentQuotientEdgeMap

theorem polynomialEdgeFunctional_property {degree : ℕ} {polynomial : HomogeneousPoly degree}
    (solution : SymmetricSolution polynomial) :
    IsPolynomialFunctional polynomial (polynomialEdgeFunctional solution) := by
  apply polynomialFunctional_of_normalization
  intro frame normalized
  change apartmentQuotientValue solution
    (apartmentQuotientEdgeMap (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frame))) = _
  rw [apartmentQuotientEdgeMap_normalizedFrame frame normalized,
    apartmentQuotientValue_normalizedFrame]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
