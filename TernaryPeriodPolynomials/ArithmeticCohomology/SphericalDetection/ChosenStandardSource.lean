module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.HomogeneousNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.Restriction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realizesStandard_goodLine_primitive_for_source {degree : ℕ} (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (realizes : RealizesStandard data operator) (coordinate : boundarySummand data .plane)
    (good_zero : VanishesOnGood degree data.chi .line (operator coordinate).val)
    (source : SourceCochain degree) (source_cycle : MaximalCycles degree data.chi .plane)
    (source_cocycle : IsSourceCocycle data .plane source)
    (source_evaluates : Evaluates data .plane source source_cycle)
    (source_represents : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) source_cycle = coordinate.val) :
    ∃ (flat standard : ℂ → SourceCochain degree) (target_cycle : MaximalCycles degree data.chi .line)
      (primitive : cochains (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) 1),
      (∀ vertices monomial, IsFlatSection data (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial)) ∧
      flat cohomologicalPoint = source ∧
      (∀ vertices monomial, IsStandardContinuation
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
        (fun parameter argument => (standard parameter vertices argument).val.coeff monomial)) ∧
      (∀ vertices argument monomial, AnalyticAt ℂ
        (fun parameter => (standard parameter vertices argument).val.coeff monomial) cohomologicalPoint) ∧
      IsSourceCocycle data .line (standard cohomologicalPoint) ∧
      Evaluates data .line (standard cohomologicalPoint) target_cycle ∧
      (operator coordinate).val = classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line) target_cycle ∧
      ∀ vertices : Fin 3 → RationalGL3,
        standard cohomologicalPoint (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
          (rationalGroup rationalGoodLine) =
        (differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
          (rationalCoefficientComponent degree data.chi) primitive).val vertices := by
  have membership : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        source_cycle ∈ boundarySummand data .plane := by
    rw [source_represents]
    exact coordinate.property
  obtain ⟨flat, standard, flat_sections, endpoint, continuations, analytic,
    standard_cycle, target_cycle, target_evaluates, target_represents⟩ :=
    realizes source source_cocycle source_cycle source_evaluates membership
  have same_coordinate : (⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        source_cycle, membership⟩ : boundarySummand data .plane) = coordinate := Subtype.ext source_represents
  rw [same_coordinate] at target_represents
  have hzero := realizedGoodLineRestriction_zero data operator coordinate good_zero
  have hiff := realizedGoodLineRestriction_zero_iff data operator coordinate
    (standard cohomologicalPoint) target_cycle target_evaluates target_represents
  exact (hiff.mp hzero).elim fun primitive coboundary =>
    ⟨flat, standard, target_cycle, primitive, flat_sections, endpoint, continuations,
      analytic, standard_cycle, target_evaluates, target_represents, coboundary⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
