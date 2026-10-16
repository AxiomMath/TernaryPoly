module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.Comparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OrbitDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.Detection

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realizedGoodLineRestriction {degree : ℕ} (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line) :
    boundarySummand data .plane →ₗ[ℂ]
      H2 (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) :=
  ((flagRestriction data.chi .line (QuotientGroup.mk rationalGoodLine)).comp
    (boundarySummand data .line).subtype).comp operator

theorem realizedGoodLineRestriction_zero {degree : ℕ} (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (coordinate : boundarySummand data .plane)
    (good_zero : VanishesOnGood degree data.chi .line (operator coordinate).val) :
    realizedGoodLineRestriction data operator coordinate = 0 :=
  rationalGoodLine_restriction_zero data.chi (operator coordinate).val good_zero

theorem realizedGoodLineRestriction_classOf {degree : ℕ} (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (coordinate : boundarySummand data .plane)
    (target_cycle : MaximalCycles degree data.chi .line)
    (represents : (operator coordinate).val = classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
      target_cycle) :
    realizedGoodLineRestriction data operator coordinate =
      classOf (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi)
        (evaluateFlagCycle data.chi .line (QuotientGroup.mk rationalGoodLine) target_cycle) := by
  change flagRestriction data.chi .line (QuotientGroup.mk rationalGoodLine)
    (operator coordinate).val = _
  rw [represents, flagRestriction_classOf]

theorem realizedGoodLineRestriction_zero_iff {degree : ℕ} (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (coordinate : boundarySummand data .plane)
    (source : SourceCochain degree)
    (target_cycle : MaximalCycles degree data.chi .line)
    (evaluates : Evaluates data .line source target_cycle)
    (represents : (operator coordinate).val = classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
      target_cycle) :
    realizedGoodLineRestriction data operator coordinate = 0 ↔
      ∃ primitive : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) 1,
        ∀ vertices : Fin 3 → RationalGL3,
          source (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
            (rationalGroup rationalGoodLine) =
          (differentialOne
            (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
            (rationalCoefficientComponent degree data.chi) primitive).val vertices := by
  rw [realizedGoodLineRestriction_classOf data operator coordinate target_cycle represents,
    classOf_eq_zero_iff]
  constructor
  · rintro ⟨primitive, equality⟩
    refine ⟨primitive, ?_⟩
    intro vertices
    have pointwise := congrArg
      (fun cochain : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) 2 => cochain.val vertices) equality
    change (differentialOne
      (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree data.chi) primitive).val vertices =
      target_cycle.val.val vertices (QuotientGroup.mk rationalGoodLine) at pointwise
    rw [evaluates vertices rationalGoodLine, rationalGoodLine_inverse] at pointwise
    exact pointwise.symm
  · rintro ⟨primitive, equality⟩
    refine ⟨primitive, ?_⟩
    apply Subtype.ext
    funext vertices
    change (differentialOne
      (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree data.chi) primitive).val vertices =
      target_cycle.val.val vertices (QuotientGroup.mk rationalGoodLine)
    rw [evaluates vertices rationalGoodLine, rationalGoodLine_inverse]
    exact (equality vertices).symm

theorem realizesStandard_goodLine_primitive {degree : ℕ}
    (data : InducingData degree)
    (operator : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (realizes : RealizesStandard data operator)
    (coordinate : boundarySummand data .plane)
    (supported : BadPlaneRepresentative data coordinate)
    (good_zero : VanishesOnGood degree data.chi .line (operator coordinate).val) :
    ∃ (source : SourceCochain degree)
      (source_cycle : MaximalCycles degree data.chi .plane)
      (flat standard : ℂ → SourceCochain degree)
      (target_cycle : MaximalCycles degree data.chi .line)
      (primitive : cochains
        (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree data.chi) 1),
      IsSourceCocycle data .plane source ∧
      Evaluates data .plane source source_cycle ∧
      classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        source_cycle = coordinate.val ∧
      BadPlaneSource source ∧
      (∀ vertices monomial, IsFlatSection data
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)) ∧
      flat cohomologicalPoint = source ∧
      (∀ vertices monomial, IsStandardContinuation
        (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
        (fun parameter argument => (standard parameter vertices argument).val.coeff monomial)) ∧
      (∀ vertices argument monomial, AnalyticAt ℂ
        (fun parameter => (standard parameter vertices argument).val.coeff monomial) cohomologicalPoint) ∧
      IsSourceCocycle data .line (standard cohomologicalPoint) ∧
      Evaluates data .line (standard cohomologicalPoint) target_cycle ∧
      (operator coordinate).val = classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
        target_cycle ∧
      ∀ vertices : Fin 3 → RationalGL3,
        standard cohomologicalPoint
          (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
          (rationalGroup rationalGoodLine) =
        (differentialOne
          (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
          (rationalCoefficientComponent degree data.chi) primitive).val vertices := by
  rcases supported with ⟨source, source_cycle, is_cycle, evaluates, represents, support⟩
  have membership : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
      source_cycle ∈ boundarySummand data .plane := by
    rw [represents]
    exact coordinate.property
  rcases realizes source is_cycle source_cycle evaluates membership with
    ⟨flat, standard, flat_sections, endpoint, continuations, analytic,
      standard_cycle, target_cycle, target_evaluates, target_represents⟩
  have same_coordinate :
      (⟨classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        source_cycle, membership⟩ : boundarySummand data .plane) = coordinate :=
    Subtype.ext represents
  rw [same_coordinate] at target_represents
  have hzero := realizedGoodLineRestriction_zero data operator coordinate good_zero
  have hiff := realizedGoodLineRestriction_zero_iff data operator coordinate
    (standard cohomologicalPoint) target_cycle target_evaluates target_represents
  exact (hiff.mp hzero).elim fun primitive coboundary =>
    ⟨source, source_cycle, flat, standard, target_cycle, primitive,
      is_cycle, evaluates, represents, support, flat_sections, endpoint, continuations,
      analytic, standard_cycle, target_evaluates, target_represents, coboundary⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
