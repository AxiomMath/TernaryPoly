module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.FinitePlaneValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finiteLevelIntegralLift (compact : finiteLevel) : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  Classical.choose compact.property

theorem finiteLevelIntegralLift_spec (compact : finiteLevel) :
    GeneralLinearGroup.map integralEmbedding (finiteLevelIntegralLift compact) = compact.val :=
  (Classical.choose_spec compact.property).2

def finitePlaneLevelInductionCoordinates (finite : FiniteGL) (coords : FinitePlaneLevelCoordinates finite) :
    FinitePlaneInductionCoordinates finite where
  first := coords.first
  second := coords.second
  scalar := coords.scalar
  block := coords.block
  compact := finiteLevelIntegralLift coords.compact
  factorization := by
    rw [finiteLevelIntegralLift_spec]
    exact coords.factorization

/-- The actual flat section is evaluated in the supplied cusp constituent at a finite binary argument. -/
theorem polynomialFlatSection_value_plane_level {degree : ℕ} (data : InducingData degree)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain degree)
    (cocycle : IsSourceCocycle data .plane source) (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (real : RealGL3) (finite : FiniteGL)
    (coords : FinitePlaneLevelCoordinates finite) :
    flat parameter vertices (combineGL real finite) =
      (realPlaneFlatWeight parameter real *
        normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (binaryInductionExponent degree .plane parameter) *
        normPower (finiteAdeleUnit coords.scalar) (-2 * inductionExponent .plane parameter)) •
        (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real)).val (atFinite coords.block) := by
  have value : flat parameter vertices (combineGL real finite) =
      (realPlaneFlatWeight parameter real *
        (normPower (finiteAdeleUnit (GeneralLinearGroup.det coords.block)) (inductionExponent .plane parameter) *
          normPower (finiteAdeleUnit coords.scalar) (-2 * inductionExponent .plane parameter))) •
        source vertices (combineGL real finite) := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simpa only [finitePlaneLevelInductionCoordinates, endpoint, Submodule.coe_smul, MvPolynomial.coeff_smul,
      smul_eq_mul] using
      flatSection_value_real_finite_coordinates data _ (sections vertices monomial) parameter real finite
        (finitePlaneLevelInductionCoordinates finite coords)
  rw [value, source_plane_level_coordinates data trivial source cocycle vertices real finite coords, smul_smul]
  apply congrArg (fun scalar : ℂ => scalar •
    (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity real)).val (atFinite coords.block))
  rw [binaryInductionExponent, normPower_add_exponents]
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
