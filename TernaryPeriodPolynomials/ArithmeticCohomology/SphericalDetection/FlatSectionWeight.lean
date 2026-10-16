module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.Uniqueness

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem normPower_add_exponents (unit : Adelesˣ) (first second : ℂ) :
    normPower unit (first + second) = normPower unit first * normPower unit second := by
  simp only [normPower, add_mul, Complex.exp_add]

theorem normPower_zero_exponent (unit : Adelesˣ) : normPower unit 0 = 1 := by
  simp [normPower]

theorem binaryInductionExponent_plane_difference (degree : ℕ) (parameter : ℂ) :
    binaryInductionExponent degree .plane parameter =
      binaryInductionExponent degree .plane cohomologicalPoint + inductionExponent .plane parameter := by
  unfold binaryInductionExponent inductionExponent cohomologicalPoint
  ring

theorem flatSection_value_compactLevi {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (block : BinaryAdelicGL) (compact : AdelicGL) (compact_mem : inMaximalCompact compact) :
    flat parameter (planeLevi block 1 * compact) =
      normPower (GeneralLinearGroup.det block) (inductionExponent .plane parameter) *
        flat cohomologicalPoint (planeLevi block 1 * compact) := by
  apply mul_left_cancel₀ (normPower_ne_zero (GeneralLinearGroup.det block)
    (-binaryInductionExponent degree .plane parameter))
  rw [section_mem.2.2 parameter block compact compact_mem, ← mul_assoc, ← normPower_add_exponents]
  have exponent : -binaryInductionExponent degree .plane parameter + inductionExponent .plane parameter =
      -binaryInductionExponent degree .plane cohomologicalPoint := by
    rw [binaryInductionExponent_plane_difference]
    ring
  rw [exponent]

theorem flatSection_value_inductionCoordinates {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (first second : Adeles) (scalar : Adelesˣ) (block : BinaryAdelicGL)
    (compact : AdelicGL) (compact_mem : inMaximalCompact compact) :
    flat parameter (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))) =
      (normPower (GeneralLinearGroup.det block) (inductionExponent .plane parameter) *
        normPower scalar (-2 * inductionExponent .plane parameter)) *
      flat cohomologicalPoint (planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))) := by
  rw [(section_mem.1 parameter).2.2.2.1, (section_mem.1 cohomologicalPoint).2.2.2.1,
    (section_mem.1 parameter).2.2.2.2.1, (section_mem.1 cohomologicalPoint).2.2.2.2.1,
    flatSection_value_compactLevi data flat section_mem parameter block compact compact_mem]
  have endpoint : inductionExponent .plane cohomologicalPoint = 0 := by
    unfold inductionExponent cohomologicalPoint
    ring
  rw [endpoint, mul_zero, normPower_zero_exponent, mul_one]
  ring

structure PlaneInductionCoordinates (argument : AdelicGL) where
  first : Adeles
  second : Adeles
  scalar : Adelesˣ
  block : BinaryAdelicGL
  compact : AdelicGL
  compact_mem : inMaximalCompact compact
  factorization : argument = planeUnipotent first second * (planeLevi 1 scalar * (planeLevi block 1 * compact))

def planeInductionCoordinates (argument : AdelicGL) : PlaneInductionCoordinates argument :=
  Classical.choice (by
    obtain ⟨first, second, scalar, block, compact, compact_mem, factorization⟩ :=
      adelicGL_exists_induction_coordinates argument
    exact ⟨⟨first, second, scalar, block, compact, compact_mem, factorization⟩⟩)

/-- The scalar deformation factor in the chosen plane Iwasawa coordinates. -/
def planeFlatWeight (parameter : ℂ) (argument : AdelicGL) : ℂ :=
  normPower (GeneralLinearGroup.det (planeInductionCoordinates argument).block) (inductionExponent .plane parameter) *
    normPower (planeInductionCoordinates argument).scalar (-2 * inductionExponent .plane parameter)

theorem planeFlatWeight_ne_zero (parameter : ℂ) (argument : AdelicGL) : planeFlatWeight parameter argument ≠ 0 :=
  mul_ne_zero (normPower_ne_zero _ _) (normPower_ne_zero _ _)

theorem planeFlatWeight_endpoint (argument : AdelicGL) : planeFlatWeight cohomologicalPoint argument = 1 := by
  have endpoint : inductionExponent .plane cohomologicalPoint = 0 := by
    unfold inductionExponent cohomologicalPoint
    ring
  simp only [planeFlatWeight, endpoint, mul_zero, normPower_zero_exponent, mul_one]

theorem planeFlatWeight_analyticAt (argument : AdelicGL) (parameter : ℂ) :
    AnalyticAt ℂ (fun parameter => planeFlatWeight parameter argument) parameter := by
  have exponent : AnalyticAt ℂ (fun parameter => inductionExponent .plane parameter) parameter := by
    unfold inductionExponent
    fun_prop
  unfold planeFlatWeight normPower
  exact ((exponent.mul analyticAt_const).cexp).mul
    (((analyticAt_const.mul exponent).mul analyticAt_const).cexp)

theorem flatSection_value_weight {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → AdelicGL → ℂ) (section_mem : IsFlatSection data flat)
    (parameter : ℂ) (argument : AdelicGL) :
    flat parameter argument = planeFlatWeight parameter argument * flat cohomologicalPoint argument := by
  have value := flatSection_value_inductionCoordinates data flat section_mem parameter
    (planeInductionCoordinates argument).first (planeInductionCoordinates argument).second
    (planeInductionCoordinates argument).scalar (planeInductionCoordinates argument).block
    (planeInductionCoordinates argument).compact (planeInductionCoordinates argument).compact_mem
  rw [← (planeInductionCoordinates argument).factorization] at value
  exact value

theorem polynomialFlatSection_value_weight {degree : ℕ} (data : InducingData degree)
    (flat : ℂ → SourceCochain degree)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (parameter : ℂ) (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    flat parameter vertices argument = planeFlatWeight parameter argument • flat cohomologicalPoint vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
    flatSection_value_weight data _ (sections vertices monomial) parameter argument

end TernaryPeriodPolynomials.SphericalDetection.Helpers
