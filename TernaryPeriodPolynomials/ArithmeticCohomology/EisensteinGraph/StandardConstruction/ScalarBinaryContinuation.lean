module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ScalarBinaryIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ContinuationUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.RankOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Invariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.Decomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryContinuation

def normalizedCuspContinuation (degree : ℕ) (continuation : ℂ → AdelicGL → ℂ)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (parameter : ℂ) : ℂ :=
  normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter) *
    continuation parameter (lineLevi 1 binary * argument)

theorem normalization_analytic (degree : ℕ) (binary : BinaryAdelicGL) (point : ℂ) :
    AnalyticAt ℂ (fun parameter => normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter)) point := by
  unfold normPower binaryInductionExponent inductionExponent
  exact (((analyticAt_const.add analyticAt_const).div_const.sub
    (analyticAt_const.sub analyticAt_id.div_const)).neg.mul analyticAt_const).cexp

theorem normalized_meromorphic {degree : ℕ} (extension continuation : ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension continuation)
    (binary : BinaryAdelicGL) (argument : AdelicGL) (parameter : ℂ) :
    MeromorphicAt (normalizedCuspContinuation degree continuation binary argument) parameter :=
  (normalization_analytic degree binary parameter).meromorphicAt.mul
    (continues.1 (lineLevi 1 binary * argument) parameter)

theorem normalized_halfPlane {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      ∀ binary : BinaryAdelicGL, ∀ argument : AdelicGL,
        normalizedCuspContinuation degree continuation binary argument parameter =
          ∫ coordinates, ScalarBinaryIntegral.cuspIntegrand data parameter
            (extension parameter) (flat.1 parameter) binary argument coordinates
              ∂radicalMeasure := by
  obtain ⟨threshold, integralEquality⟩ := continues.2
  refine ⟨threshold, ?_⟩
  intro parameter large binary argument
  change normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter) *
        continuation parameter (lineLevi 1 binary * argument) = _
  rw [(integralEquality parameter large (lineLevi 1 binary * argument)).2]
  change normPower (GeneralLinearGroup.det binary)
      (-binaryInductionExponent degree .line parameter) *
        (∫ coordinates, standardIntegrand (fun _ => extension parameter) parameter
          (lineLevi 1 binary * argument) coordinates ∂radicalMeasure) = _
  rw [ScalarBinaryIntegral.integral_lineLevi_normalized data parameter
    (extension parameter) (flat.1 parameter) binary argument]
  exact ParabolicInvariance.normPower_neg_mul _ _ _

theorem normalized_halfPlane_integrable {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation) :
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      ∀ binary : BinaryAdelicGL, ∀ argument : AdelicGL,
        Integrable (ScalarBinaryIntegral.cuspIntegrand data parameter
          (extension parameter) (flat.1 parameter) binary argument) radicalMeasure ∧
        normalizedCuspContinuation degree continuation binary argument parameter =
          ∫ coordinates, ScalarBinaryIntegral.cuspIntegrand data parameter
            (extension parameter) (flat.1 parameter) binary argument coordinates
              ∂radicalMeasure := by
  obtain ⟨threshold, standardIntegrals⟩ := continues.2
  obtain ⟨otherThreshold, cuspIntegrals⟩ :=
    normalized_halfPlane data extension continuation flat continues
  refine ⟨max threshold otherThreshold, ?_⟩
  intro parameter large binary argument
  constructor
  · exact ScalarBinaryIntegral.cuspIntegrand_integrable_of_standard data parameter
      (extension parameter) (flat.1 parameter) binary argument
      ((standardIntegrals parameter (lt_of_le_of_lt (le_max_left _ _) large)
        (lineLevi 1 binary * argument)).1)
  · exact cuspIntegrals parameter (lt_of_le_of_lt (le_max_right _ _) large)
      binary argument

theorem normalized_regular {degree : ℕ} (continuation : ℂ → AdelicGL → ℂ)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    AnalyticAt ℂ (normalizedCuspContinuation degree continuation binary argument)
      cohomologicalPoint :=
  (normalization_analytic degree binary cohomologicalPoint).mul
    (regular (lineLevi 1 binary * argument))

theorem cuspIntegrand_leftRational {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL)
    (argument : AdelicGL) (coordinates : Adeles × Adeles) :
    ScalarBinaryIntegral.cuspIntegrand data parameter function induced
        (GeneralLinearGroup.map rationalAdele rational * binary) argument coordinates =
      ScalarBinaryIntegral.cuspIntegrand data parameter function induced binary argument
        coordinates :=
  data.cusp.leftRational rational
    (CuspLift.vector data .plane parameter function induced
      (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument)) binary

theorem normalized_leftRational {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (rational : BinaryRationalGL) (binary : BinaryAdelicGL) (argument : AdelicGL) :
    normalizedCuspContinuation degree continuation
        (GeneralLinearGroup.map rationalAdele rational * binary) argument cohomologicalPoint =
      normalizedCuspContinuation degree continuation binary argument cohomologicalPoint := by
  obtain ⟨threshold, integrals⟩ := normalized_halfPlane data extension continuation flat continues
  apply ContinuationUniqueness.meromorphic_halfPlane_unique
    (normalizedCuspContinuation degree continuation
      (GeneralLinearGroup.map rationalAdele rational * binary) argument)
    (normalizedCuspContinuation degree continuation binary argument)
    (fun parameter => normalized_meromorphic extension continuation continues _ _ parameter)
    (fun parameter => normalized_meromorphic extension continuation continues _ _ parameter)
    threshold _ cohomologicalPoint
    (normalized_regular continuation regular _ argument)
    (normalized_regular continuation regular binary argument)
  intro parameter large
  rw [integrals parameter large (GeneralLinearGroup.map rationalAdele rational * binary) argument,
    integrals parameter large binary argument]
  apply integral_congr_ae
  filter_upwards [] with coordinates
  exact cuspIntegrand_leftRational data parameter (extension parameter)
    (flat.1 parameter) rational binary argument coordinates

theorem continued_binaryRational {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (rational : BinaryRationalGL) (argument : AdelicGL) :
    continuation cohomologicalPoint
        (lineLevi 1 (GeneralLinearGroup.map rationalAdele rational) * argument) =
      continuation cohomologicalPoint argument := by
  have invariant := normalized_leftRational data extension continuation flat continues regular
    rational 1 argument
  have rationalNorm : adeleNorm (GeneralLinearGroup.det
      (GeneralLinearGroup.map rationalAdele rational)) = 1 := by
    rw [GeneralLinearGroup.map_det]
    exact RationalNorm.rational_norm _
  have factor : normPower (GeneralLinearGroup.det
      (GeneralLinearGroup.map rationalAdele rational))
      (-binaryInductionExponent degree .line cohomologicalPoint) = 1 := by
    simp [normPower, rationalNorm]
  simpa only [normalizedCuspContinuation, mul_one, one_mul, map_one,
    ParabolicInvariance.normPower_one, ParabolicInvariance.lineLevi_one, factor] using invariant

theorem continued_rankOneRational {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (rational : ℚˣ) (argument : AdelicGL) :
    continuation cohomologicalPoint
        (lineLevi (Units.map rationalAdele rational) 1 * argument) =
      continuation cohomologicalPoint argument := by
  have covariance := StandardRankOne.continuation_rankOne data extension continuation flat
    continues cohomologicalPoint regular (Units.map rationalAdele rational) argument
  have norm := RationalNorm.rational_norm rational
  simpa [data.chi.rational, normPower, norm] using covariance

theorem continued_lineRational {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (regular : ∀ argument, AnalyticAt ℂ
      (fun parameter => continuation parameter argument) cohomologicalPoint)
    (rational : RationalGL3) (membership : rational ∈ lineParabolic ℚ)
    (argument : AdelicGL) :
    continuation cohomologicalPoint (rationalGroup rational * argument) =
      continuation cohomologicalPoint argument := by
  have decomposition : rationalGroup rational =
      lineLevi (Units.map rationalAdele (LineDecomposition.rankOneBlock rational membership))
        (GeneralLinearGroup.map rationalAdele
          (LineDecomposition.binaryLeviBlock rational membership)) *
      lineUnipotent (rationalAdele (rational.val 0 1 / rational.val 0 0))
        (rationalAdele (rational.val 0 2 / rational.val 0 0)) := by
    conv_lhs => rw [LineDecomposition.line_decomposition rational membership]
    rw [map_mul]
    exact congrArg₂ (fun first second : AdelicGL => first * second)
      (LineDecomposition.map_lineLevi rationalAdele _ _)
      (LineDecomposition.map_lineUnipotent rationalAdele _ _)
  have split : lineLevi
      (Units.map rationalAdele (LineDecomposition.rankOneBlock rational membership))
      (GeneralLinearGroup.map rationalAdele
        (LineDecomposition.binaryLeviBlock rational membership)) =
      lineLevi 1 (GeneralLinearGroup.map rationalAdele
        (LineDecomposition.binaryLeviBlock rational membership)) *
      lineLevi (Units.map rationalAdele (LineDecomposition.rankOneBlock rational membership)) 1 := by
    simpa only [Prod.mk_mul_mk, mul_one, one_mul, lineLeviHom,
      MonoidHom.coe_mk, OneHom.coe_mk] using
      (lineLeviHom Adeles).map_mul
        (1, GeneralLinearGroup.map rationalAdele
          (LineDecomposition.binaryLeviBlock rational membership))
        (Units.map rationalAdele (LineDecomposition.rankOneBlock rational membership), 1)
  rw [decomposition, split, mul_assoc, mul_assoc]
  exact (continued_binaryRational data extension continuation flat continues regular
    (LineDecomposition.binaryLeviBlock rational membership) _).trans
      ((continued_rankOneRational data extension continuation flat continues regular
        (LineDecomposition.rankOneBlock rational membership) _).trans
        (StandardInvariance.continuation_lineRadical extension continuation continues
          cohomologicalPoint regular _ _ argument))

theorem polynomialContinuation_lineRational {degree : ℕ} (data : InducingData degree)
    (extension continuation :
      ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (flat : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial))
    (continues : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (extension parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (continuation parameter vertices argument).val.coeff monomial))
    (regular : ∀ vertices argument monomial, AnalyticAt ℂ (fun parameter =>
      (continuation parameter vertices argument).val.coeff monomial)
        cohomologicalPoint)
    (vertices : Fin 3 → RealGL3) (rational : RationalGL3)
    (membership : rational ∈ lineParabolic ℚ) (argument : AdelicGL) :
    continuation cohomologicalPoint vertices (rationalGroup rational * argument) =
      continuation cohomologicalPoint vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact continued_lineRational data _ _ (flat vertices monomial)
    (continues vertices monomial) (fun argument => regular vertices argument monomial)
    rational membership argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.ScalarBinaryContinuation
