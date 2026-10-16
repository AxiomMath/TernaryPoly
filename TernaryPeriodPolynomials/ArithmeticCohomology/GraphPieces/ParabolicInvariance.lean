module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.FlatExtensions

@[expose] public section


/- Ported from AxiomDeep (Claude Opus 5.5). -/
open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.GraphPieces.ParabolicInvariance

theorem normPower_one (exponent : ℂ) : normPower 1 exponent = 1 := by
  simp [normPower]

theorem normPower_zero (unit : Adelesˣ) : normPower unit 0 = 1 := by
  simp [normPower]

theorem normPower_neg (unit : Adelesˣ) (exponent : ℂ) :
    normPower unit (-exponent) = (normPower unit exponent)⁻¹ := by
  simp [normPower, Complex.exp_neg]

theorem normPower_ne_zero (unit : Adelesˣ) (exponent : ℂ) :
    normPower unit exponent ≠ 0 := by
  exact Complex.exp_ne_zero _

theorem normPower_neg_mul (unit : Adelesˣ) (exponent : ℂ) (value : ℂ) :
    normPower unit (-exponent) * (normPower unit exponent * value) = value := by
  rw [normPower_neg, inv_mul_cancel_left₀ (normPower_ne_zero unit exponent)]

theorem planeLevi_one {Ring : Type} [CommRing Ring] :
    planeLevi (1 : Matrix.GeneralLinearGroup (Fin 2) Ring) 1 = 1 := by
  exact (planeLeviHom Ring).map_one

theorem lineLevi_one {Ring : Type} [CommRing Ring] :
    lineLevi 1 (1 : Matrix.GeneralLinearGroup (Fin 2) Ring) = 1 := by
  exact (lineLeviHom Ring).map_one

theorem cuspFunction_leftRational {degree : ℕ} (data : InducingData degree)
    (function : BinaryAdelicGL → ℂ) (membership : function ∈ cuspFunctions data.cusp)
    (rationalElement : BinaryRationalGL) (argument : BinaryAdelicGL) :
    function (Matrix.GeneralLinearGroup.map rationalAdele rationalElement * argument) =
      function argument := by
  obtain ⟨vector, rfl⟩ := membership
  exact data.cusp.leftRational rationalElement vector argument

theorem induced_binaryRational_covariance {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function)
    (rationalElement : BinaryRationalGL) (argument : AdelicGL) :
    function (binaryLevi side (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) *
      argument) =
      normPower (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map rationalAdele rationalElement))
        (binaryInductionExponent degree side parameter) * function argument := by
  have invariant :
      normPower (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.map rationalAdele rationalElement))
        (-binaryInductionExponent degree side parameter) *
          function (binaryLevi side (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) *
            argument) = function argument := by
    cases side with
    | plane =>
      have equality := cuspFunction_leftRational data _ (induced.2.2.2.2.2 argument)
        rationalElement 1
      simpa only [mul_one, map_one, normPower_one, one_mul, planeLevi_one,
        binaryLevi, binaryInductionExponent] using equality
    | line =>
      have equality := cuspFunction_leftRational data _ (induced.2.2.2.2.2 argument)
        rationalElement 1
      simpa only [mul_one, map_one, normPower_one, one_mul, lineLevi_one,
        binaryLevi, binaryInductionExponent] using equality
  have equality := congrArg (fun value =>
    normPower (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map rationalAdele rationalElement))
      (binaryInductionExponent degree side parameter) * value) invariant
  rw [normPower_neg, mul_inv_cancel_left₀ (normPower_ne_zero _ _)] at equality
  exact equality

theorem induced_binaryRational_norm_one {degree : ℕ} (data : InducingData degree)
    (side : Side) (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function)
    (rationalElement : BinaryRationalGL)
    (norm : adeleNorm (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map rationalAdele rationalElement)) = 1)
    (argument : AdelicGL) :
    function (binaryLevi side (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) *
      argument) = function argument := by
  rw [induced_binaryRational_covariance data side parameter function induced]
  simp [normPower, norm]

theorem planeInduced_rankOneRational {degree : ℕ} (data : InducingData degree)
    (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane cohomologicalPoint function)
    (rationalUnit : ℚˣ) (argument : AdelicGL) :
    function (planeLevi 1 (Units.map rationalAdele rationalUnit) * argument) =
      function argument := by
  rw [induced.2.2.2.2.1]
  have exponent : -2 * inductionExponent .plane cohomologicalPoint = 0 := by
    simp only [inductionExponent, cohomologicalPoint]
    ring
  rw [data.chi.rational, exponent, normPower_zero, one_mul, one_mul]

theorem planeInduced_binaryRational_det_one {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .plane parameter function)
    (rationalElement : BinaryRationalGL)
    (determinant : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) = 1)
    (argument : AdelicGL) :
    function (planeLevi (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) 1 *
      argument) = function argument := by
  have invariant := cuspFunction_leftRational data _ (induced.2.2.2.2.2 argument)
    rationalElement 1
  simpa only [mul_one, determinant, normPower_one, one_mul, map_one, planeLevi_one]
    using invariant

theorem lineInduced_binaryRational_det_one {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data .line parameter function)
    (rationalElement : BinaryRationalGL)
    (determinant : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) = 1)
    (argument : AdelicGL) :
    function (lineLevi 1 (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) *
      argument) = function argument := by
  have invariant := cuspFunction_leftRational data _ (induced.2.2.2.2.2 argument)
    rationalElement 1
  simpa only [mul_one, determinant, normPower_one, one_mul, map_one, lineLevi_one]
    using invariant

theorem source_planeRadicalInvariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source)
    (vertices : Fin 3 → RealGL3) (first second : Adeles) (argument : AdelicGL) :
    source vertices (planeUnipotent first second * argument) = source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 vertices monomial).2.2.2.1 first second argument

theorem source_lineRadicalInvariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source)
    (vertices : Fin 3 → RealGL3) (first second : Adeles) (argument : AdelicGL) :
    source vertices (lineUnipotent first second * argument) = source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 vertices monomial).2.2.2.1 first second argument

theorem source_binaryRational_det_one {degree : ℕ} (data : InducingData degree)
    (side : Side) (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source)
    (rationalElement : BinaryRationalGL)
    (determinant : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) = 1)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    source vertices
      (binaryLevi side (Matrix.GeneralLinearGroup.map rationalAdele rationalElement) * argument) =
      source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  cases side with
  | plane =>
    exact planeInduced_binaryRational_det_one data cohomologicalPoint _
      (isSource.1 vertices monomial) rationalElement determinant argument
  | line =>
    exact lineInduced_binaryRational_det_one data cohomologicalPoint _
      (isSource.1 vertices monomial) rationalElement determinant argument

end TernaryPeriodPolynomials.GraphPieces.ParabolicInvariance
