module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalAutomorphy
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LineFactorization

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

namespace TernaryPeriodPolynomials.EisensteinGraph.SourceComparison

theorem line_induced_binary_rational
    {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (rationalMatrix : BinaryRationalGL) (argument : AdelicGL) :
    sectionValue (lineLevi 1 (GeneralLinearGroup.map rationalAdele rationalMatrix) * argument) =
      sectionValue argument := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 argument
  have rational_value := congrFun realized (GeneralLinearGroup.map rationalAdele rationalMatrix)
  have identity_value := congrFun realized (1 : BinaryAdelicGL)
  have rational_invariance := data.cusp.leftRational rationalMatrix vector 1
  rw [mul_one] at rational_invariance
  rw [rational_invariance, GeneralLinearGroup.map_det, normPower_rational,
    one_mul] at rational_value
  have levi_one : lineLevi 1 (1 : BinaryAdelicGL) = 1 := (lineLeviHom Adeles).map_one
  rw [map_one, normPower_one, one_mul, levi_one, one_mul] at identity_value
  exact rational_value.symm.trans identity_value

theorem line_induced_rankOne_rational
    {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (rationalScalar : ℚˣ) (argument : AdelicGL) :
    sectionValue (lineLevi (Units.map rationalAdele rationalScalar) 1 * argument) =
      sectionValue argument := by
  rw [induced.2.2.2.2.1, data.chi.rational, normPower_rational, one_mul, one_mul]

theorem line_induced_parabolic_rational
    {degree : ℕ} {data : InducingData degree} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data .line parameter sectionValue)
    (rationalMatrix : RationalGL3) (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic .line)
    (argument : AdelicGL) :
    sectionValue (rationalGroup rationalMatrix * argument) = sectionValue argument := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    lineParabolic_factorization rationalMatrix parabolic
  rw [factorization, map_mul, mul_assoc]
  change sectionValue (GeneralLinearGroup.map rationalAdele (lineLevi scalar binary) *
    (GeneralLinearGroup.map rationalAdele (lineUnipotent first second) * argument)) = _
  rw [map_lineLevi, map_lineUnipotent, lineLevi_split, mul_assoc,
    line_induced_rankOne_rational induced, line_induced_binary_rational induced,
    induced.2.2.2.1]

theorem induced_parabolic_invariant
    {degree : ℕ} {data : InducingData degree} {side : Side} {parameter : ℂ}
    {sectionValue : AdelicGL → ℂ} (induced : IsInduced data side parameter sectionValue)
    (rationalMatrix : RationalGL3) (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic side)
    (argument : AdelicGL) :
    sectionValue (rationalGroup rationalMatrix * argument) = sectionValue argument := by
  cases side with
  | plane => exact induced_parabolic_rational induced rationalMatrix parabolic argument
  | line => exact line_induced_parabolic_rational induced rationalMatrix parabolic argument

theorem source_parabolic_invariant {degree : ℕ} (data : InducingData degree)
    (side : Side) (source : SourceCochain degree) (closed : IsSourceCocycle data side source)
    (rationalMatrix : RationalGL3) (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic side)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    source vertices (rationalGroup rationalMatrix * argument) = source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact induced_parabolic_invariant (closed.1 vertices monomial) rationalMatrix parabolic argument

end TernaryPeriodPolynomials.EisensteinGraph.SourceComparison
