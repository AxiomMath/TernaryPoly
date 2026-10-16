module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Continuation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.Line

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem normPower_ne_zero (unit : Adelesˣ) (exponent : ℂ) :
    normPower unit exponent ≠ 0 :=
  Complex.exp_ne_zero _

theorem flatSection_eq_on_compactLevi {degree : ℕ}
    (data : InducingData degree) (first second : ℂ → AdelicGL → ℂ)
    (first_flat : IsFlatSection data first)
    (second_flat : IsFlatSection data second)
    (same_endpoint : first cohomologicalPoint = second cohomologicalPoint)
    (parameter : ℂ) (block : BinaryAdelicGL) (compact : AdelicGL)
    (is_compact : inMaximalCompact compact) :
    first parameter (planeLevi block 1 * compact) =
      second parameter (planeLevi block 1 * compact) := by
  apply mul_left_cancel₀
    (normPower_ne_zero (Matrix.GeneralLinearGroup.det block)
      (-binaryInductionExponent degree .plane parameter))
  rw [first_flat.2.2 parameter block compact is_compact,
    second_flat.2.2 parameter block compact is_compact, same_endpoint]

theorem flatSection_eq_on_parabolicCompact {degree : ℕ}
    (data : InducingData degree) (first second : ℂ → AdelicGL → ℂ)
    (first_flat : IsFlatSection data first)
    (second_flat : IsFlatSection data second)
    (same_endpoint : first cohomologicalPoint = second cohomologicalPoint)
    (parameter : ℂ) (block : BinaryAdelicGL) (unit : Adelesˣ)
    (first_radical second_radical : Adeles) (compact : AdelicGL)
    (is_compact : inMaximalCompact compact) :
    first parameter (planeUnipotent first_radical second_radical *
        (planeLevi 1 unit * (planeLevi block 1 * compact))) =
      second parameter (planeUnipotent first_radical second_radical *
        (planeLevi 1 unit * (planeLevi block 1 * compact))) := by
  have first_induced := first_flat.1 parameter
  have second_induced := second_flat.1 parameter
  rw [first_induced.2.2.2.1, second_induced.2.2.2.1,
    first_induced.2.2.2.2.1, second_induced.2.2.2.2.1]
  rw [flatSection_eq_on_compactLevi data first second first_flat second_flat
    same_endpoint parameter block compact is_compact]

theorem polynomialStandardContinuation_eq_at {degree : ℕ}
    (flat first second : ℂ → SourceCochain degree)
    (first_continuation : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (first parameter vertices argument).val.coeff monomial))
    (second_continuation : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (second parameter vertices argument).val.coeff monomial))
    (first_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (first parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (second_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (second parameter vertices argument).val.coeff monomial) cohomologicalPoint) :
    first cohomologicalPoint = second cohomologicalPoint := by
  funext vertices argument
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact standardContinuation_eq_at
    (first_continuation vertices monomial)
    (second_continuation vertices monomial) argument
    (first_analytic vertices argument monomial)
    (second_analytic vertices argument monomial)

theorem evaluates_unique {degree : ℕ}
    (data : InducingData degree) (side : Side) (source : SourceCochain degree)
    (first second : MaximalCycles degree data.chi side)
    (first_evaluates : Evaluates data side source first)
    (second_evaluates : Evaluates data side source second) : first = second := by
  apply Subtype.ext
  apply Subtype.ext
  funext vertices flag
  induction flag using Quotient.inductionOn with
  | h representative =>
    rw [first_evaluates vertices representative, second_evaluates vertices representative]

theorem evaluatedStandardContinuation_eq {degree : ℕ}
    (data : InducingData degree)
    (flat first second : ℂ → SourceCochain degree)
    (first_continuation : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (first parameter vertices argument).val.coeff monomial))
    (second_continuation : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (second parameter vertices argument).val.coeff monomial))
    (first_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (first parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (second_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (second parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (first_cycle second_cycle : MaximalCycles degree data.chi .line)
    (first_evaluates : Evaluates data .line (first cohomologicalPoint) first_cycle)
    (second_evaluates : Evaluates data .line (second cohomologicalPoint) second_cycle) :
    first_cycle = second_cycle := by
  have same_endpoint := polynomialStandardContinuation_eq_at flat first second
    first_continuation second_continuation first_analytic second_analytic
  rw [← same_endpoint] at second_evaluates
  exact evaluates_unique data .line (first cohomologicalPoint) first_cycle second_cycle
    first_evaluates second_evaluates

end TernaryPeriodPolynomials.SphericalDetection.Helpers
