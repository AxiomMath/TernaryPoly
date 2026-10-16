module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.Decomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalComparison

def RationalNormFormula : Prop :=
  ∀ rationalUnit : ℚˣ, adeleNorm (Units.map rationalAdele rationalUnit) = 1

theorem induced_parabolicInvariant {degree : ℕ} (data : InducingData degree)
    (normFormula : RationalNormFormula) (side : Side) (function : AdelicGL → ℂ)
    (induced : IsInduced data side cohomologicalPoint function) (element : RationalGL3)
    (membership : element ∈ parabolic side) (argument : AdelicGL) :
    function (rationalGroup element * argument) = function argument := by
  cases side with
  | plane =>
    apply PlaneDecomposition.induced_planeRational_invariant data function induced
      element membership _ argument
    rw [Matrix.GeneralLinearGroup.map_det]
    exact normFormula _
  | line =>
    apply LineDecomposition.induced_lineRational_invariant data function induced
      element membership _ _ argument
    · rw [Matrix.GeneralLinearGroup.map_det]
      exact normFormula _
    · exact normFormula _

theorem source_parabolicInvariant {degree : ℕ} (data : InducingData degree)
    (normFormula : RationalNormFormula) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) (element : RationalGL3)
    (membership : element ∈ parabolic side) (vertices : Fin 3 → RealGL3)
    (argument : AdelicGL) : source vertices (rationalGroup element * argument) =
      source vertices argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact induced_parabolicInvariant data normFormula side _ (isSource.1 vertices monomial)
    element membership argument

theorem source_flagIndependent {degree : ℕ} (data : InducingData degree)
    (normFormula : RationalNormFormula) (side : Side)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data side source) : Comparison.FlagIndependent side source := by
  intro vertices first second related
  have inverseRelated : (first⁻¹ * second)⁻¹ ∈ parabolic side :=
    (parabolic side).inv_mem related
  have invariant := source_parabolicInvariant data normFormula side source isSource
    ((first⁻¹ * second)⁻¹) inverseRelated
    (fun index => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
    (rationalGroup first⁻¹)
  have argumentEquality : rationalGroup ((first⁻¹ * second)⁻¹) * rationalGroup first⁻¹ =
      rationalGroup second⁻¹ := by
    rw [← map_mul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  rw [argumentEquality] at invariant
  exact invariant.symm

theorem sourceComparison_of_rationalNorm {degree : ℕ} (data : InducingData degree)
    (normFormula : RationalNormFormula) : SourceComparisonExists data := by
  apply (Comparison.sourceComparison_iff data).mpr
  intro side source isSource
  exact source_flagIndependent data normFormula side source isSource

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.RationalComparison
