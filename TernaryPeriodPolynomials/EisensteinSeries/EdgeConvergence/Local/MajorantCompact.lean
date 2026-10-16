module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.MajorantBound
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.NormContinuity

@[expose] public section


/-!
# Majorants of the local standard integrand, uniform on compact sets of integral arguments

For parameters with `Re s > -n/2 - 1` the local standard integrand is dominated, uniformly for the
arguments in a compact set whose finite parts are integral, by a constant times the negative power
`localHeight ^ (-(n/2 + 3 + Re s))`, which is integrable because the exponent exceeds `2`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The arguments whose finite part is integral. -/
def integralArguments : Set AdelicGL :=
  {argument | ∃ integral : GeneralLinearGroup (Fin 3) IntegralAdeles,
    finiteGroup argument = GeneralLinearGroup.map integralEmbedding integral}

/-- The size of the real inverse of an argument, continuous in the argument. -/
theorem inverseSquares_continuous :
    Continuous (fun argument : AdelicGL =>
      ∑ index, ∑ column, ((realGroup argument).inv column index) ^ 2) := by
  have inverse : Continuous (fun argument : AdelicGL =>
      (((realGroup argument)⁻¹ : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ)) :=
    Units.continuous_coe_inv.comp InducedContinuity.realGroup_continuous
  have entry (column index : Fin 3) :
      Continuous (fun argument : AdelicGL => (realGroup argument).inv column index) :=
    (continuous_apply index).comp ((continuous_apply column).comp inverse)
  exact continuous_finsetSum _ fun index _ =>
    continuous_finsetSum _ fun column _ => (entry column index).pow 2

/-- A local majorant for the compact sets of arguments with integral finite parts. -/
theorem exists_localMajorant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (arguments : Set AdelicGL)
    (compact : IsCompact arguments) (integral : arguments ⊆ integralArguments) :
    Nonempty (LocalMajorant data parameter function induced arguments) := by
  obtain ⟨bound, bounded⟩ := CuspLift.bounded data .plane parameter function induced
  obtain ⟨discriminant, discriminantBound⟩ :=
    compact.exists_bound_of_continuousOn inverseSquares_continuous.continuousOn
  obtain ⟨determinantBound, determinantControl⟩ := compact.exists_bound_of_continuousOn
    (AdelicNormContinuity.determinant_weight_continuous (size := 3)
      (binaryInductionExponent degree .plane parameter).re).continuousOn
  have exponent : -((degree : ℝ) + 6) / 2 - parameter.re =
      -((degree : ℝ) / 2 + 3 + parameter.re) := by ring
  refine ⟨{
    constant := determinantBound * ((3 * Real.sqrt (discriminant + 1)) ^
      (-(-((degree : ℝ) + 6) / 2 - parameter.re))) * max bound 0
    bound := fun coordinates => localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + parameter.re))
    integrable := localHeight_rpow_integrable _ (by linarith)
    dominates := ?_ }⟩
  intro argument membership coordinates
  obtain ⟨integralArgument, finite⟩ := integral membership
  have estimate := localIntegrand_norm_le_of_bounds data parameter function induced halfPlane
    argument integralArgument finite bound bounded discriminant
    ((Real.le_norm_self _).trans (discriminantBound argument membership))
    determinantBound
    ((Real.le_norm_self _).trans (determinantControl argument membership))
    coordinates
  have power : localHeight coordinates ^ (-((degree : ℝ) + 6) / 2 - parameter.re) =
      localHeight coordinates ^ (-((degree : ℝ) / 2 + 3 + parameter.re)) := by
    rw [exponent]
  rw [power] at estimate
  exact estimate

end TernaryPeriodPolynomials.EdgeConvergence
