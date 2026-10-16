module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.StrictPivotPartition
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Basic.Real.Embedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPlanePivotCoordinates {prime : ℕ} [Fact prime.Prime] (first second : ℚ_[prime]) :
    LocalPlanePivotCoordinates (PadicInt.subring prime) first second :=
  valuedPlanePivotCoordinates NormedField.valuation first second

theorem padicPlanePivotCoordinates_integral {prime : ℕ} [Fact prime.Prime]
    (first second : ℚ_[prime]) (first_integral : ‖first‖ ≤ 1) (second_integral : ‖second‖ ≤ 1) :
    (padicPlanePivotCoordinates first second).block = 1 := by
  change (valuedPlanePivotCoordinates NormedField.valuation first second).block = 1
  rw [valuedPlanePivotCoordinates_integral NormedField.valuation first second first_integral second_integral]
  rfl

theorem padicPlanePivotCoordinates_first {prime : ℕ} [Fact prime.Prime]
    (first second : ℚ_[prime]) (large : 1 < ‖first‖) (dominant : ‖second‖ ≤ ‖first‖) :
    (padicPlanePivotCoordinates first second).block =
      planeFirstPivotBinary (Units.mk0 first (norm_pos_iff.mp (lt_trans zero_lt_one large))) second := by
  change (valuedPlanePivotCoordinates NormedField.valuation first second).block = _
  rw [valuedPlanePivotCoordinates_first NormedField.valuation first second large dominant]
  rfl

theorem padicPlanePivotCoordinates_second {prime : ℕ} [Fact prime.Prime]
    (first second : ℚ_[prime]) (large : 1 < ‖second‖) (dominant : ‖first‖ < ‖second‖) :
    (padicPlanePivotCoordinates first second).block =
      planeSecondPivotBinary (Units.mk0 second (norm_pos_iff.mp (lt_trans zero_lt_one large))) first := by
  change (valuedPlanePivotCoordinates NormedField.valuation first second).block = _
  rw [valuedPlanePivotCoordinates_second NormedField.valuation first second large dominant]
  rfl

theorem padicPlanePivotCoordinates_det_norm {prime : ℕ} [Fact prime.Prime] (first second : ℚ_[prime]) :
    ‖(GeneralLinearGroup.det (padicPlanePivotCoordinates first second).block).val‖ =
      (max 1 (max ‖first‖ ‖second‖))⁻¹ := by
  have equality := valuedPlanePivotCoordinates_det NormedField.valuation first second
  exact congrArg (fun value : NNReal => (value : ℝ)) equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
