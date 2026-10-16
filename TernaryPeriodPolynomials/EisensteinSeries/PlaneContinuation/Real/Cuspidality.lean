module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.ResidueIntegration
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealCuspidality

theorem integral_three_shifts (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) :
    ∫ parameter in Set.Ico (0 : ℝ) 1, (3 : ℝ)⁻¹ •
        (realFunction data vector point realPoint parameter +
          realFunction data vector point realPoint (parameter - 1) +
          realFunction data vector point realPoint (parameter - 2)) = 0 := by
  let basePoint := atFinite (GeneralLinearGroup.map integralEmbedding point) * atInfinity realPoint
  let function := fun value : Adeles => data.realize vector (binaryUnipotent value * basePoint)
  have integrable : Integrable function
      (((volume : Measure ℝ).restrict (Set.Ico 0 1)).prod (finiteMeasure.restrict (Set.range integralEmbedding))) := by
    rw [Measure.prod_restrict]
    exact (data.cuspidal vector basePoint).1
  have inner : (fun parameter : ℝ => ∫ value in Set.range integralEmbedding,
      function (parameter, value) ∂finiteMeasure) =ᵐ[volume.restrict (Set.Ico 0 1)]
      (fun parameter => (3 : ℝ)⁻¹ •
        (realFunction data vector point realPoint parameter +
          realFunction data vector point realPoint (parameter - 1) +
          realFunction data vector point realPoint (parameter - 2))) := by
    filter_upwards [integrable.prod_right_ae] with parameter integrableAt
    have equality := FiniteResidueIntegration.integral_three_residues
      (fun value => function (parameter, value)) integrableAt
      (fun residue => realFunction data vector point realPoint (parameter - residue))
      (fun residue quotient => realize_residue data vector fixed point realPoint parameter residue quotient)
    simpa only [Nat.cast_zero, sub_zero, Nat.cast_one, Nat.cast_ofNat] using equality
  have equality := integral_congr_ae inner
  rw [← integral_prod function integrable, Measure.prod_restrict] at equality
  exact equality.symm.trans (data.cuspidal vector basePoint).2

theorem shifted_intervals {function : ℝ → ℂ} (continuous : Continuous function) :
    (∫ parameter in (0 : ℝ)..1,
      function parameter + function (parameter - 1) + function (parameter - 2)) =
      ∫ parameter in (-2 : ℝ)..1, function parameter := by
  have integrableFirst : IntervalIntegrable function volume 0 1 := continuous.intervalIntegrable _ _
  have integrableSecond : IntervalIntegrable (fun parameter => function (parameter - 1)) volume 0 1 :=
    (continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have integrableThird : IntervalIntegrable (fun parameter => function (parameter - 2)) volume 0 1 :=
    (continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (integrableFirst.add integrableSecond) integrableThird,
    intervalIntegral.integral_add integrableFirst integrableSecond,
    intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_comp_sub_right]
  norm_num only [sub_self, zero_sub]
  calc
    _ = ((∫ parameter in (-2 : ℝ)..-1, function parameter) +
        ∫ parameter in (-1 : ℝ)..0, function parameter) + ∫ parameter in (0 : ℝ)..1, function parameter := by abel
    _ = _ := by
      rw [intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable _ _)
        (continuous.intervalIntegrable _ _),
        intervalIntegral.integral_add_adjacent_intervals (continuous.intervalIntegrable _ _)
          (continuous.intervalIntegrable _ _)]

theorem integral_period_zero (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) (start : ℝ) :
    ∫ parameter in start..start + 3, realFunction data vector point realPoint parameter = 0 := by
  have vanishing := integral_three_shifts data vector fixed point realPoint
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_smul, shifted_intervals (realFunction_continuous data vector point realPoint)] at vanishing
  have integralZero : ∫ parameter in (-2 : ℝ)..1, realFunction data vector point realPoint parameter = 0 :=
    (smul_eq_zero.mp vanishing).resolve_left (by norm_num)
  have equality := (realFunction_periodic data vector fixed point realPoint).intervalIntegral_add_eq start (-2)
  norm_num only [show (-2 : ℝ) + 3 = 1 by norm_num] at equality
  exact equality.trans integralZero

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealCuspidality
