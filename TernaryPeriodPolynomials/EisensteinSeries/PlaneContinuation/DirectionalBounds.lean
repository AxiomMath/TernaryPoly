module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.RapidCuspDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalBounds

theorem directional_expansion (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) :
    directionalOperator data direction vector =
      ∑ index : Fin 2 × Fin 2, (((Matrix.stdBasis ℝ (Fin 2) (Fin 2)).repr direction) index : ℂ) •
        directionalOperator data (Matrix.stdBasis ℝ (Fin 2) (Fin 2) index) vector := by
  have equality := congrArg (directionalSmooth data vector)
    ((Matrix.stdBasis ℝ (Fin 2) (Fin 2)).sum_repr direction)
  simp only [map_sum, map_smul] at equality
  exact equality.symm

theorem iterates_continuous (data : CuspidalRepresentation) (vector : data.smooth) (order : ℕ) :
    Continuous (fun direction : BinaryMatrix =>
      boundedRealization data ((directionalOperator data direction) ^ order $ vector)) := by
  induction order generalizing vector with
  | zero => simpa only [pow_zero, Module.End.one_apply] using
      (continuous_const : Continuous (fun _ : BinaryMatrix => boundedRealization data vector))
  | succ order inductionHypothesis =>
      have equality : (fun direction : BinaryMatrix =>
          boundedRealization data ((directionalOperator data direction) ^ (order + 1) $ vector)) =
          fun direction => ∑ index : Fin 2 × Fin 2,
            (((Matrix.stdBasis ℝ (Fin 2) (Fin 2)).repr direction) index : ℂ) •
              boundedRealization data ((directionalOperator data direction) ^ order $
                directionalOperator data (Matrix.stdBasis ℝ (Fin 2) (Fin 2) index) vector) := by
        funext direction
        rw [pow_succ, Module.End.mul_apply, directional_expansion]
        simp only [map_sum, map_smul]
      rw [equality]
      apply continuous_finsetSum
      intro index _
      have coordinate := Complex.continuous_ofReal.comp
        (((Matrix.stdBasis ℝ (Fin 2) (Fin 2)).coord index).continuous_of_finiteDimensional)
      exact coordinate.smul (inductionHypothesis
        (directionalOperator data (Matrix.stdBasis ℝ (Fin 2) (Fin 2) index) vector))

theorem cuspSupNorm_iterates_continuous (data : CuspidalRepresentation) (vector : data.smooth)
    (order : ℕ) : Continuous (fun direction : BinaryMatrix =>
      cuspSupNorm ((directionalOperator data direction) ^ order $ vector)) :=
  (iterates_continuous data vector order).norm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalBounds
