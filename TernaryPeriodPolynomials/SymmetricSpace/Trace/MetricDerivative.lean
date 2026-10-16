module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCoordinates
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section


/-! The trace-free tangent matrices are the literal derivatives of the chart. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpaceCharts
open scoped ContDiff Matrix.Norms.Elementwise

def tangentLinear : Coordinates →ₗ[ℝ] Mat where
  toFun := tangentMatrix
  map_add' := tangentMatrix_add
  map_smul' := tangentMatrix_smul

def tangentCLM : Coordinates →L[ℝ] Mat := tangentLinear.toContinuousLinearMap

@[simp] theorem tangentCLM_apply (v : Coordinates) : tangentCLM v = tangentMatrix v := rfl

theorem reconstruct_eq_tangent (x : Coordinates) :
    reconstruct x = tangentCLM x + reconstruct 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [reconstruct, tangentCLM_apply, tangentMatrix]
  all_goals ring

/-- The derivative map in the exact five-coordinate convention. -/
theorem hasFDerivAt_reconstruct (x : Coordinates) : HasFDerivAt reconstruct tangentCLM x := by
  have h : reconstruct = fun y => tangentCLM y + reconstruct 0 := funext reconstruct_eq_tangent
  rw [h]
  exact tangentCLM.hasFDerivAt.add_const _

@[simp] theorem fderiv_reconstruct (x : Coordinates) : fderiv ℝ reconstruct x = tangentCLM :=
  (hasFDerivAt_reconstruct x).fderiv

end TernaryPoly.SymmetricSpaceTraceMetric
