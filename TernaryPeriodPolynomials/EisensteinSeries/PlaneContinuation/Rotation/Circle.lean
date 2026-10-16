module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArchimedeanAveraging
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

noncomputable def complexMatrix : ℂ →+* BinaryMatrix where
  toFun value := !![value.re, -value.im; value.im, value.re]
  map_zero' := by ext row column; fin_cases row <;> fin_cases column <;> simp
  map_one' := by ext row column; fin_cases row <;> fin_cases column <;> simp
  map_add' first second := by
    ext row column
    fin_cases row <;> fin_cases column <;> simp
    ring
  map_mul' first second := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem complexMatrix_continuous : Continuous complexMatrix := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  fin_cases row <;> fin_cases column
  · exact Complex.continuous_re
  · exact Complex.continuous_im.neg
  · exact Complex.continuous_im
  · exact Complex.continuous_re

noncomputable def circleRotation : Circle →* BinaryRealGL :=
  (Units.map complexMatrix.toMonoidHom).comp Circle.toUnits

theorem circleRotation_val (value : Circle) : (circleRotation value).val = complexMatrix value := rfl

theorem circleRotation_continuous : Continuous circleRotation := by
  apply Units.continuous_iff.mpr
  constructor
  · exact complexMatrix_continuous.comp continuous_subtype_val
  · have equality : (fun value : Circle => (circleRotation value)⁻¹.val) =
        (fun value : Circle => complexMatrix (value⁻¹ : Circle)) := by
      funext value
      rw [← map_inv, circleRotation_val]
    rw [equality]
    exact complexMatrix_continuous.comp (continuous_subtype_val.comp continuous_inv)

abbrev Parameter := AddCircle (1 : ℝ)

noncomputable def rotation (parameter : Parameter) : BinaryRealGL := circleRotation parameter.toCircle

theorem rotation_zero : rotation 0 = 1 := by
  rw [rotation, AddCircle.toCircle_zero, map_one]

theorem rotation_add (first second : Parameter) : rotation (first + second) = rotation first * rotation second := by
  rw [rotation, AddCircle.toCircle_add, map_mul]
  rfl

theorem rotation_neg (parameter : Parameter) : rotation (-parameter) = (rotation parameter)⁻¹ := by
  rw [rotation, AddCircle.toCircle_neg, map_inv]
  rfl

theorem rotation_continuous : Continuous rotation := circleRotation_continuous.comp AddCircle.continuous_toCircle

theorem fourier_add_argument (index : ℤ) (first second : Parameter) :
    fourier index (first + second) = fourier index first * fourier index second := by
  change (((index • (first + second)).toCircle : Circle) : ℂ) =
    (((index • first).toCircle : Circle) : ℂ) * (((index • second).toCircle : Circle) : ℂ)
  rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_mul_neg (index : ℤ) (parameter : Parameter) :
    fourier index parameter * fourier (-index) parameter = 1 := by
  rw [← fourier_add, add_neg_cancel, fourier_zero]

theorem fourier_norm_one (index : ℤ) (parameter : Parameter) : ‖fourier index parameter‖ = 1 :=
  Circle.norm_coe _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle
