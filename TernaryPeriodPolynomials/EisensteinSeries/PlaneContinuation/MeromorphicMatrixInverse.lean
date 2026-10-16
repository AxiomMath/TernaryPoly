module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeromorphicFiniteEvaluation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Group.Subgroup.Finsupp

@[expose] public section


open Matrix
open scoped Classical

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicMatrixInverse

theorem determinant {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (matrix : ℂ → Matrix Indices Indices ℂ) (parameter : ℂ)
    (meromorphic : ∀ row column, MeromorphicAt (fun parameter => matrix parameter row column) parameter) :
    MeromorphicAt (fun parameter => (matrix parameter).det) parameter := by
  simp only [Matrix.det_apply']
  apply MeromorphicAt.fun_sum
  intro permutation _
  apply analyticAt_const.meromorphicAt.mul
  exact MeromorphicAt.fun_prod (fun column _ => meromorphic (permutation column) column)

theorem adjugate {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (matrix : ℂ → Matrix Indices Indices ℂ) (parameter : ℂ)
    (meromorphic : ∀ row column, MeromorphicAt (fun parameter => matrix parameter row column) parameter)
    (row column : Indices) :
    MeromorphicAt (fun parameter => (matrix parameter).adjugate row column) parameter := by
  simp only [Matrix.adjugate_apply]
  apply determinant
  intro first second
  by_cases equality : first = column
  · subst first
    simp only [Matrix.updateRow_self]
    exact analyticAt_const.meromorphicAt
  · simpa only [Matrix.updateRow_ne equality] using meromorphic first second

theorem inverse {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (matrix : ℂ → Matrix Indices Indices ℂ) (parameter : ℂ)
    (meromorphic : ∀ row column, MeromorphicAt (fun parameter => matrix parameter row column) parameter)
    (row column : Indices) :
    MeromorphicAt (fun parameter => (matrix parameter)⁻¹ row column) parameter := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (determinant matrix parameter meromorphic).fun_inv.mul (adjugate matrix parameter meromorphic row column)

theorem inverse_mul {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (matrix : Matrix Indices Indices ℂ) (nonzero : matrix.det ≠ 0) : matrix⁻¹ * matrix = 1 :=
  matrix.nonsing_inv_mul (isUnit_iff_ne_zero.mpr nonzero)

theorem mul_inverse {Indices : Type*} [Fintype Indices] [DecidableEq Indices]
    (matrix : Matrix Indices Indices ℂ) (nonzero : matrix.det ≠ 0) : matrix * matrix⁻¹ = 1 :=
  matrix.mul_nonsing_inv (isUnit_iff_ne_zero.mpr nonzero)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeromorphicMatrixInverse
