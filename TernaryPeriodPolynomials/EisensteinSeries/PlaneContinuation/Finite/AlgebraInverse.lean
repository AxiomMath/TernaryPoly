module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MeromorphicMatrixInverse

@[expose] public section


open Matrix
open scoped Classical

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteAlgebraInverse

theorem multiplication_matrix {AlgebraType Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [Fintype Indices] [DecidableEq Indices] (basis : Module.Basis Indices ℂ AlgebraType)
    (domain : Set ℂ) (family : domain → AlgebraType)
    (functionalContinuations : ∀ functional : AlgebraType →ₗ[ℂ] ℂ,
      ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
        ∀ parameter : domain, continuation parameter.val = functional (family parameter)) :
    ∃ matrix : ℂ → Matrix Indices Indices ℂ,
      (∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter) ∧
      ∀ parameter : domain, matrix parameter.val =
        LinearMap.toMatrix basis basis (LinearMap.mulLeft ℂ (family parameter)) := by
  choose entries meromorphic equalities using fun row column : Indices =>
    functionalContinuations ((basis.coord row).comp (LinearMap.mulRight ℂ (basis column)))
  refine ⟨fun parameter row column => entries row column parameter, meromorphic, ?_⟩
  intro parameter
  apply Matrix.ext
  intro row column
  rw [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
  exact equalities row column parameter

def coefficients {AlgebraType Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [Fintype Indices] [DecidableEq Indices] (basis : Module.Basis Indices ℂ AlgebraType)
    (matrix : ℂ → Matrix Indices Indices ℂ) (parameter : ℂ) : Indices → ℂ :=
  (matrix parameter)⁻¹ *ᵥ (fun index => basis.repr 1 index)

theorem coefficients_meromorphic {AlgebraType Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [Fintype Indices] [DecidableEq Indices] (basis : Module.Basis Indices ℂ AlgebraType)
    (matrix : ℂ → Matrix Indices Indices ℂ)
    (meromorphic : ∀ row column parameter, MeromorphicAt (fun parameter => matrix parameter row column) parameter)
    (index : Indices) (parameter : ℂ) :
    MeromorphicAt (fun parameter => coefficients basis matrix parameter index) parameter := by
  apply MeromorphicAt.fun_sum
  intro column _
  exact (MeromorphicMatrixInverse.inverse matrix parameter (fun row column => meromorphic row column parameter) index column).mul
    analyticAt_const.meromorphicAt

theorem inverse_identity {AlgebraType Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [Fintype Indices] [DecidableEq Indices] (basis : Module.Basis Indices ℂ AlgebraType)
    (matrix : ℂ → Matrix Indices Indices ℂ) (parameter : ℂ) (value : AlgebraType) (unit : IsUnit value)
    (equality : matrix parameter = LinearMap.toMatrix basis basis (LinearMap.mulLeft ℂ value)) :
    value * (∑ index, coefficients basis matrix parameter index • basis index) = 1 ∧
      (∑ index, coefficients basis matrix parameter index • basis index) * value = 1 := by
  have multiplicationUnit : IsUnit (LinearMap.mulLeft ℂ value) :=
    (Module.End.isUnit_iff _).mpr (IsUnit.isUnit_iff_mulLeft_bijective.mp unit)
  have matrixUnit : IsUnit (matrix parameter) := by
    rw [equality]
    exact (LinearMap.isUnit_toMatrix_iff basis).mpr multiplicationUnit
  let candidate := ∑ index, coefficients basis matrix parameter index • basis index
  have represented : (fun index => basis.repr (value * candidate) index) = fun index => basis.repr 1 index := by
    calc
      _ = (matrix parameter) *ᵥ (fun index => basis.repr candidate index) := by
        rw [equality]
        exact (LinearMap.toMatrix_mulVec_repr basis basis (LinearMap.mulLeft ℂ value) candidate).symm
      _ = (matrix parameter) *ᵥ coefficients basis matrix parameter := by
        rw [basis.repr_sum_self]
      _ = _ := by
        change (matrix parameter) *ᵥ ((matrix parameter)⁻¹ *ᵥ (fun index => basis.repr 1 index)) = _
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp matrixUnit), Matrix.one_mulVec]
  have left : value * candidate = 1 :=
    basis.repr.injective (Finsupp.ext (fun index => congrFun represented index))
  refine ⟨left, unit.mul_left_cancel ?_⟩
  rw [← mul_assoc, left, one_mul, mul_one]

theorem exists_inverse_coefficients {AlgebraType Indices : Type*} [Ring AlgebraType] [Algebra ℂ AlgebraType]
    [Fintype Indices] [DecidableEq Indices] (basis : Module.Basis Indices ℂ AlgebraType)
    (lower : ℝ) (family : {parameter : ℂ // lower < parameter.re} → AlgebraType)
    (functionalContinuations : ∀ functional : AlgebraType →ₗ[ℂ] ℂ,
      ∃ continuation : ℂ → ℂ, (∀ parameter, MeromorphicAt continuation parameter) ∧
        ∀ parameter, continuation parameter.val = functional (family parameter))
    (eventualUnit : ∃ cutoff : ℝ, lower < cutoff ∧
      ∀ parameter, cutoff ≤ parameter.val.re → IsUnit (family parameter)) :
    ∃ coefficientFamily : ℂ → Indices → ℂ, ∃ cutoff : ℝ, lower < cutoff ∧
      (∀ index parameter, MeromorphicAt (fun parameter => coefficientFamily parameter index) parameter) ∧
      ∀ parameter, cutoff ≤ parameter.val.re →
        family parameter * (∑ index, coefficientFamily parameter.val index • basis index) = 1 ∧
          (∑ index, coefficientFamily parameter.val index • basis index) * family parameter = 1 := by
  obtain ⟨matrix, meromorphic, equality⟩ := multiplication_matrix basis
    {parameter : ℂ | lower < parameter.re} family functionalContinuations
  obtain ⟨cutoff, bound, invertible⟩ := eventualUnit
  refine ⟨coefficients basis matrix, cutoff, bound, coefficients_meromorphic basis matrix meromorphic, ?_⟩
  intro parameter above
  exact inverse_identity basis matrix parameter.val (family parameter) (invertible parameter above) (equality parameter)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteAlgebraInverse
