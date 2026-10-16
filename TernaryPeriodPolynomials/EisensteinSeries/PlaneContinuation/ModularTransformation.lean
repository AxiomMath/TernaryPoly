module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HolomorphicTransform
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ModularTransformation

theorem sigma_of_det_one (matrix : BinaryRealGL) (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) :
    UpperHalfPlane.σ matrix = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp [UpperHalfPlane.σ, determinant]

theorem slash_det_one (weight : ℤ) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) (function : UpperHalfPlane → ℂ) :
    SlashAction.map weight matrix function = fun argument : UpperHalfPlane =>
      UpperHalfPlane.denom matrix argument ^ (-weight) * function (matrix • argument) := by
  rw [ModularForm.slash_def, sigma_of_det_one matrix determinant]
  funext argument
  simp [determinant, mul_comm]

theorem slash_realization {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (weight : ℤ)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (point : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) :
    SlashAction.map weight matrix (realization data.cusp weight vector point) =
      realization data.cusp weight vector (point * atInfinity matrix) := by
  rw [slash_det_one weight matrix determinant]
  funext argument
  exact (HolomorphicTransform.function_transform data vector weight eigen point matrix determinant argument).symm

theorem slash_zero_at_infty {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (weight : ℤ)
    (weightPositive : 0 < weight)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (point : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) :
    UpperHalfPlane.IsZeroAtImInfty (SlashAction.map weight matrix (realization data.cusp weight vector point)) := by
  rw [slash_realization data vector weight eigen point matrix determinant]
  exact HolomorphicDecay.isZeroAtImInfty data.cusp _ vector weight weightPositive

theorem zero_at_boundary {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) (weight : ℤ)
    (weightPositive : 0 < weight)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-weight : ℤ)) • vector)
    (point : BinaryAdelicGL) (boundary : OnePoint ℝ) :
    boundary.IsZeroAt (realization data.cusp weight vector point) weight := by
  obtain ⟨matrix, equality⟩ := OnePoint.exists_mem_SL2 ℝ boundary
  apply (OnePoint.isZeroAt_iff equality).mpr
  apply slash_zero_at_infty data vector weight weightPositive eigen point
  rw [Matrix.SpecialLinearGroup.det_mapGL]
  rfl

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ModularTransformation
