module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ArithmeticModularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.LadderAdmissibility TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicRealization

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalCuspForms

theorem slash_invariant {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector)
    (point : IntegralBinaryGL) (matrix : BinaryRealGL) (membership : matrix ∈ arithmeticGroup) :
    SlashAction.map (degree + 3 : ℤ) matrix
        (realization data.cusp (degree + 3) vector (atFinite (GeneralLinearGroup.map integralEmbedding point))) =
      realization data.cusp (degree + 3) vector (atFinite (GeneralLinearGroup.map integralEmbedding point)) := by
  obtain ⟨arithmetic, congruence, rfl⟩ := membership
  rw [ModularTransformation.slash_realization data vector _ (by simpa only [Int.cast_neg] using eigen) _ _ (by
    rw [SpecialLinearGroup.det_mapGL]; rfl)]
  exact realization_arithmetic data.cusp vector fixed _ arithmetic congruence point

noncomputable def cuspForm {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector)
    (point : IntegralBinaryGL) : CuspForm arithmeticGroup (degree + 3) where
  toFun := realization data.cusp (degree + 3) vector (atFinite (GeneralLinearGroup.map integralEmbedding point))
  slash_action_eq' := slash_invariant data vector fixed eigen point
  holo' := negative_endpoint_holomorphic data vector eigen _
  zero_at_cusps' := fun {_} _ =>
    ModularTransformation.zero_at_boundary data vector (degree + 3) (by omega)
      (by simpa only [Int.cast_neg] using eigen) _ _

theorem fixedMode_eigen {degree : ℕ} (data : InducingData degree)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :
    rotationOperator data.cusp vector.val = (Complex.I * (-(degree + 3 : ℤ))) • vector.val := by
  simpa only [Int.cast_neg] using (rotation_eigen_iff data.cusp vector.val _).mpr
    ((mem_fixedMode_iff data.cusp finiteCongruence _ vector.val).mp vector.property).2

noncomputable def realizationLinear {degree : ℕ} (data : InducingData degree) (point : IntegralBinaryGL) :
    fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ)) →ₗ[ℂ] CuspForm arithmeticGroup (degree + 3) where
  toFun vector := cuspForm data vector.val vector.property.1 (fixedMode_eigen data vector) point
  map_add' first second := by
    apply CuspForm.ext
    intro argument
    exact function_add data.cusp _ first.val second.val _ argument
  map_smul' scalar vector := by
    apply CuspForm.ext
    intro argument
    exact function_smul data.cusp _ scalar vector.val _ argument

theorem realizationLinear_apply {degree : ℕ} (data : InducingData degree) (point : IntegralBinaryGL)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) (argument : UpperHalfPlane) :
    realizationLinear data point vector argument =
      HighestWeightHolomorphic.function data.cusp
        (atFinite (GeneralLinearGroup.map integralEmbedding point)) vector.val (degree + 3) argument := rfl

instance cuspForm_finiteDimensional (weight : ℤ) : FiniteDimensional ℂ (CuspForm arithmeticGroup weight) := by
  let _ := ModularFiniteDimension.finiteDimensional (group := arithmeticGroup) weight
  exact FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalCuspForms
