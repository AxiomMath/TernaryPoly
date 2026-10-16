module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ClassicalCuspForms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.ArithmeticModularity
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.ClassicalCuspForms

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteClassicalComponents

theorem equal_reduction_congruence (first second : IntegralBinaryGL)
    (equality : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second) :
    first⁻¹ * second ∈ integralCongruence := by
  change GeneralLinearGroup.map integralReduction (first⁻¹ * second) = 1
  rw [map_mul, map_inv, equality, inv_mul_cancel]

theorem realize_equal_reduction (data : CuspidalRepresentation) (vector : data.smooth)
    (fixed : vector.val ∈ fixedSubspace data finiteCongruence)
    (first second : IntegralBinaryGL)
    (equality : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second)
    (realPoint : BinaryRealGL) :
    data.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding first) * atInfinity realPoint) =
      data.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding second) * atInfinity realPoint) := by
  have fixedValue := realize_right_fixed data vector fixed
    (GeneralLinearGroup.map integralEmbedding (first⁻¹ * second))
    ⟨_, equal_reduction_congruence first second equality, rfl⟩
    (atFinite (GeneralLinearGroup.map integralEmbedding first) * atInfinity realPoint)
  rw [mul_assoc, ← atFinite_atInfinity_commute, ← mul_assoc, ← atFinite_mul,
    ← map_mul, mul_inv_cancel_left] at fixedValue
  exact fixedValue.symm

theorem realizationLinear_equal_reduction {degree : ℕ} (data : InducingData degree)
    (first second : IntegralBinaryGL)
    (equality : GeneralLinearGroup.map integralReduction first = GeneralLinearGroup.map integralReduction second) :
    realizationLinear data first = realizationLinear data second := by
  apply LinearMap.ext
  intro vector
  apply CuspForm.ext
  intro argument
  simp only [realizationLinear_apply, HighestWeightHolomorphic.function,
    UpperTriangularChart.raw_eq data.cusp _ vector.val argument argument.im_pos]
  rw [realize_equal_reduction data.cusp vector.val vector.property.1 first second equality]

abbrev Residue := Set.range (GeneralLinearGroup.map integralReduction (n := Fin 2))

noncomputable def representative (residue : Residue) : IntegralBinaryGL := Classical.choose residue.property

theorem representative_reduction (residue : Residue) :
    GeneralLinearGroup.map integralReduction (representative residue) = residue.val :=
  Classical.choose_spec residue.property

noncomputable def finiteRealization {degree : ℕ} (data : InducingData degree) :
    fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ)) →ₗ[ℂ]
      (Residue → CuspForm arithmeticGroup (degree + 3)) :=
  LinearMap.pi (fun residue => realizationLinear data (representative residue))

theorem finiteRealization_determines_integral {degree : ℕ} (data : InducingData degree)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ)))
    (vanishing : finiteRealization data vector = 0) (point : IntegralBinaryGL) :
    realizationLinear data point vector = 0 := by
  let residue : Residue := ⟨GeneralLinearGroup.map integralReduction point, point, rfl⟩
  have equality : realizationLinear data (representative residue) = realizationLinear data point :=
    realizationLinear_equal_reduction data _ point (representative_reduction residue)
  have evaluated := congrFun vanishing residue
  change realizationLinear data (representative residue) vector = 0 at evaluated
  rwa [equality] at evaluated

theorem finiteRealization_zero_iff {degree : ℕ} (data : InducingData degree)
    (vector : fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :
    finiteRealization data vector = 0 ↔ ∀ point : IntegralBinaryGL, realizationLinear data point vector = 0 := by
  constructor
  · exact finiteRealization_determines_integral data vector
  · intro vanishing
    funext residue
    exact vanishing (representative residue)

instance finite_target (degree : ℕ) : FiniteDimensional ℂ (Residue → CuspForm arithmeticGroup (degree + 3)) := by
  let _ : Fintype Residue := Fintype.ofFinite _
  infer_instance

theorem finiteDimensional_of_injective {degree : ℕ} (data : InducingData degree)
    (injective : Function.Injective (finiteRealization data)) :
    FiniteDimensional ℂ (fixedMode data.cusp finiteCongruence (-(degree + 3 : ℤ))) :=
  FiniteDimensional.of_injective (finiteRealization data) injective

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteClassicalComponents
