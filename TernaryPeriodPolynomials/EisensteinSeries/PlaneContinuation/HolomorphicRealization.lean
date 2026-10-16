module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HolomorphicDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators
open scoped Manifold

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicRealization

theorem function_add (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (first second : data.smooth) (weight : ℤ) (argument : ℂ) :
    function data point (first + second) weight argument =
      function data point first weight argument + function data point second weight argument := by
  unfold function raw RotationScalarDerivative.scalarMatrixOrbit
  rw [map_add, Pi.add_apply, mul_add]

theorem function_smul (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (scalar : ℂ) (vector : data.smooth) (weight : ℤ) (argument : ℂ) :
    function data point (scalar • vector) weight argument = scalar * function data point vector weight argument := by
  unfold function raw RotationScalarDerivative.scalarMatrixOrbit
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem unit_I : unit Complex.I (by simp) = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [unit, matrix]

theorem function_I (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) : function data point vector weight Complex.I = data.realize vector point := by
  rw [function, raw_eq data point vector Complex.I (by simp), unit_I,
    AveragingSmooth.atInfinity_one, mul_one]
  simp [normalization]

noncomputable def realization (data : CuspidalRepresentation) (weight : ℤ) :
    data.smooth →ₗ[ℂ] (BinaryAdelicGL → UpperHalfPlane → ℂ) where
  toFun vector point argument := function data point vector weight argument
  map_add' first second := by
    funext point argument
    exact function_add data point first second weight argument
  map_smul' scalar vector := by
    funext point argument
    exact function_smul data point scalar vector weight argument

theorem realization_injective (data : CuspidalRepresentation) (weight : ℤ) :
    Function.Injective (realization data weight) := by
  intro first second equality
  apply data.injective
  funext point
  have evaluated := congrFun (congrFun equality point) (⟨Complex.I, by simp⟩ : UpperHalfPlane)
  change function data point first weight Complex.I = function data point second weight Complex.I at evaluated
  simpa only [function_I] using evaluated

theorem negative_endpoint_holomorphic {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth)
    (eigen : rotationOperator data.cusp vector = (Complex.I * (-(degree + 3 : ℤ))) • vector)
    (point : BinaryAdelicGL) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (realization data.cusp (degree + 3) vector point) := by
  apply HighestWeightHolomorphic.mdifferentiable data point vector (degree + 3)
    (by simpa only [Int.cast_neg] using eigen)
  exact CohomologicalCasimir.negative_endpoint_highest data vector eigen

theorem negative_endpoint_decay {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (point : BinaryAdelicGL) :
    UpperHalfPlane.IsZeroAtImInfty (realization data.cusp (degree + 3) vector point) :=
  HolomorphicDecay.isZeroAtImInfty data.cusp point vector (degree + 3) (by omega)

theorem exists_nonzero_holomorphic {degree : ℕ} (data : InducingData degree) :
    ∃ vector : data.cusp.smooth, ∃ point : BinaryAdelicGL,
      function data.cusp point vector (degree + 3) Complex.I ≠ 0 ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (realization data.cusp (degree + 3) vector point) ∧
      UpperHalfPlane.IsZeroAtImInfty (realization data.cusp (degree + 3) vector point) := by
  obtain ⟨vector, nonzero, eigen, _, _⟩ := CohomologicalCasimir.exists_highest_weight_fixed data
  have existsPoint : ∃ point : BinaryAdelicGL, data.cusp.realize vector point ≠ 0 := by
    by_contra! vanishing
    apply nonzero
    apply data.cusp.injective
    funext point
    rw [vanishing, map_zero, Pi.zero_apply]
  obtain ⟨point, nonzeroValue⟩ := existsPoint
  exact ⟨vector, point, by simpa only [function_I] using nonzeroValue,
    negative_endpoint_holomorphic data vector eigen point, negative_endpoint_decay data vector point⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicRealization
