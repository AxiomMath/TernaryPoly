module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveCocycleDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem additiveTwoCocycle_hasDerivAt (action : ℝ → E →L[ℝ] E) (cycle : ℝ → ℝ → E)
    (cocycle : ∀ first second third,
      cycle (first + second) third + cycle first second = action first (cycle second third) + cycle first (second + third))
    (tangent : ℝ → E) (derivative : ∀ first, HasDerivAt (cycle first) (tangent first) 0)
    (first second : ℝ) :
    HasDerivAt (cycle first) (tangent (first + second) - action first (tangent second)) second := by
  have translated : HasDerivAt (fun parameter => cycle first (second + parameter))
      (tangent (first + second) - action first (tangent second)) 0 := by
    have computed := ((derivative (first + second)).add_const (cycle first second)).sub
      ((action first).hasFDerivAt.comp_hasDerivAt 0 (derivative second))
    convert computed using 1
    funext parameter
    change cycle first (second + parameter) =
      cycle (first + second) parameter + cycle first second - action first (cycle second parameter)
    have relation := cocycle first second parameter
    linear_combination (norm := abel) -relation
  have shifted := translated.scomp_of_eq second ((hasDerivAt_id second).sub_const second) (sub_self second).symm
  convert shifted using 1 <;> simp [Function.comp_def, sub_eq_add_neg]

def additiveTwoCocyclePrimitive [CompleteSpace E] (tangent : ℝ → E) (point : ℝ) : E :=
  -(∫ parameter in 0..point, tangent parameter)

theorem additiveTwoCocyclePrimitive_zero [CompleteSpace E] (tangent : ℝ → E) :
    additiveTwoCocyclePrimitive tangent 0 = 0 := by
  simp [additiveTwoCocyclePrimitive]

theorem additiveTwoCocyclePrimitive_hasDerivAt [CompleteSpace E] (tangent : ℝ → E)
    (regular : Continuous tangent) (point : ℝ) :
    HasDerivAt (additiveTwoCocyclePrimitive tangent) (-tangent point) point := by
  exact (intervalIntegral.integral_hasDerivAt_right (regular.intervalIntegrable 0 point)
    regular.stronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt).neg

theorem additiveTwoCocyclePrimitive_boundary [CompleteSpace E] (action : ℝ → E →L[ℝ] E)
    (cycle : ℝ → ℝ → E)
    (cocycle : ∀ first second third,
      cycle (first + second) third + cycle first second = action first (cycle second third) + cycle first (second + third))
    (origin : ∀ first, cycle first 0 = 0)
    (tangent : ℝ → E) (derivative : ∀ first, HasDerivAt (cycle first) (tangent first) 0)
    (regular : Continuous tangent) (first second : ℝ) :
    cycle first second = action first (additiveTwoCocyclePrimitive tangent second) -
      additiveTwoCocyclePrimitive tangent (first + second) + additiveTwoCocyclePrimitive tangent first := by
  let boundary (point : ℝ) := action first (additiveTwoCocyclePrimitive tangent point) -
    additiveTwoCocyclePrimitive tangent (first + point) + additiveTwoCocyclePrimitive tangent first
  have boundary_derivative (point : ℝ) : HasDerivAt boundary
      (tangent (first + point) - action first (tangent point)) point := by
    have translated := (additiveTwoCocyclePrimitive_hasDerivAt tangent regular (first + point)).scomp point
      ((hasDerivAt_id point).const_add first)
    have computed := (((action first).hasFDerivAt.comp_hasDerivAt point
      (additiveTwoCocyclePrimitive_hasDerivAt tangent regular point)).sub translated).add_const
        (additiveTwoCocyclePrimitive tangent first)
    simpa only [boundary, Function.comp_def, Pi.sub_apply, one_smul, map_neg, neg_sub_neg] using computed
  have difference_derivative (point : ℝ) : HasDerivAt (fun sample => cycle first sample - boundary sample) 0 point := by
    change HasDerivAt (cycle first - boundary) 0 point
    simpa only [sub_self] using
      (additiveTwoCocycle_hasDerivAt action cycle cocycle tangent derivative first point).sub (boundary_derivative point)
  have constant := is_const_of_deriv_eq_zero (fun point => (difference_derivative point).differentiableAt)
    (fun point => (difference_derivative point).deriv)
  have equality := constant second 0
  have boundary_zero : boundary 0 = 0 := by
    simp [boundary, additiveTwoCocyclePrimitive_zero]
  rw [origin, boundary_zero, sub_zero] at equality
  exact sub_eq_zero.mp equality

def additiveTwoCocycleTangent (cycle : ℝ → ℝ → E) (point : ℝ) : E :=
  fderiv ℝ (Function.uncurry cycle) (point, 0) (0, 1)

theorem additiveTwoCocycleTangent_derivative (cycle : ℝ → ℝ → E)
    (regular : ContDiff ℝ 1 (Function.uncurry cycle)) (point : ℝ) :
    HasDerivAt (cycle point) (additiveTwoCocycleTangent cycle point) 0 := by
  have curve : HasDerivAt (fun parameter : ℝ => (point, parameter)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℝ) point).prodMk (hasDerivAt_id 0)
  exact ((regular.differentiable (by norm_num) (point, 0)).hasFDerivAt).comp_hasDerivAt 0 curve

theorem additiveTwoCocycleTangent_continuous (cycle : ℝ → ℝ → E)
    (regular : ContDiff ℝ 1 (Function.uncurry cycle)) :
    Continuous (additiveTwoCocycleTangent cycle) := by
  exact (regular.continuous_fderiv_apply (by norm_num)).comp
    (show Continuous (fun point : ℝ => ((point, (0 : ℝ)), ((0 : ℝ), (1 : ℝ)))) by fun_prop)

theorem additiveTwoCocycle_exists_primitive [CompleteSpace E] (action : ℝ → E →L[ℝ] E)
    (cycle : ℝ → ℝ → E)
    (cocycle : ∀ first second third,
      cycle (first + second) third + cycle first second = action first (cycle second third) + cycle first (second + third))
    (origin : ∀ first, cycle first 0 = 0)
    (regular : ContDiff ℝ 1 (Function.uncurry cycle)) :
    ∃ primitive : ℝ → E, primitive 0 = 0 ∧ Differentiable ℝ primitive ∧
      ∀ first second, cycle first second = action first (primitive second) - primitive (first + second) + primitive first := by
  let tangent := additiveTwoCocycleTangent cycle
  have continuous : Continuous tangent := additiveTwoCocycleTangent_continuous cycle regular
  refine ⟨additiveTwoCocyclePrimitive tangent, additiveTwoCocyclePrimitive_zero tangent, ?_, ?_⟩
  · intro point
    exact (additiveTwoCocyclePrimitive_hasDerivAt tangent continuous point).differentiableAt
  · exact additiveTwoCocyclePrimitive_boundary action cycle cocycle origin tangent
      (additiveTwoCocycleTangent_derivative cycle regular) continuous

theorem additiveTwoCocyclePrimitive_contDiff [CompleteSpace E] {order : ℕ∞} (tangent : ℝ → E)
    (regular : ContDiff ℝ order tangent) :
    ContDiff ℝ ((order : WithTop ℕ∞) + 1) (additiveTwoCocyclePrimitive tangent) := by
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun point => (additiveTwoCocyclePrimitive_hasDerivAt tangent regular.continuous point).differentiableAt,
    by simp, ?_⟩
  have derivative : deriv (additiveTwoCocyclePrimitive tangent) = fun point => -tangent point :=
    funext (fun point => (additiveTwoCocyclePrimitive_hasDerivAt tangent regular.continuous point).deriv)
  rw [derivative]
  exact regular.neg

theorem additiveTwoCocycleTangent_contDiff (cycle : ℝ → ℝ → E) {order : ℕ∞}
    (regular : ContDiff ℝ ((order : WithTop ℕ∞) + 1) (Function.uncurry cycle)) :
    ContDiff ℝ order (additiveTwoCocycleTangent cycle) := by
  exact (regular.contDiff_fderiv_apply (m := order) le_rfl).comp
    (show ContDiff ℝ order (fun point : ℝ => ((point, (0 : ℝ)), ((0 : ℝ), (1 : ℝ)))) by fun_prop)

theorem additiveTwoCocycle_exists_smooth_primitive [CompleteSpace E] (action : ℝ → E →L[ℝ] E)
    (cycle : ℝ → ℝ → E)
    (cocycle : ∀ first second third,
      cycle (first + second) third + cycle first second = action first (cycle second third) + cycle first (second + third))
    (origin : ∀ first, cycle first 0 = 0)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (Function.uncurry cycle)) :
    ∃ primitive : ℝ → E, primitive 0 = 0 ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) primitive ∧
      ∀ first second, cycle first second = action first (primitive second) - primitive (first + second) + primitive first := by
  have differentiable : ContDiff ℝ 1 (Function.uncurry cycle) := regular.of_le (by simp)
  let tangent := additiveTwoCocycleTangent cycle
  have tangent_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) tangent :=
    additiveTwoCocycleTangent_contDiff cycle (by simpa using regular)
  refine ⟨additiveTwoCocyclePrimitive tangent, additiveTwoCocyclePrimitive_zero tangent, ?_, ?_⟩
  · simpa using additiveTwoCocyclePrimitive_contDiff tangent tangent_regular
  · exact additiveTwoCocyclePrimitive_boundary action cycle cocycle origin tangent
      (additiveTwoCocycleTangent_derivative cycle differentiable) tangent_regular.continuous

end TernaryPeriodPolynomials.SphericalDetection.Helpers
