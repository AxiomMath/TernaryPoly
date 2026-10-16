module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointFormAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryEndpointPeriod (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (vector : cusp.H) (point : ℂ) : Fin (degree + 2) → cusp.H :=
  ∫ parameter : ℝ in 0..1, (point - Complex.I) •
    binaryEndpointHolomorphicForm cusp degree halfWeight vector
      (Complex.I + parameter • (point - Complex.I))

theorem binaryEndpointHolomorphicForm_continuousOn (cusp : CuspidalRepresentation)
    (degree : ℕ) (halfWeight : ℤ) (vector : cusp.H) :
    ContinuousOn (binaryEndpointHolomorphicForm cusp degree halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  apply continuousOn_pi.mpr
  intro position
  exact (continuous_iff_continuousAt.mpr (fun point =>
    (binaryPointPower_functional_analytic (degree + 1)
      ((binaryWeightBasis (degree + 1)).coord position) point).continuousAt)).continuousOn.smul
        (cuspWeightedAffineOrbit_continuousOn cusp halfWeight vector)

theorem binaryEndpointPeriod_integrable (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) :
    IntervalIntegrable (fun parameter : ℝ => (point - Complex.I) •
      binaryEndpointHolomorphicForm cusp degree halfWeight vector
        (Complex.I + parameter • (point - Complex.I))) volume 0 1 := by
  have path_continuous : Continuous (fun parameter : ℝ => Complex.I + parameter • (point - Complex.I)) := by
    fun_prop
  exact ((continuousOn_const (c := point - Complex.I)).smul
    ((binaryEndpointHolomorphicForm_continuousOn cusp degree halfWeight vector).comp
      path_continuous.continuousOn (fun _ member => upperHalfPlane_straightPath ⟨point, positive⟩ member))).intervalIntegrable_of_Icc
        zero_le_one

theorem binaryEndpointPrimitive_eq_periods (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (degree : ℕ) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) :
    binaryEndpointPrimitive cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point =
      (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp degree halfWeight vector point +
        binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
          (binaryEndpointPeriod cusp degree halfWeight vector (binaryComplexReflection point))) := by
  let first : ℝ → Fin (degree + 2) → cusp.H := fun parameter => (point - Complex.I) •
    binaryEndpointHolomorphicForm cusp degree halfWeight vector
      (Complex.I + parameter • (point - Complex.I))
  let second : ℝ → Fin (degree + 2) → cusp.H := fun parameter =>
    (binaryComplexReflection point - Complex.I) •
      binaryEndpointHolomorphicForm cusp degree halfWeight vector
        (Complex.I + parameter • (binaryComplexReflection point - Complex.I))
  let reflection := binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
  have first_integrable : IntervalIntegrable first volume 0 1 :=
    binaryEndpointPeriod_integrable cusp degree halfWeight vector point positive
  have second_integrable : IntervalIntegrable second volume 0 1 :=
    binaryEndpointPeriod_integrable cusp degree halfWeight vector (binaryComplexReflection point)
      (by rw [binaryComplexReflection_im]; exact positive)
  have reflected_integrable : IntervalIntegrable (fun parameter => reflection (second parameter)) volume 0 1 :=
    ⟨reflection.integrable_comp second_integrable.1, reflection.integrable_comp second_integrable.2⟩
  have direction : binaryComplexReflection point - Complex.I = -(starRingEnd ℂ (point - Complex.I)) := by
    simp [binaryComplexReflection]
    abel
  have path (parameter : ℝ) :
      binaryComplexReflection (Complex.I + parameter • (point - Complex.I)) =
        Complex.I + parameter • (binaryComplexReflection point - Complex.I) := by
    rw [map_add, map_smul, map_sub, binaryComplexReflection_basepoint]
  calc
    _ = ∫ parameter : ℝ in 0..1, (2 : ℂ)⁻¹ • (first parameter + reflection (second parameter)) := by
      apply intervalIntegral.integral_congr
      intro parameter member
      dsimp only
      have belongs : parameter ∈ Set.Icc 0 1 := by simpa only [Set.uIcc_of_le zero_le_one] using member
      rw [binaryEndpointDifferential_holomorphicForm cusp spherical degree halfWeight weight vector
        (Complex.I + parameter • (point - Complex.I))
        (upperHalfPlane_straightPath ⟨point, positive⟩ belongs), path]
      change (2 : ℂ)⁻¹ • (first parameter - (starRingEnd ℂ (point - Complex.I)) •
        reflection (binaryEndpointHolomorphicForm cusp degree halfWeight vector
          (Complex.I + parameter • (binaryComplexReflection point - Complex.I)))) = _
      dsimp only [second]
      rw [map_smul, direction, neg_smul, sub_eq_add_neg]
    _ = _ := by
      rw [intervalIntegral.integral_smul, intervalIntegral.integral_add first_integrable reflected_integrable,
        reflection.intervalIntegral_comp_comm second_integrable]
      rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
