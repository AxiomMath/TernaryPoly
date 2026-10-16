module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RotationSmallDivisors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance scalarRotationProjectionMeasurable : MeasurableSpace Circle := borel Circle
local instance scalarRotationProjectionBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspScalarRotationOrbit_continuous (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryAdelicGL) :
    Continuous (fun angle : Circle => cusp.realize vector (base * atInfinity (binaryRotations angle))) := by
  have real_regular := smooth_one_contDiffOn
    (function := fun matrix => cusp.realize vector (base * atInfinity matrix)) (cusp.scalarSmooth vector base)
  have real_continuous : Continuous (fun matrix : BinaryRealGL => cusp.realize vector (base * atInfinity matrix)) :=
    realGL_continuous_of_contDiffOn real_regular
  exact real_continuous.comp binaryRotations_continuous

theorem cuspScalarRotationIntegrand_integrable (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    Integrable (fun angle : Circle => (angle : ℂ) ^ (-weight) *
      cusp.realize vector (base * atInfinity (binaryRotations angle))) binaryRotationMeasure := by
  have character : Continuous (fun angle : Circle => (angle : ℂ) ^ (-weight)) :=
    (show Continuous (fun angle : Circle => (angle : ℂ)) by fun_prop).zpow₀ _
      (fun angle => Or.inl (Circle.coe_ne_zero angle))
  exact (character.mul (cuspScalarRotationOrbit_continuous cusp vector base)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Scalar rotation averaging is defined directly on the supplied realization. -/
def cuspScalarRotationCoefficient (cusp : CuspidalRepresentation) (weight : ℤ) (base : BinaryAdelicGL) :
    cusp.smooth →ₗ[ℂ] ℂ where
  toFun vector := ∫ angle : Circle, (angle : ℂ) ^ (-weight) *
    cusp.realize vector (base * atInfinity (binaryRotations angle)) ∂binaryRotationMeasure
  map_add' first second := by
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (cuspScalarRotationIntegrand_integrable cusp weight first base)
      (cuspScalarRotationIntegrand_integrable cusp weight second base)
  map_smul' scalar vector := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ scalar]
    exact integral_const_mul _ _

theorem cuspScalarRotationCoefficient_weight (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) :
    cuspScalarRotationCoefficient cusp weight base vector = cusp.realize vector base := by
  change (∫ angle : Circle, (angle : ℂ) ^ (-weight) *
    cusp.realize vector (base * atInfinity (binaryRotations angle)) ∂binaryRotationMeasure) = _
  have constant (angle : Circle) : (angle : ℂ) ^ (-weight) *
      cusp.realize vector (base * atInfinity (binaryRotations angle)) = cusp.realize vector base := by
    rw [cuspRealization_right_eigenvector cusp vector _ _ (rotation angle), ← mul_assoc,
      ← zpow_add₀ (Circle.coe_ne_zero angle), neg_add_cancel, zpow_zero, one_mul]
  simp only [constant, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

theorem cuspScalarRotationCoefficient_translate (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (angle : Circle) :
    cuspScalarRotationCoefficient cusp weight base
      (cuspSmoothAction cusp (atInfinity (binaryRotations angle)) vector) =
      (angle : ℂ) ^ weight * cuspScalarRotationCoefficient cusp weight base vector := by
  change (∫ other : Circle, (other : ℂ) ^ (-weight) *
    cusp.realize (cuspSmoothAction cusp (atInfinity (binaryRotations angle)) vector)
      (base * atInfinity (binaryRotations other)) ∂binaryRotationMeasure) = _
  have inverse_character : (angle : ℂ) ^ weight * (angle : ℂ) ^ (-weight) = 1 := by
    rw [← zpow_add₀ (Circle.coe_ne_zero angle), add_neg_cancel, zpow_zero]
  calc
    _ = ∫ other : Circle, (angle : ℂ) ^ weight *
        (((other * angle : Circle) : ℂ) ^ (-weight) *
          cusp.realize vector (base * atInfinity (binaryRotations (other * angle)))) ∂binaryRotationMeasure := by
      apply integral_congr_ae
      filter_upwards [] with other
      rw [cuspSmoothAction_realize, mul_assoc, ← atInfinity_mul, ← map_mul,
        Circle.coe_mul, mul_zpow]
      linear_combination -((other : ℂ) ^ (-weight) *
        cusp.realize vector (base * atInfinity (binaryRotations (other * angle)))) * inverse_character
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_mul_right_eq_self (fun other : Circle => (other : ℂ) ^ (-weight) *
        cusp.realize vector (base * atInfinity (binaryRotations other))) angle

/-- A finite rotation difference has zero scalar coefficient at that rotation character. -/
theorem cuspScalarRotationCoefficient_difference (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (angle : Circle) :
    cuspScalarRotationCoefficient cusp weight base
      (cuspSmoothAction cusp (atInfinity (binaryRotations angle)) vector - (angle : ℂ) ^ weight • vector) = 0 := by
  rw [map_sub, map_smul, cuspScalarRotationCoefficient_translate, smul_eq_mul, sub_self]

/-- An algebraic difference witness suffices to compare scalar averaging with a Hilbert weight component. -/
theorem cuspScalarRotationCoefficient_of_difference (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector component primitive : cusp.smooth) (base : BinaryAdelicGL) (angle : Circle)
    (rotation : ∀ other : Circle, cusp.π (atInfinity (binaryRotations other)) component.val =
      (other : ℂ) ^ weight • component.val)
    (difference : vector.val - component.val =
      cusp.π (atInfinity (binaryRotations angle)) primitive.val - (angle : ℂ) ^ weight • primitive.val) :
    cuspScalarRotationCoefficient cusp weight base vector = cusp.realize component base := by
  have equality : vector - component =
      cuspSmoothAction cusp (atInfinity (binaryRotations angle)) primitive - (angle : ℂ) ^ weight • primitive :=
    Subtype.ext difference
  have vanishes := congrArg (cuspScalarRotationCoefficient cusp weight base) equality
  rw [map_sub, cuspScalarRotationCoefficient_weight cusp weight component base rotation,
    cuspScalarRotationCoefficient_difference] at vanishes
  exact sub_eq_zero.mp vanishes

end TernaryPeriodPolynomials.SphericalDetection.Helpers
