module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.RotationGroup

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_atInfinity_continuous : Continuous (atInfinity : BinaryRealGL → BinaryAdelicGL) := by
  have value : Continuous (fun matrix : BinaryRealGL => matrix.val) := Units.continuous_val
  have inverse : Continuous (fun matrix : BinaryRealGL => (matrix⁻¹).val) := Units.continuous_val.comp continuous_inv
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : BinaryRealGL => (matrix.val row column, (1 : Matrix (Fin 2) (Fin 2) FiniteAdeles) row column))
    exact ((continuous_apply column).comp ((continuous_apply row).comp value)).prodMk continuous_const
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : BinaryRealGL => ((matrix⁻¹).val row column, (1 : Matrix (Fin 2) (Fin 2) FiniteAdeles) row column))
    exact ((continuous_apply column).comp ((continuous_apply row).comp inverse)).prodMk continuous_const

noncomputable def cuspCircularOrbit (cusp : CuspidalRepresentation) (vector : cusp.H) (angle : AddCircle (1 : ℝ)) : cusp.H :=
  cusp.π (atInfinity (binaryCircleRotation angle.toCircle)) vector

theorem cuspCircularOrbit_continuous (cusp : CuspidalRepresentation) (vector : cusp.H) :
    Continuous (cuspCircularOrbit cusp vector) :=
  (cusp.continuous vector).comp
    (binary_atInfinity_continuous.comp (binaryCircleRotation_continuous.comp AddCircle.continuous_toCircle))

theorem cuspCircularOrbit_zero (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cuspCircularOrbit cusp vector 0 = vector := by
  simp [cuspCircularOrbit, binary_atInfinity_one]

theorem cuspCircularOrbit_add (cusp : CuspidalRepresentation) (vector : cusp.H) (first second : AddCircle (1 : ℝ)) :
    cuspCircularOrbit cusp vector (first + second) =
      cuspCircularOrbit cusp (cuspCircularOrbit cusp vector second) first := by
  simp only [cuspCircularOrbit, AddCircle.toCircle_add, map_mul, binary_atInfinity_mul, Module.End.mul_apply]

theorem cuspCircularOrbit_norm (cusp : CuspidalRepresentation) (vector : cusp.H) (angle : AddCircle (1 : ℝ)) :
    ‖cuspCircularOrbit cusp vector angle‖ = ‖vector‖ := cusp.unitary _ _

theorem cuspCircularOrbit_map_add (cusp : CuspidalRepresentation) (first second : cusp.H) (angle : AddCircle (1 : ℝ)) :
    cuspCircularOrbit cusp (first + second) angle = cuspCircularOrbit cusp first angle + cuspCircularOrbit cusp second angle :=
  map_add _ _ _

theorem cuspCircularOrbit_map_smul (cusp : CuspidalRepresentation) (scalar : ℂ) (vector : cusp.H) (angle : AddCircle (1 : ℝ)) :
    cuspCircularOrbit cusp (scalar • vector) angle = scalar • cuspCircularOrbit cusp vector angle :=
  map_smul _ _ _

theorem circle_fourier_norm (weight : ℤ) (angle : AddCircle (1 : ℝ)) : ‖fourier weight angle‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem circle_fourier_add (weight : ℤ) (first second : AddCircle (1 : ℝ)) :
    fourier weight (first + second) = fourier weight first * fourier weight second := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem cuspRotationFourier_integrable (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    Integrable (fun angle : AddCircle (1 : ℝ) => fourier (-weight) angle • cuspCircularOrbit cusp vector angle)
      AddCircle.haarAddCircle := by
  apply integrableOn_univ.mp
  exact ContinuousOn.integrableOn_compact isCompact_univ
    (((fourier (-weight)).continuous.smul (cuspCircularOrbit_continuous cusp vector)).continuousOn)

noncomputable def cuspRotationFourier (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) : cusp.H :=
  ∫ angle : AddCircle (1 : ℝ), fourier (-weight) angle • cuspCircularOrbit cusp vector angle ∂AddCircle.haarAddCircle

theorem cuspRotationFourier_eq_fourierCoeff (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    cuspRotationFourier cusp weight vector = fourierCoeff (cuspCircularOrbit cusp vector) weight := rfl

theorem cuspRotationFourier_norm_le (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    ‖cuspRotationFourier cusp weight vector‖ ≤ ‖vector‖ := by
  calc
    _ ≤ ∫ angle : AddCircle (1 : ℝ), ‖fourier (-weight) angle • cuspCircularOrbit cusp vector angle‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ = ‖vector‖ := by simp only [norm_smul, circle_fourier_norm, cuspCircularOrbit_norm, one_mul]; simp

noncomputable def cuspRotationProjection (cusp : CuspidalRepresentation) (weight : ℤ) : cusp.H →L[ℂ] cusp.H :=
  LinearMap.mkContinuous
    { toFun := cuspRotationFourier cusp weight
      map_add' := fun first second => by
        simp only [cuspRotationFourier, cuspCircularOrbit_map_add, smul_add]
        exact integral_add (cuspRotationFourier_integrable cusp weight first) (cuspRotationFourier_integrable cusp weight second)
      map_smul' := fun scalar vector => by
        simp only [cuspRotationFourier, cuspCircularOrbit_map_smul, RingHom.id_apply]
        rw [← integral_smul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun angle => smul_comm _ _ _) }
    1 (fun vector => by
      change ‖cuspRotationFourier cusp weight vector‖ ≤ 1 * ‖vector‖
      simpa only [one_mul] using cuspRotationFourier_norm_le cusp weight vector)

theorem cuspRotationProjection_apply (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    cuspRotationProjection cusp weight vector = cuspRotationFourier cusp weight vector := rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
