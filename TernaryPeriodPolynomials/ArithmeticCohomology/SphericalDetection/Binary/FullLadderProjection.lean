module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FullLadderComparison

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

theorem cuspRotationProjection_full_differentiable (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    DifferentiableAt ℝ (cuspMatrixOrbit cusp (cuspRotationProjection cusp weight vector.val)) 1 := by
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  exact ((cuspRotationProjection_full_contDiffOn cusp weight vector).contDiffAt
    (domain_open.mem_nhds (by simp))).differentiableAt (by simp)

theorem cuspMatrixDifferential_projection_integral (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (direction : BinaryRealMatrix) :
    Integrable (fun angle : Circle => (angle : ℂ) ^ (-weight) •
      cuspMatrixDifferential cusp (cusp.π (atInfinity (binaryRotations angle)) vector.val) direction) binaryRotationMeasure ∧
    cuspMatrixDifferential cusp (cuspRotationProjection cusp weight vector.val) direction =
      ∫ angle : Circle, (angle : ℂ) ^ (-weight) •
        cuspMatrixDifferential cusp (cusp.π (atInfinity (binaryRotations angle)) vector.val) direction ∂binaryRotationMeasure := by
  let domain : Set ℝ := {parameter | (binaryMatrixLine direction parameter).det ≠ 0}
  have domain_open : IsOpen domain :=
    isOpen_ne_fun ((binaryMatrixLine_contDiff direction (order := 1)).continuous.matrix_det) continuous_const
  have member : (0 : ℝ) ∈ domain := by simp [domain, binaryMatrixLine]
  let values : ℝ → BinaryRealMatrix → cusp.H := fun parameter matrix =>
    binaryMatrixRotationCoordinate matrix ^ (-weight) •
      cusp.π (atInfinity (invertibleMatrix (binaryMatrixLine direction parameter * matrix))) vector.val
  have kernel := (cuspRotationProjection_kernel_contDiffOn cusp weight vector).of_le
    (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
  have first : ContDiffOn ℝ 1 (fun pair : ℝ × BinaryRealMatrix => binaryMatrixLine direction pair.1)
      (domain ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) :=
    (binaryMatrixLine_contDiff direction (order := 1)).comp contDiff_fst |>.contDiffOn
  have regular : ContDiffOn ℝ 1 (Function.uncurry values) (domain ×ˢ {matrix | matrix.det ≠ 0}) :=
    kernel.comp (first.prodMk contDiffOn_snd) (fun _ pair_mem => pair_mem)
  have derivative_value (angle : Circle) :
      deriv (fun parameter => values parameter (binaryRotationMatrix angle)) 0 =
        (angle : ℂ) ^ (-weight) • cuspMatrixDifferential cusp
          (cusp.π (atInfinity (binaryRotations angle)) vector.val) direction := by
    let shifted : cusp.smooth := ⟨cusp.π (atInfinity (binaryRotations angle)) vector.val,
      cusp.smooth_stable _ _ vector.property⟩
    have shifted_derivative := (cuspMatrixDifferential_curve cusp shifted.val
      (cuspMatrixOrbit_smooth_differentiable cusp shifted) direction).const_smul ((angle : ℂ) ^ (-weight))
    have equality : (fun parameter => values parameter (binaryRotationMatrix angle)) =ᶠ[nhds 0]
        (fun parameter => (angle : ℂ) ^ (-weight) • cuspMatrixOrbit cusp shifted.val (binaryMatrixLine direction parameter)) := by
      filter_upwards [binaryMatrixLine_eventually_invertible direction] with parameter invertible
      dsimp only [values]
      rw [binaryMatrixRotationCoordinate_rotation, invertibleMatrix_mul _ _ invertible
        (by rw [binaryRotationMatrix_det]; exact one_ne_zero), binaryRotationMatrix, invertibleMatrix_coe,
        atInfinity_mul, map_mul]
      rfl
    exact (shifted_derivative.congr_of_eventuallyEq equality).deriv
  have continuous := (binaryRotationAverage_fderiv_continuous values domain domain_open regular 0 member).clm_apply
    (continuous_const (y := (1 : ℝ)))
  change Continuous (fun angle => deriv (fun parameter => values parameter (binaryRotationMatrix angle)) 0) at continuous
  have integrable := (continuous.congr derivative_value).integrable_of_hasCompactSupport
    (μ := binaryRotationMeasure) (HasCompactSupport.of_compactSpace _)
  refine ⟨integrable, ?_⟩
  have derivative := binaryRotationAverage_hasDerivAt values domain domain_open regular 0 member
  simp_rw [derivative_value] at derivative
  have equality : (fun parameter => cuspMatrixOrbit cusp (cuspRotationProjection cusp weight vector.val)
      (binaryMatrixLine direction parameter)) =ᶠ[nhds 0]
      (fun parameter => ∫ angle : Circle, values parameter (binaryRotationMatrix angle) ∂binaryRotationMeasure) := by
    filter_upwards [binaryMatrixLine_eventually_invertible direction] with parameter invertible
    exact cuspRotationProjection_full_orbit cusp weight vector.val (binaryMatrixLine direction parameter) invertible
  exact (cuspMatrixDifferential_curve cusp _ (cuspRotationProjection_full_differentiable cusp weight vector) direction).unique
    (derivative.congr_of_eventuallyEq equality)

theorem cuspFullRaisingVector_projection (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    cuspFullRaisingVector cusp (cuspRotationProjection cusp weight vector.val) =
      cuspRotationProjection cusp (weight + 2) (cuspFullRaisingVector cusp vector.val) := by
  have horizontal := cuspMatrixDifferential_projection_integral cusp weight vector binarySymmetricGenerator
  have vertical := cuspMatrixDifferential_projection_integral cusp weight vector binaryDiagonalGenerator
  calc
    _ = ∫ angle : Circle, (angle : ℂ) ^ (-weight) •
        cuspFullRaisingVector cusp (cusp.π (atInfinity (binaryRotations angle)) vector.val) ∂binaryRotationMeasure := by
      rw [cuspFullRaisingVector, horizontal.2, vertical.2, ← integral_smul]
      refine (integral_add horizontal.1 (Integrable.smul Complex.I vertical.1)).symm.trans ?_
      apply integral_congr_ae
      filter_upwards [] with angle
      simp only [Pi.smul_apply, cuspFullRaisingVector, smul_add, smul_smul]
      module
    _ = _ := by
      unfold cuspRotationProjection
      apply integral_congr_ae
      filter_upwards [] with angle
      rw [cuspFullRaisingVector_rotation cusp vector angle, smul_smul, ← zpow_add₀ (Circle.coe_ne_zero angle)]
      congr 2
      omega

theorem cuspRaisingVector_projection (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    cuspRaisingVector cusp weight (cuspRotationProjection cusp weight vector.val) =
      cuspRotationProjection cusp (weight + 2) (cuspFullRaisingVector cusp vector.val) := by
  rw [← cuspFullRaisingVector_eq_weighted cusp weight _ (cuspRotationProjection_full_differentiable cusp weight vector)
    (cuspRotationProjection_rotation cusp weight vector.val), cuspFullRaisingVector_projection]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
