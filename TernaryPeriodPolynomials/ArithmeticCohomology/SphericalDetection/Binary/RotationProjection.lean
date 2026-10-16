module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.FiniteProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderClosures
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationIntegralDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

def cuspRotationProjection (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) : cusp.H :=
  ∫ angle : Circle, (angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) vector ∂binaryRotationMeasure

theorem cuspRotationProjection_integrable (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) :
    Integrable (fun angle : Circle => (angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) vector)
      binaryRotationMeasure := by
  have character : Continuous (fun angle : Circle => (angle : ℂ) ^ (-weight)) :=
    (show Continuous (fun angle : Circle => (angle : ℂ)) by fun_prop).zpow₀ _
      (fun angle => Or.inl (Circle.coe_ne_zero angle))
  have orbit := (cusp.continuous vector).comp (atInfinity_continuous.comp binaryRotations_continuous)
  exact (character.smul orbit).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem cuspRotationProjection_rotation (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspRotationProjection cusp weight vector) =
      (angle : ℂ) ^ weight • cuspRotationProjection cusp weight vector := by
  have inverse_character : (angle : ℂ) ^ weight * (angle : ℂ) ^ (-weight) = 1 := by
    rw [← zpow_add₀ (Circle.coe_ne_zero angle), add_neg_cancel, zpow_zero]
  change cuspUnitaryOperator cusp (atInfinity (binaryRotations angle)) (∫ other : Circle,
    (other : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations other)) vector ∂binaryRotationMeasure) = _
  rw [← (cuspUnitaryOperator cusp (atInfinity (binaryRotations angle))).integral_comp_comm
    (cuspRotationProjection_integrable cusp weight vector)]
  calc
    _ = ∫ other : Circle, (angle : ℂ) ^ weight •
        (((angle * other : Circle) : ℂ) ^ (-weight) •
          cusp.π (atInfinity (binaryRotations (angle * other))) vector) ∂binaryRotationMeasure := by
      apply integral_congr_ae
      filter_upwards [] with other
      change cusp.π (atInfinity (binaryRotations angle))
        ((other : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations other)) vector) = _
      rw [map_smul]
      change (other : ℂ) ^ (-weight) •
        (cusp.π (atInfinity (binaryRotations angle)) * cusp.π (atInfinity (binaryRotations other))) vector = _
      rw [← map_mul, ← atInfinity_mul, ← map_mul, Circle.coe_mul, mul_zpow, smul_smul,
        ← mul_assoc, inverse_character, one_mul]
    _ = _ := by
      rw [integral_smul]
      congr 1
      exact integral_mul_left_eq_self (fun other : Circle =>
        (other : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations other)) vector) angle

theorem cuspRotationProjection_eq_self (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    cuspRotationProjection cusp weight vector = vector := by
  unfold cuspRotationProjection
  have constant (angle : Circle) : (angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) vector = vector := by
    rw [rotation, smul_smul, ← zpow_add₀ (Circle.coe_ne_zero angle), neg_add_cancel, zpow_zero, one_smul]
  simp only [constant, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

theorem cuspRotationProjection_finiteLevel (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cusp.H) (fixed : vector ∈ cuspFiniteLevelValues cusp level) :
    cuspRotationProjection cusp weight vector ∈ cuspFiniteLevelValues cusp level := by
  intro element
  change cuspUnitaryOperator cusp (atFinite element.val) (cuspRotationProjection cusp weight vector) = _
  unfold cuspRotationProjection
  rw [← (cuspUnitaryOperator cusp (atFinite element.val)).integral_comp_comm
    (cuspRotationProjection_integrable cusp weight vector)]
  apply integral_congr_ae
  filter_upwards [] with angle
  change cusp.π (atFinite element.val) ((angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) vector) = _
  rw [map_smul]
  congr 1
  exact cuspFiniteLevelValues_real cusp level (binaryRotations angle) vector fixed element

theorem cuspRotationProjection_inner_weight (cusp : CuspidalRepresentation) (weight : ℤ) (vector test : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    inner ℂ vector (cuspRotationProjection cusp weight test) = inner ℂ vector test := by
  have constant (angle : Circle) :
      inner ℂ vector ((angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) test) = inner ℂ vector test := by
    have inverse_rotation : cusp.π ((atInfinity (binaryRotations angle))⁻¹) vector =
        (angle : ℂ) ^ (-weight) • vector := by
      rw [← atInfinity_inv, ← map_inv, rotation, Circle.coe_inv, inv_zpow, zpow_neg]
    have paired := (cuspUnitaryIsometryEquiv cusp (atInfinity (binaryRotations angle))).symm.inner_map_eq_flip vector test
    change inner ℂ (cusp.π ((atInfinity (binaryRotations angle))⁻¹) vector) test =
      inner ℂ vector (cusp.π (atInfinity (binaryRotations angle)) test) at paired
    have conjugate : (starRingEnd ℂ) ((angle : ℂ) ^ (-weight)) = (angle : ℂ) ^ weight := by
      rw [map_zpow₀, ← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_zpow, ← zpow_neg, neg_neg]
    rw [inner_smul_right, ← paired, inverse_rotation, inner_smul_left, conjugate,
      ← mul_assoc, ← zpow_add₀ (Circle.coe_ne_zero angle), neg_add_cancel, zpow_zero, one_mul]
  unfold cuspRotationProjection
  change (innerSL ℂ vector) (∫ angle : Circle,
    (angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) test ∂binaryRotationMeasure) = _
  rw [← (innerSL ℂ vector).integral_comp_comm (cuspRotationProjection_integrable cusp weight test)]
  change (∫ angle : Circle, inner ℂ vector
    ((angle : ℂ) ^ (-weight) • cusp.π (atInfinity (binaryRotations angle)) test) ∂binaryRotationMeasure) = _
  simp only [constant, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

def binaryMatrixRotationCoordinate (matrix : BinaryRealMatrix) : ℂ :=
  (matrix 0 0 : ℂ) + Complex.I * (matrix 1 0 : ℂ)

theorem binaryMatrixRotationCoordinate_rotation (angle : Circle) :
    binaryMatrixRotationCoordinate (binaryRotationMatrix angle) = (angle : ℂ) := by
  apply Complex.ext <;> simp [binaryMatrixRotationCoordinate, binaryRotationMatrix, binaryRotations, binaryRotation]

theorem binaryMatrixRotationCoordinate_ne_zero (matrix : BinaryRealMatrix) (invertible : matrix.det ≠ 0) :
    binaryMatrixRotationCoordinate matrix ≠ 0 := by
  intro zero
  have real := congrArg Complex.re zero
  have imaginary := congrArg Complex.im zero
  simp only [binaryMatrixRotationCoordinate, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at real
  simp only [binaryMatrixRotationCoordinate, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.ofReal_re, Complex.zero_im] at imaginary
  apply invertible
  simp [Matrix.det_fin_two, real, imaginary]

theorem binaryMatrixRotationCoordinate_contDiff {order : WithTop ℕ∞} :
    ContDiff ℝ order binaryMatrixRotationCoordinate := by
  have entry (row column : Fin 2) : ContDiff ℝ order (fun matrix : BinaryRealMatrix => (matrix row column : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  exact (entry 0 0).add (contDiff_const.mul (entry 1 0))

theorem cuspRotationProjection_kernel_contDiffOn (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point : BinaryRealMatrix × BinaryRealMatrix => binaryMatrixRotationCoordinate point.2 ^ (-weight) •
        cusp.π (atInfinity (invertibleMatrix (point.1 * point.2))) vector.val)
      ({matrix | matrix.det ≠ 0} ×ˢ {matrix | matrix.det ≠ 0}) := by
  have multiplication : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun point : BinaryRealMatrix × BinaryRealMatrix => point.1 * point.2) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have regular := (smooth_one_contDiffOn (function := fun matrix => cusp.π (atInfinity matrix) vector.val)
    ((cusp.smooth_exact vector.val).mp vector.property).1).of_le (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ ⊤ from le_top)
  have product_regular := regular.comp multiplication.contDiffOn (s :=
    {matrix : BinaryRealMatrix | matrix.det ≠ 0} ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) (by
      intro point member
      change (point.1 * point.2).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero member.1 member.2)
  have character : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point : BinaryRealMatrix × BinaryRealMatrix => binaryMatrixRotationCoordinate point.2 ^ (-weight))
      ({matrix : BinaryRealMatrix | matrix.det ≠ 0} ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) := by
    intro point member
    have coordinate : AnalyticAt ℝ (fun argument : BinaryRealMatrix × BinaryRealMatrix =>
        binaryMatrixRotationCoordinate argument.2) point :=
      (binaryMatrixRotationCoordinate_contDiff (order := ⊤)).contDiffAt.analyticAt.fun_comp
        (contDiff_snd (𝕜 := ℝ) (E := BinaryRealMatrix) (F := BinaryRealMatrix) (n := ⊤)).contDiffAt.analyticAt
    exact (coordinate.zpow (n := -weight) (binaryMatrixRotationCoordinate_ne_zero point.2 member.2)).contDiffAt.contDiffWithinAt
  exact character.smul product_regular

theorem cuspRotationProjection_full_orbit (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.H)
    (matrix : BinaryRealMatrix) (invertible : matrix.det ≠ 0) :
    cusp.π (atInfinity (invertibleMatrix matrix)) (cuspRotationProjection cusp weight vector) =
      ∫ angle : Circle, binaryMatrixRotationCoordinate (binaryRotationMatrix angle) ^ (-weight) •
        cusp.π (atInfinity (invertibleMatrix (matrix * binaryRotationMatrix angle))) vector ∂binaryRotationMeasure := by
  change cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix)) (cuspRotationProjection cusp weight vector) = _
  unfold cuspRotationProjection
  rw [← (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).integral_comp_comm
    (cuspRotationProjection_integrable cusp weight vector)]
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [binaryMatrixRotationCoordinate_rotation,
    invertibleMatrix_mul _ _ invertible (by rw [binaryRotationMatrix_det]; exact one_ne_zero),
    binaryRotationMatrix, invertibleMatrix_coe, atInfinity_mul, map_mul]
  exact map_smul _ _ _

theorem cuspRotationProjection_full_contDiffOn (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun matrix : BinaryRealMatrix => cusp.π (atInfinity (invertibleMatrix matrix)) (cuspRotationProjection cusp weight vector.val))
      {matrix | matrix.det ≠ 0} := by
  have domain_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have averaged := binaryRotationAverage_contDiffOn domain_open
    (fun first second => binaryMatrixRotationCoordinate second ^ (-weight) •
      cusp.π (atInfinity (invertibleMatrix (first * second))) vector.val)
    (cuspRotationProjection_kernel_contDiffOn cusp weight vector)
  exact averaged.congr (fun matrix invertible => cuspRotationProjection_full_orbit cusp weight vector.val matrix invertible)

theorem cuspRotationProjection_curve_hasFDerivAt (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth)
    (matrices : ℝ → BinaryRealMatrix) (domain : Set ℝ) (domain_open : IsOpen domain)
    (matrices_regular : ContDiffOn ℝ 1 matrices domain)
    (invertible : ∀ parameter ∈ domain, (matrices parameter).det ≠ 0)
    (point : ℝ) (member : point ∈ domain) :
    HasFDerivAt (𝕜 := ℝ)
      (fun parameter => cusp.π (atInfinity (invertibleMatrix (matrices parameter))) (cuspRotationProjection cusp weight vector.val))
      (∫ angle : Circle, fderiv ℝ (fun parameter : ℝ => (angle : ℂ) ^ (-weight) •
        cusp.π (atInfinity (invertibleMatrix (matrices parameter * binaryRotationMatrix angle))) vector.val) point ∂binaryRotationMeasure) point := by
  have kernel := (cuspRotationProjection_kernel_contDiffOn cusp weight vector).of_le
    (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)
  have first : ContDiffOn ℝ 1 (fun pair : ℝ × BinaryRealMatrix => matrices pair.1)
      (domain ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) :=
    matrices_regular.comp contDiffOn_fst (fun _ pair_mem => pair_mem.1)
  have regular := kernel.comp (first.prodMk contDiffOn_snd)
    (fun pair pair_mem => ⟨invertible pair.1 pair_mem.1, pair_mem.2⟩)
  have derivative := binaryRotationAverage_hasFDerivAt
    (fun parameter second => binaryMatrixRotationCoordinate second ^ (-weight) •
      cusp.π (atInfinity (invertibleMatrix (matrices parameter * second))) vector.val)
    domain domain_open regular point member
  have equality : (fun parameter => cusp.π (atInfinity (invertibleMatrix (matrices parameter)))
      (cuspRotationProjection cusp weight vector.val)) =ᶠ[nhds point]
      (fun parameter => ∫ angle : Circle, binaryMatrixRotationCoordinate (binaryRotationMatrix angle) ^ (-weight) •
        cusp.π (atInfinity (invertibleMatrix (matrices parameter * binaryRotationMatrix angle))) vector.val ∂binaryRotationMeasure) := by
    filter_upwards [domain_open.mem_nhds member] with parameter parameter_mem
    exact cuspRotationProjection_full_orbit cusp weight vector.val (matrices parameter) (invertible parameter parameter_mem)
  simpa only [binaryMatrixRotationCoordinate_rotation] using derivative.congr_of_eventuallyEq equality

theorem cuspRotationProjection_affineSmooth (cusp : CuspidalRepresentation) (weight : ℤ) (vector : cusp.smooth) :
    cuspRotationProjection cusp weight vector.val ∈ cuspAffineSmoothValues cusp :=
  (cuspRotationProjection_full_contDiffOn cusp weight vector).comp binaryUpperSectionMatrix_contDiffOn
    binaryUpperSectionMatrix_invertible

end TernaryPeriodPolynomials.SphericalDetection.Helpers
