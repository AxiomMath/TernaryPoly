module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DetNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryMatrixDenomI (matrix : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (matrix 1 0 : ℂ) * Complex.I + (matrix 1 1 : ℂ)

def binaryMatrixPointI (matrix : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((matrix 0 0 : ℂ) * Complex.I + (matrix 0 1 : ℂ)) / binaryMatrixDenomI matrix

def binaryMatrixPhaseI (matrix : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  binaryMatrixDenomI matrix / (‖binaryMatrixDenomI matrix‖ : ℂ)

theorem binaryMatrixDenomI_one : binaryMatrixDenomI 1 = 1 := by simp [binaryMatrixDenomI]

theorem binaryMatrixPointI_one : binaryMatrixPointI 1 = Complex.I := by
  simp [binaryMatrixPointI, binaryMatrixDenomI_one]

theorem binaryMatrixPhaseI_one : binaryMatrixPhaseI 1 = 1 := by
  simp [binaryMatrixPhaseI, binaryMatrixDenomI_one]

theorem binaryMatrixPointI_coe (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) :
    binaryMatrixPointI matrix.val = ((matrix • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos positive, UpperHalfPlane.coe_I]
  rfl

theorem binaryMatrixPhaseI_coe (matrix : BinaryRealGL) :
    binaryMatrixPhaseI matrix.val = binaryPhaseValue matrix Complex.I := rfl

theorem binaryDetNormalizedMatrix_contDiffAt_one :
    ContDiffAt ℝ ⊤ binaryDetNormalizedMatrix 1 := by
  have determinant : ContDiffAt ℝ ⊤ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => matrix.det) 1 := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have root := determinant.sqrt (by simp)
  exact (root.inv (by simp)).smul contDiffAt_id

theorem binaryMatrixDenomI_contDiff : ContDiff ℝ ⊤ binaryMatrixDenomI := by
  have entries (row column : Fin 2) : ContDiff ℝ ⊤
      (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => (matrix row column : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (by fun_prop)
  exact ((entries 1 0).mul contDiff_const).add (entries 1 1)

theorem binaryMatrixPointI_contDiffAt_one : ContDiffAt ℝ ⊤ binaryMatrixPointI 1 := by
  have numerator : ContDiff ℝ ⊤
      (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => (matrix 0 0 : ℂ) * Complex.I + (matrix 0 1 : ℂ)) := by
    have entries (row column : Fin 2) : ContDiff ℝ ⊤
        (fun matrix : Matrix (Fin 2) (Fin 2) ℝ => (matrix row column : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (by fun_prop)
    exact ((entries 0 0).mul contDiff_const).add (entries 0 1)
  convert numerator.contDiffAt.mul (binaryMatrixDenomI_contDiff.contDiffAt.inv
    (by rw [binaryMatrixDenomI_one]; exact one_ne_zero)) using 1; rfl

theorem binaryMatrixPhaseI_contDiffAt_one : ContDiffAt ℝ ⊤ binaryMatrixPhaseI 1 := by
  have denominator := binaryMatrixDenomI_contDiff.contDiffAt (x := (1 : Matrix (Fin 2) (Fin 2) ℝ))
  have norm_regular := denominator.norm ℂ (by rw [binaryMatrixDenomI_one]; exact one_ne_zero)
  have complex_norm := Complex.ofRealCLM.contDiff.contDiffAt.comp 1 norm_regular
  convert denominator.mul (complex_norm.inv (by simp [binaryMatrixDenomI_one])) using 1; rfl

theorem cuspRotationWeight_positive_matrix_formula (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) (positive : 0 < matrix.det) :
    cusp.π (atInfinity (invertibleMatrix matrix)) vector =
      binaryMatrixPhaseI (binaryDetNormalizedMatrix matrix) ^ weight •
        cuspAffineOrbitVector cusp vector (binaryMatrixPointI (binaryDetNormalizedMatrix matrix)) := by
  have normalized_invertible : (binaryDetNormalizedMatrix matrix).det ≠ 0 := by
    rw [binaryDetNormalizedMatrix_det matrix positive]
    exact one_ne_zero
  have normalized_positive :
      (0 : ℝ) < (invertibleMatrix (binaryDetNormalizedMatrix matrix)).val.det := by
    rw [invertibleMatrix_val _ normalized_invertible, binaryDetNormalizedMatrix_det _ positive]
    norm_num
  have equality := cuspRotationWeight_positive_formula cusp spherical central_positive vector weight rotation
    (invertibleMatrix matrix) (by rw [invertibleMatrix_val _ (ne_of_gt positive)]; exact positive)
  simp only [invertibleMatrix_val matrix (ne_of_gt positive)] at equality
  rw [← binaryMatrixPhaseI_coe, ← binaryMatrixPointI_coe _ normalized_positive,
    invertibleMatrix_val _ normalized_invertible] at equality
  exact equality

theorem cuspRotationWeight_analyticAt_one (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (affine_analytic : AnalyticAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    AnalyticAt ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1 := by
  have point_analytic : AnalyticAt ℝ
      (fun matrix => binaryMatrixPointI (binaryDetNormalizedMatrix matrix)) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one] using binaryMatrixPointI_contDiffAt_one.analyticAt
    · exact binaryDetNormalizedMatrix_contDiffAt_one.analyticAt
  have phase_analytic : AnalyticAt ℝ
      (fun matrix => binaryMatrixPhaseI (binaryDetNormalizedMatrix matrix)) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one] using binaryMatrixPhaseI_contDiffAt_one.analyticAt
    · exact binaryDetNormalizedMatrix_contDiffAt_one.analyticAt
  have vector_analytic : AnalyticAt ℝ
      (fun matrix => cuspAffineOrbitVector cusp vector (binaryMatrixPointI (binaryDetNormalizedMatrix matrix))) 1 := by
    apply AnalyticAt.fun_comp
    · simpa only [binaryDetNormalizedMatrix_one, binaryMatrixPointI_one] using affine_analytic
    · exact point_analytic
  have analytic := (phase_analytic.zpow (n := weight)
    (by simp only [binaryDetNormalizedMatrix_one, binaryMatrixPhaseI_one, ne_eq, one_ne_zero, not_false_eq_true])).smul vector_analytic
  apply analytic.congr
  have domain_open : IsOpen {matrix : Matrix (Fin 2) (Fin 2) ℝ | 0 < matrix.det} :=
    isOpen_lt continuous_const continuous_id.matrix_det
  filter_upwards [domain_open.mem_nhds (show (0 : ℝ) < (1 : Matrix (Fin 2) (Fin 2) ℝ).det by simp)] with matrix positive
  exact (cuspRotationWeight_positive_matrix_formula cusp spherical central_positive vector weight rotation matrix positive).symm

theorem cuspUnitary_orbit_analytic_of_one (cusp : CuspidalRepresentation) (vector : cusp.H)
    (at_one : AnalyticAt ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1) :
    AnalyticOnNhd ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) {matrix | matrix.det ≠ 0} := by
  intro point invertible
  let matrix := invertibleMatrix point
  have at_point : matrix⁻¹.val * point = 1 := by
    calc
      _ = matrix⁻¹.val * matrix.val := by rw [invertibleMatrix_val point invertible]
      _ = 1 := matrix.inv_mul
  have multiplication : AnalyticAt ℝ (fun argument : Matrix (Fin 2) (Fin 2) ℝ => matrix⁻¹.val * argument) point := by
    have regular : ContDiff ℝ ⊤ (fun argument : Matrix (Fin 2) (Fin 2) ℝ => matrix⁻¹.val * argument) := by
      apply contDiff_pi.mpr
      intro row
      apply contDiff_pi.mpr
      intro column
      simp only [Matrix.mul_apply]
      fun_prop
    exact regular.contDiffAt.analyticAt
  have inner_analytic := (at_point.symm ▸ at_one).fun_comp multiplication
  have outer_analytic := (((cuspUnitaryOperator cusp (atInfinity matrix)).restrictScalars ℝ).analyticAt _).fun_comp inner_analytic
  apply outer_analytic.congr
  have domain_open : IsOpen {argument : Matrix (Fin 2) (Fin 2) ℝ | argument.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  filter_upwards [domain_open.mem_nhds invertible] with argument argument_invertible
  change cusp.π (atInfinity matrix)
      (cusp.π (atInfinity (invertibleMatrix (matrix⁻¹.val * argument))) vector) = _
  rw [invertibleMatrix_mul _ _ matrix⁻¹.det_ne_zero argument_invertible, invertibleMatrix_coe]
  change (cusp.π (atInfinity matrix) * cusp.π (atInfinity (matrix⁻¹ * invertibleMatrix argument))) vector = _
  rw [← map_mul, ← atInfinity_mul, ← mul_assoc, mul_inv_cancel, one_mul]

theorem cuspUnitary_orbit_smooth_of_one (cusp : CuspidalRepresentation) (vector : cusp.H)
    (at_one : AnalyticAt ℝ (fun matrix : Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1) :
    Smooth (fun point : Fin 1 → BinaryRealGL => cusp.π (atInfinity (point 0)) vector) := by
  have domain_open : IsOpen {matrix : Matrix (Fin 2) (Fin 2) ℝ | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have regular := (cuspUnitary_orbit_analytic_of_one cusp vector at_one).contDiffOn (n := ⊤) domain_open.uniqueDiffOn
  exact regular.comp (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) 0).contDiffOn
    (fun _ member => member 0)

theorem cuspSphericalWeight_smooth_of_affine_analytic (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (fixed : vector ∈ cuspSphericalValues cusp)
    (affine_analytic : AnalyticAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact vector).mpr
  refine ⟨cuspUnitary_orbit_smooth_of_one cusp vector
    (cuspRotationWeight_analyticAt_one cusp spherical central_positive vector weight rotation affine_analytic),
    finiteIntegralGLLevel 2, finiteIntegralGLLevel_isOpen 2, finiteIntegralGLLevel_isCompact 2, ?_⟩
  intro element
  obtain ⟨original, equality⟩ := element.property
  rw [← equality]
  exact fixed original

theorem cuspSphericalWeight_smooth_of_raising_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (halfWeight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ (2 * halfWeight) • vector)
    (fixed : vector ∈ cuspSphericalValues cusp)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    vector ∈ cusp.smooth := by
  apply cuspSphericalWeight_smooth_of_affine_analytic cusp spherical central_positive vector (2 * halfWeight) rotation fixed
  exact cuspAffineOrbitVector_analytic_of_raising_zero cusp halfWeight vector regular raising_zero Complex.I (by simp)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
