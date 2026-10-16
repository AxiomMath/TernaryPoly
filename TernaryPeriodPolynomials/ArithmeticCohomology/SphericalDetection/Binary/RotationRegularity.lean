module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.NormalizedCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SmoothIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Topology

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

abbrev BinaryRealMatrix := Matrix (Fin 2) (Fin 2) ℝ

def binaryRotationMatrix (angle : Circle) : BinaryRealMatrix := (binaryRotations angle).val

theorem binaryRotationMatrix_continuous : Continuous binaryRotationMatrix :=
  Units.continuous_val.comp binaryRotations_continuous

theorem binaryRotationMatrix_det (angle : Circle) : (binaryRotationMatrix angle).det = 1 := by
  have norm := Circle.normSq_coe angle
  simpa [Complex.normSq_apply, binaryRotationMatrix, binaryRotations, binaryRotation,
    Matrix.det_fin_two] using norm

theorem binaryRotationMatrix_norm_le (angle : Circle) : ‖binaryRotationMatrix angle‖ ≤ 1 := by
  have norm_one : ‖(angle : ℂ)‖ = 1 := by
    have member := angle.property
    change dist (angle : ℂ) 0 = 1 at member
    simpa only [dist_zero_right] using member
  have real_bound : |(angle : ℂ).re| ≤ 1 := by simpa only [norm_one] using Complex.abs_re_le_norm (angle : ℂ)
  have imaginary_bound : |(angle : ℂ).im| ≤ 1 := by simpa only [norm_one] using Complex.abs_im_le_norm (angle : ℂ)
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro row
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro column
  fin_cases row <;> fin_cases column <;>
    simp [binaryRotationMatrix, binaryRotations, binaryRotation, real_bound, imaginary_bound]

def binaryMatrixBump : ContDiffBump (0 : BinaryRealMatrix) := ⟨2, 3, by norm_num, by norm_num⟩

def binaryDeterminantBump : ContDiffBump (1 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

def binaryRotationCutoff (matrix : BinaryRealMatrix) : ℝ :=
  binaryMatrixBump matrix * binaryDeterminantBump matrix.det

theorem binaryRotationCutoff_contDiff {order : ℕ∞} :
    ContDiff ℝ order binaryRotationCutoff := by
  have determinant : ContDiff ℝ order (fun matrix : BinaryRealMatrix => matrix.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  exact binaryMatrixBump.contDiff.mul (binaryDeterminantBump.contDiff.comp determinant)

theorem binaryRotationCutoff_rotation (angle : Circle) :
    binaryRotationCutoff (binaryRotationMatrix angle) = 1 := by
  have matrix_one : binaryMatrixBump (binaryRotationMatrix angle) = 1 := by
    apply binaryMatrixBump.one_of_mem_closedBall
    change dist (binaryRotationMatrix angle) 0 ≤ 2
    rw [dist_zero_right]
    exact (binaryRotationMatrix_norm_le angle).trans (by norm_num)
  have determinant_one : binaryDeterminantBump (1 : ℝ) = 1 := by
    apply binaryDeterminantBump.one_of_mem_closedBall
    simp [binaryDeterminantBump]
  simp only [binaryRotationCutoff, matrix_one, binaryRotationMatrix_det, determinant_one, mul_one]

theorem binaryRotationCutoff_eventually_zero (matrix : BinaryRealMatrix) (singular : matrix.det = 0) :
    binaryRotationCutoff =ᶠ[𝓝 matrix] 0 := by
  have nearby : ∀ᶠ argument : BinaryRealMatrix in 𝓝 matrix,
      (1/2 : ℝ) < dist argument.det 1 := by
    apply (isOpen_lt continuous_const (continuous_id.matrix_det.dist continuous_const)).mem_nhds
    simpa [singular] using (show (1/2 : ℝ) < 1 by norm_num)
  filter_upwards [nearby] with argument outside
  change binaryMatrixBump argument * binaryDeterminantBump argument.det = 0
  rw [binaryDeterminantBump.zero_of_le_dist outside.le, mul_zero]

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
local instance : MeasurableSpace BinaryRealMatrix := borel BinaryRealMatrix
local instance : BorelSpace BinaryRealMatrix := ⟨rfl⟩

local instance : SecondCountableTopology BinaryRealMatrix := by
  change SecondCountableTopology (Fin 2 → Fin 2 → ℝ)
  infer_instance

theorem binaryRotationAverage_contDiffOn
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {order : ℕ∞}
    {domain : Set P} (domain_open : IsOpen domain) (values : P → BinaryRealMatrix → E)
    (regular : ContDiffOn ℝ order (Function.uncurry values)
      (domain ×ˢ {matrix | matrix.det ≠ 0})) :
    ContDiffOn ℝ order (fun parameter => ∫ angle, values parameter (binaryRotationMatrix angle)
      ∂binaryRotationMeasure) domain := by
  let cut : P → BinaryRealMatrix → E := fun parameter matrix =>
    binaryRotationCutoff matrix • values parameter matrix
  have matrix_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have cut_regular : ContDiffOn ℝ order (Function.uncurry cut) (domain ×ˢ Set.univ) := by
    intro point member
    by_cases invertible : point.2.det ≠ 0
    · have at_point := regular.contDiffAt ((domain_open.prod matrix_open).mem_nhds ⟨member.1, invertible⟩)
      exact ((binaryRotationCutoff_contDiff.comp contDiff_snd).contDiffAt.smul at_point).contDiffWithinAt
    · have zero_nearby := (binaryRotationCutoff_eventually_zero point.2 (not_ne_iff.mp invertible)).comp_tendsto
        continuous_snd.continuousAt
      apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [zero_nearby] with argument zero
      change binaryRotationCutoff argument.2 = 0 at zero
      change binaryRotationCutoff argument.2 • values argument.1 argument.2 = 0
      rw [zero, zero_smul]
  let measure := Measure.map binaryRotationMatrix binaryRotationMeasure
  have integral_regular := @contDiffOn_integral_compact_support P BinaryRealMatrix E
    _ _ _ _ instMeasurableSpaceBinaryRealMatrix ⟨rfl⟩ _ _ measure _ order cut domain
    (tsupport (binaryMatrixBump : BinaryRealMatrix → ℝ))
    domain_open binaryMatrixBump.hasCompactSupport
    (by
      intro parameter matrix _ outside
      change (binaryMatrixBump matrix * binaryDeterminantBump matrix.det) • values parameter matrix = 0
      rw [image_eq_zero_of_notMem_tsupport outside, zero_mul, zero_smul]) cut_regular
  apply integral_regular.congr
  intro parameter member
  have cut_continuous : Continuous (cut parameter) :=
    cut_regular.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨member, Set.mem_univ _⟩)
  rw [MeasureTheory.integral_map binaryRotationMatrix_continuous.measurable.aemeasurable
    cut_continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with angle
  change values parameter (binaryRotationMatrix angle) =
    binaryRotationCutoff (binaryRotationMatrix angle) • values parameter (binaryRotationMatrix angle)
  rw [binaryRotationCutoff_rotation, one_smul]

theorem binaryRotationAverage_right_contDiffOn {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {order : ℕ∞}
    (values : BinaryRealGL → E)
    (regular : ContDiffOn ℝ order (fun matrix : BinaryRealMatrix => values (invertibleMatrix matrix))
      {matrix | matrix.det ≠ 0}) :
    ContDiffOn ℝ order
      (fun matrix : BinaryRealMatrix => ∫ angle,
        values (invertibleMatrix matrix * binaryRotations angle) ∂binaryRotationMeasure)
      {matrix | matrix.det ≠ 0} := by
  have matrix_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have multiplication : ContDiff ℝ order
      (fun point : BinaryRealMatrix × BinaryRealMatrix => point.1 * point.2) := by
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have product_regular := regular.comp multiplication.contDiffOn (s :=
    {matrix : BinaryRealMatrix | matrix.det ≠ 0} ×ˢ {matrix : BinaryRealMatrix | matrix.det ≠ 0}) (by
      intro point member
      change (point.1 * point.2).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero member.1 member.2)
  have average_regular := binaryRotationAverage_contDiffOn matrix_open
    (fun first second => values (invertibleMatrix (first * second))) product_regular
  apply average_regular.congr
  intro matrix invertible
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [invertibleMatrix_mul _ _ invertible (by rw [binaryRotationMatrix_det]; norm_num)]
  rw [binaryRotationMatrix, invertibleMatrix_coe]

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binaryRotationNormalizedCycle_average (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)))
    (matrix : BinaryRealGL) :
    binaryRotationNormalizedCycle cusp basis cycle matrix =
      (∫ angle, binaryHilbertEmbedding cusp basis (cycle (matrix * binaryRotations angle))
        ∂binaryRotationMeasure) -
      ∫ angle, binaryHilbertEmbedding cusp basis (cycle (binaryRotations angle))
        ∂binaryRotationMeasure := by
  have integrable : Integrable
      (fun angle => binaryHilbertEmbedding cusp basis (cycle (binaryRotations angle))) binaryRotationMeasure :=
    (continuous.comp binaryRotations_continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have operator_integrable := (binaryHilbertOperator cusp basis matrix).integrable_comp integrable
  simp_rw [binaryHilbertCocycle_identity]
  rw [integral_add (integrable_const _) operator_integrable,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    (binaryHilbertOperator cusp basis matrix).integral_comp_comm integrable]
  simp only [binaryRotationNormalizedCycle, binaryRotationPrimitive, map_neg]
  abel

theorem binaryRotationNormalizedCycle_contDiffOn (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (regular : Smooth (fun point : Fin 1 → BinaryRealGL =>
      binaryHilbertEmbedding cusp basis (cycle (point 0)))) {order : ℕ∞} :
    ContDiffOn ℝ order (fun matrix : BinaryRealMatrix =>
      binaryRotationNormalizedCycle cusp basis cycle (invertibleMatrix matrix))
      {matrix | matrix.det ≠ 0} := by
  have chart_regular := smooth_one_contDiffOn
    (function := fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) regular
  have cycle_regular := chart_regular.of_le (show (order : WithTop ℕ∞) ≤ ⊤ from le_top)
  have cycle_continuous : Continuous (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) :=
    realGL_continuous_of_contDiffOn chart_regular
  have averaged := binaryRotationAverage_right_contDiffOn
    (fun matrix => binaryHilbertEmbedding cusp basis (cycle matrix)) cycle_regular
  apply (averaged.sub contDiffOn_const).congr
  intro matrix _
  exact binaryRotationNormalizedCycle_average cusp basis cycle cycle_continuous (invertibleMatrix matrix)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
