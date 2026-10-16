module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Normal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CocycleLocalRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.IntervalIntegral

@[expose] public section


/-!
# Real analyticity of the Hilbert Eichler period and smoothness of the binary correction

The Hilbert-space Eichler period `binaryEndpointPeriod` of a smooth vector is a real-analytic
function of its endpoint on the upper half plane, and `A ↦ A · i` is real analytic on the
invertible real matrices. Consequently the Hilbert normal form
`½ (Per(A·i) + J Per(-conj(A·i)))` is a smooth function of `A`. If a binary cocycle with
analytic Hilbert embedding is reconstructed as this normal form plus the coboundary of a
finite-level correction, then every coordinate of the correction is a smooth vector.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

section IntervalIntegral

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

/-- **Analyticity of parametric integrals over the unit interval.** Only analyticity at the
parameters of the interval of integration and continuity on that interval are required. -/
theorem analyticAt_intervalIntegral_unit (function : P × ℝ → F) (point : P) (domain : Set P)
    (domain_open : IsOpen domain) (point_mem : point ∈ domain)
    (continuous : ∀ parameter ∈ domain,
      ContinuousOn (fun sample => function (parameter, sample)) (Icc 0 1))
    (analytic : ∀ center ∈ Icc (0 : ℝ) 1, AnalyticAt ℝ function (point, center)) :
    AnalyticAt ℝ (fun parameter => ∫ sample in (0 : ℝ)..1, function (parameter, sample)) point := by
  let property (endpoint : ℝ) :=
    AnalyticAt ℝ (fun parameter => ∫ sample in (0 : ℝ)..endpoint, function (parameter, sample))
      point
  have integrable (parameter : P) (member : parameter ∈ domain) (left right : ℝ)
      (left_mem : left ∈ Icc (0 : ℝ) 1) (right_mem : right ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun sample => function (parameter, sample)) volume left right :=
    ((continuous parameter member).mono
      (uIcc_subset_Icc left_mem right_mem)).intervalIntegrable
  have local_equivalence (center : ℝ) (center_mem : center ∈ Icc (0 : ℝ) 1) :
      ∀ᶠ endpoint in nhdsWithin center (Icc 0 1),
        (property center ↔ property endpoint) ∧ (property endpoint ↔ property center) := by
    have nearby := analyticAt_intervalIntegral_nearby function point center
      (analytic center center_mem)
    filter_upwards [nhdsWithin_le_nhds nearby, self_mem_nhdsWithin] with endpoint increment
      endpoint_mem
    have addition : ∀ᶠ parameter in nhds point,
        (∫ sample in (0 : ℝ)..center, function (parameter, sample)) +
          (∫ sample in center..endpoint, function (parameter, sample)) =
            ∫ sample in (0 : ℝ)..endpoint, function (parameter, sample) := by
      filter_upwards [domain_open.mem_nhds point_mem] with parameter member
      exact intervalIntegral.integral_add_adjacent_intervals
        (integrable parameter member 0 center ⟨le_rfl, zero_le_one⟩ center_mem)
        (integrable parameter member center endpoint center_mem endpoint_mem)
    have forward : property center → property endpoint := fun center_analytic =>
      (center_analytic.add increment).congr addition
    have backward : property endpoint → property center := by
      intro endpoint_analytic
      apply (endpoint_analytic.sub increment).congr
      filter_upwards [addition] with parameter equality
      exact (eq_sub_iff_add_eq.mpr equality).symm
    exact ⟨⟨forward, backward⟩, ⟨backward, forward⟩⟩
  have chain := isPreconnected_Icc.induction₂'
    (fun first second => property first ↔ property second)
    local_equivalence (fun _ _ _ _ _ _ first second => first.trans second)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
  apply chain.mp
  change AnalyticAt ℝ (fun parameter => ∫ sample in (0 : ℝ)..0, function (parameter, sample))
    point
  simpa only [intervalIntegral.integral_same] using
    (analyticAt_const (𝕜 := ℝ) (v := (0 : F)) (x := point))

end IntervalIntegral

/-! ### The Hilbert Eichler period is real analytic -/

theorem straightPath_mem (point : ℂ) (positive : 0 < point.im) {parameter : ℝ}
    (member : parameter ∈ Icc (0 : ℝ) 1) :
    Complex.I + parameter • (point - Complex.I) ∈ UpperHalfPlane.upperHalfPlaneSet :=
  upperHalfPlane_straightPath ⟨point, positive⟩ member

theorem affineOrbit_analyticAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (cuspAffineOrbitVector cusp vector.val) point := by
  have smooth := ((cusp.smooth_exact vector.val).mp vector.property).1
  have group_regular := smooth_one_contDiffOn
    (function := fun matrix => cusp.π (atInfinity matrix) vector.val) smooth
  have affine_regular : ContDiffOn ℝ ⊤ (cuspAffineOrbitVector cusp vector.val)
      UpperHalfPlane.upperHalfPlaneSet :=
    group_regular.comp binaryUpperSectionMatrix_contDiffOn binaryUpperSectionMatrix_invertible
  exact (affine_regular.contDiffAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).analyticAt

theorem endpointForm_analyticAt (cusp : CuspidalRepresentation) (degree : ℕ) (halfWeight : ℤ)
    (vector : cusp.smooth) {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (binaryEndpointHolomorphicForm cusp degree halfWeight vector.val) point := by
  apply analyticAt_pi_iff.mpr
  intro position
  have scalar : AnalyticAt ℝ (fun argument : ℂ => (binaryWeightBasis (degree + 1)).coord position
      (binaryPointPower (degree + 1) argument)) point :=
    (binaryPointPower_functional_analytic (degree + 1)
      ((binaryWeightBasis (degree + 1)).coord position) point).restrictScalars
  have weight : AnalyticAt ℝ (fun argument : ℂ => argument.im ^ halfWeight) point :=
    (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  exact scalar.smul (weight.smul (affineOrbit_analyticAt cusp vector positive))

/-- **The Hilbert Eichler period is real analytic in its endpoint.** -/
theorem endpointPeriod_analyticAt (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (vector : cusp.smooth) {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (binaryEndpointPeriod cusp degree halfWeight vector.val) point := by
  let path : ℂ × ℝ → ℂ := fun parameter => Complex.I + parameter.2 • (parameter.1 - Complex.I)
  let integrand : ℂ × ℝ → (Fin (degree + 2) → cusp.H) := fun parameter =>
    (parameter.1 - Complex.I) • binaryEndpointHolomorphicForm cusp degree halfWeight vector.val
      (path parameter)
  have path_analytic (parameter : ℂ × ℝ) : AnalyticAt ℝ path parameter :=
    analyticAt_const.add (analyticAt_snd.smul (analyticAt_fst.sub analyticAt_const))
  have integrand_analytic (center : ℝ) (member : center ∈ Icc (0 : ℝ) 1) :
      AnalyticAt ℝ integrand (point, center) := by
    have form_analytic : AnalyticAt ℝ
        (fun parameter => binaryEndpointHolomorphicForm cusp degree halfWeight vector.val
          (path parameter)) (point, center) :=
      AnalyticAt.comp (f := path) (x := (point, center)) (endpointForm_analyticAt cusp degree
        halfWeight vector (straightPath_mem point positive member)) (path_analytic (point, center))
    exact (analyticAt_fst.sub analyticAt_const).smul form_analytic
  exact analyticAt_intervalIntegral_unit integrand point
    UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.isOpen_upperHalfPlaneSet positive
    (fun parameter member => by
      have path_continuous : Continuous (fun sample : ℝ => path (parameter, sample)) := by
        fun_prop
      exact (continuousOn_const (c := parameter - Complex.I)).smul
        ((binaryEndpointHolomorphicForm_continuousOn cusp degree halfWeight vector.val).comp
          path_continuous.continuousOn (fun _ inside => straightPath_mem parameter member inside)))
    integrand_analytic

theorem endpointPeriod_contDiffOn (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (vector : cusp.smooth) :
    ContDiffOn ℝ ⊤ (binaryEndpointPeriod cusp degree halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet := fun _ positive =>
  (endpointPeriod_analyticAt cusp degree halfWeight vector positive).contDiffAt.contDiffWithinAt

/-! ### The base point `A · i` is real analytic in `A` -/

theorem basePoint_re (A : BinaryRealGL) : (basePoint A).re =
    (A.val 0 0 * A.val 1 0 + A.val 0 1 * A.val 1 1) / (A.val 1 0 ^ 2 + A.val 1 1 ^ 2) := by
  have formula := UpperHalfPlane.re_smul A UpperHalfPlane.I
  simp only [basePoint, UpperHalfPlane.coe_re] at formula ⊢
  rw [formula]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, Complex.div_re, Complex.normSq_apply]
  ring

theorem basePoint_im (A : BinaryRealGL) : (basePoint A).im =
    |A.val.det| / (A.val 1 0 ^ 2 + A.val 1 1 ^ 2) := by
  have formula := UpperHalfPlane.im_smul_eq_div_normSq A UpperHalfPlane.I
  simp only [basePoint, UpperHalfPlane.coe_im] at formula ⊢
  rw [formula]
  simp [UpperHalfPlane.denom, Complex.normSq_apply, Matrix.GeneralLinearGroup.val_det_apply]
  ring

theorem basePoint_im_pos (A : BinaryRealGL) : 0 < (basePoint A).im :=
  (A • UpperHalfPlane.I).im_pos

theorem lowerRow_ne_zero (M : Matrix (Fin 2) (Fin 2) ℝ) (invertible : M.det ≠ 0) :
    M 1 0 ^ 2 + M 1 1 ^ 2 ≠ 0 := by
  intro vanish
  have first : M 1 0 = 0 := by nlinarith [sq_nonneg (M 1 0), sq_nonneg (M 1 1)]
  have second : M 1 1 = 0 := by nlinarith [sq_nonneg (M 1 0), sq_nonneg (M 1 1)]
  apply invertible
  rw [Matrix.det_fin_two, first, second]
  ring

theorem abs_det_contDiffOn :
    ContDiffOn ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ => |M.det|) {M | M.det ≠ 0} := by
  have determinant : ContDiff ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ => M.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  intro M member
  apply ContDiffAt.contDiffWithinAt
  rcases lt_or_gt_of_ne member with negative | positive
  · apply determinant.contDiffAt.neg.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt determinant.continuous continuous_const).mem_nhds negative]
      with N inside
    exact abs_of_neg inside
  · apply determinant.contDiffAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const determinant.continuous).mem_nhds positive]
      with N inside
    exact abs_of_pos inside

/-- **The base point `A · i` is a real-analytic function of the matrix `A`.** -/
theorem basePoint_contDiffOn :
    ContDiffOn ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ => basePoint (invertibleMatrix M))
      {M | M.det ≠ 0} := by
  have denominator : ContDiffOn ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0 ^ 2 + M 1 1 ^ 2)
      {M | M.det ≠ 0} := by fun_prop
  have real_part : ContDiffOn ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      (M 0 0 * M 1 0 + M 0 1 * M 1 1) / (M 1 0 ^ 2 + M 1 1 ^ 2)) {M | M.det ≠ 0} :=
    ContDiffOn.div (by fun_prop) denominator lowerRow_ne_zero
  have imaginary_part : ContDiffOn ℝ ⊤ (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      |M.det| / (M 1 0 ^ 2 + M 1 1 ^ 2)) {M | M.det ≠ 0} :=
    abs_det_contDiffOn.div denominator lowerRow_ne_zero
  have combined := (Complex.ofRealCLM.contDiff.comp_contDiffOn real_part).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn imaginary_part).mul
      (contDiffOn_const (c := Complex.I)))
  apply combined.congr
  intro M member
  have value := invertibleMatrix_val M member
  apply Complex.ext
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, basePoint_re, value]
    ring
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, basePoint_im, value]
    ring

/-! ### The Hilbert normal form and the smoothness of the correction -/

/-- **The Hilbert normal form** `½ (Per(A·i) + J Per(-conj(A·i)))`. -/
def hilbertNormal (cusp : CuspidalRepresentation) (degree : ℕ) (halfWeight : ℤ)
    (vector : cusp.H) (A : BinaryRealGL) : Fin (degree + 2) → cusp.H :=
  (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp degree halfWeight vector (basePoint A) +
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
      (binaryEndpointPeriod cusp degree halfWeight vector
        (binaryComplexReflection (basePoint A))))

/-- **The Hilbert normal form is smooth.** -/
theorem hilbertNormal_smooth (cusp : CuspidalRepresentation) (degree : ℕ) (halfWeight : ℤ)
    (vector : cusp.smooth) :
    Smooth (fun point : Fin 1 → BinaryRealGL =>
      hilbertNormal cusp degree halfWeight vector.val (point 0)) := by
  have period := endpointPeriod_contDiffOn cusp degree halfWeight vector
  have base : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      basePoint (invertibleMatrix (point 0))) {point | ∀ position, (point position).det ≠ 0} :=
    basePoint_contDiffOn.comp (contDiff_apply ℝ (Matrix (Fin 2) (Fin 2) ℝ) (0 : Fin 1)).contDiffOn
      (fun _ member => member 0)
  have reflected : ContDiffOn ℝ ⊤ (fun point : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      binaryComplexReflection (basePoint (invertibleMatrix (point 0))))
      {point | ∀ position, (point position).det ≠ 0} :=
    binaryComplexReflection.contDiff.comp_contDiffOn base
  have first := period.comp base (fun point _ => basePoint_im_pos (invertibleMatrix (point 0)))
  have second := period.comp reflected (fun point _ => by
    change 0 < (binaryComplexReflection (basePoint (invertibleMatrix (point 0)))).im
    rw [binaryComplexReflection_im]
    exact basePoint_im_pos _)
  have third := ((binaryHilbertOperator cusp (binaryWeightBasis (degree + 1))
    UpperHalfPlane.J).restrictScalars ℝ).contDiff.comp_contDiffOn second
  exact (first.add third).const_smul (2 : ℂ)⁻¹

/-- **Smoothness of the binary correction.** If the Hilbert embedding of a binary cocycle with
analytic Hilbert embedding at `1` equals the Hilbert normal form of a smooth vector plus the
coboundary of a finite-level correction, then each coordinate of the correction is smooth. -/
theorem correction_smooth (cusp : CuspidalRepresentation) {degree : ℕ} (halfWeight : ℤ)
    (vector : cusp.smooth)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree))
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1))
        (original (invertibleMatrix matrix))) 1)
    (correction : Fin (degree + 2) → cusp.H) (level : Subgroup BinaryFiniteGL)
    (level_open : IsOpen (level : Set BinaryFiniteGL))
    (level_compact : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ element : level, ∀ position,
      cusp.π (atFinite element.val) (correction position) = correction position)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (degree + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp degree halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp degree halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) A correction -
          correction))
    (position : Fin (degree + 2)) : correction position ∈ cusp.smooth := by
  let basis := binaryWeightBasis (degree + 1)
  let cycle : BinaryRealGL → (Fin (degree + 2) → cusp.H) := fun A =>
    binaryHilbertOperator cusp basis A correction - correction
  have embedding := binaryHilbertCocycle_smooth_of_analyticAt_one cusp basis original analytic
  have normal := hilbertNormal_smooth cusp degree halfWeight vector
  have regular : Smooth (fun point : Fin 1 → BinaryRealGL => cycle (point 0)) := by
    have equality : (fun point : Fin 1 → BinaryRealGL => cycle (point 0)) =
        fun point => binaryHilbertEmbedding cusp basis (original (point 0)) -
          hilbertNormal cusp degree halfWeight vector.val (point 0) := by
      funext point
      exact eq_sub_of_add_eq' (reconstruction (point 0)).symm
    rw [equality]
    exact ContDiffOn.sub embedding normal
  have smooth := binaryHilbertPrimitive_smooth cusp basis cycle regular correction (fun _ => rfl)
  apply (cusp.smooth_exact (correction position)).mpr
  refine ⟨contDiffOn_pi.mp smooth position, level, level_open, level_compact, ?_⟩
  intro element
  exact fixed element position

end TernaryPeriodPolynomials.AnalyticClasses
