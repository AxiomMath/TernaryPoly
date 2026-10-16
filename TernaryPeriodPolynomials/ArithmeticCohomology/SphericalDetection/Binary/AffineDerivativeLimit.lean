module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RaisingGraphApproximation
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeExtremalReduction
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspAffineDerivativeTranslate (cusp : CuspidalRepresentation) (point : ℂ)
    (derivative : ℂ →L[ℝ] cusp.H) : ℂ →L[ℝ] cusp.H :=
  point.im⁻¹ • ((cuspUnitaryOperator cusp (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))).restrictScalars ℝ).comp derivative

theorem cuspAffineDerivativeTranslate_sub (cusp : CuspidalRepresentation) (point : ℂ)
    (first second : ℂ →L[ℝ] cusp.H) :
    cuspAffineDerivativeTranslate cusp point (first - second) =
      cuspAffineDerivativeTranslate cusp point first - cuspAffineDerivativeTranslate cusp point second := by
  simp only [cuspAffineDerivativeTranslate, ContinuousLinearMap.comp_sub, smul_sub]

theorem cuspAffineDerivativeTranslate_bound (cusp : CuspidalRepresentation) (point : ℂ)
    (derivative : ℂ →L[ℝ] cusp.H) :
    ‖cuspAffineDerivativeTranslate cusp point derivative‖ ≤ ‖point.im⁻¹‖ * ‖derivative‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro direction
  change ‖point.im⁻¹ • cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) (derivative direction)‖ ≤ _
  rw [norm_smul, cusp.unitary, mul_assoc]
  exact mul_le_mul_of_nonneg_left (derivative.le_opNorm direction) (norm_nonneg _)

theorem cuspAffineOrbitVector_fderiv_translate (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : ℂ) (positive : 0 < point.im) :
    fderiv ℝ (cuspAffineOrbitVector cusp vector) point =
      cuspAffineDerivativeTranslate cusp point (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I) := by
  ext direction
  have identity := cuspAffineOrbitVector_derivative_translate cusp vector regular ⟨point, positive⟩ direction
  change cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))
      (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) =
    point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) point direction at identity
  change _ = point.im⁻¹ • cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))
    (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction)
  rw [identity, inv_smul_smul₀ (ne_of_gt positive)]

theorem cuspAffineDerivativeTranslate_I (cusp : CuspidalRepresentation) (derivative : ℂ →L[ℝ] cusp.H) :
    cuspAffineDerivativeTranslate cusp Complex.I derivative = derivative := by
  ext direction
  change Complex.I.im⁻¹ • cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix Complex.I))) (derivative direction) = _
  rw [Complex.I_im, inv_one, one_smul, binaryAffineSection_I, atInfinity_one, map_one, Module.End.one_apply]

theorem cuspAffineOrbitVector_hasFDerivAt_of_limit (cusp : CuspidalRepresentation)
    (sequence : ℕ → cuspAffineSmoothValues cusp) (vector : cusp.H) (derivative : ℂ →L[ℝ] cusp.H)
    (vector_limit : Tendsto (fun index => (sequence index).val) atTop (nhds vector))
    (derivative_limit : Tendsto (fun index => fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I)
      atTop (nhds derivative)) (point : ℂ) (positive : 0 < point.im) :
    HasFDerivAt (cuspAffineOrbitVector cusp vector) (cuspAffineDerivativeTranslate cusp point derivative) point := by
  let cutoff := point.im / 2
  let domain : Set ℂ := {argument | cutoff < argument.im}
  have cutoff_positive : 0 < cutoff := half_pos positive
  have bound_positive : 0 < cutoff⁻¹ := inv_pos.mpr cutoff_positive
  have domain_open : IsOpen domain := isOpen_lt continuous_const Complex.continuous_im
  have domain_positive {argument : ℂ} (member : argument ∈ domain) : 0 < argument.im := cutoff_positive.trans member
  have uniform : TendstoUniformlyOn
      (fun index argument => cuspAffineDerivativeTranslate cusp argument
        (fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I))
      (fun argument => cuspAffineDerivativeTranslate cusp argument derivative) atTop domain := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon epsilon_positive
    have limit : Tendsto (fun index => ‖derivative - fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I‖)
        atTop (nhds 0) := by
      have constant : Tendsto (fun _ : ℕ => derivative) atTop (nhds derivative) := tendsto_const_nhds
      simpa only [sub_self, norm_zero] using (constant.sub derivative_limit).norm
    filter_upwards [limit.eventually (gt_mem_nhds (div_pos epsilon_positive bound_positive))] with index small
    intro argument member
    have inverse_bound : ‖argument.im⁻¹‖ ≤ cutoff⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (domain_positive member))]
      simpa only [one_div] using one_div_le_one_div_of_le cutoff_positive member.le
    rw [dist_eq_norm, ← cuspAffineDerivativeTranslate_sub]
    calc
      _ ≤ ‖argument.im⁻¹‖ * ‖derivative - fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I‖ :=
        cuspAffineDerivativeTranslate_bound cusp argument _
      _ ≤ cutoff⁻¹ * ‖derivative - fderiv ℝ (cuspAffineOrbitVector cusp (sequence index).val) Complex.I‖ :=
        mul_le_mul_of_nonneg_right inverse_bound (norm_nonneg _)
      _ < cutoff⁻¹ * (epsilon / cutoff⁻¹) := mul_lt_mul_of_pos_left small bound_positive
      _ = epsilon := mul_div_cancel₀ _ (ne_of_gt bound_positive)
  apply hasFDerivAt_of_tendstoUniformlyOn domain_open uniform
  · intro index argument member
    have regular := (sequence index).property.differentiableOn (by simp)
    rw [← cuspAffineOrbitVector_fderiv_translate cusp (sequence index).val regular argument (domain_positive member)]
    exact (regular.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (domain_positive member))).hasFDerivAt
  · intro argument _
    exact ((cuspUnitaryOperator cusp (atInfinity (invertibleMatrix (binaryUpperSectionMatrix argument)))).continuous.tendsto vector).comp
      vector_limit
  · change point.im / 2 < point.im
    linarith

theorem cuspFiniteRaisingPMap_closure_differentiable (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (nonnegative : 0 ≤ weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector.val) UpperHalfPlane.upperHalfPlaneSet ∧
      cuspRaisingVector cusp weight vector.val = ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H) := by
  obtain ⟨sequence, derivative, _, vector_limit, derivative_limit, raising_eq⟩ :=
    cuspRaising_graph_approximation_fderiv cusp spherical level weight nonnegative vector
  have derivative_at := cuspAffineOrbitVector_hasFDerivAt_of_limit cusp sequence vector.val derivative vector_limit derivative_limit
  constructor
  · intro point positive
    exact (derivative_at point positive).differentiableAt.differentiableWithinAt
  · have basepoint := (derivative_at Complex.I (by simp)).fderiv
    rw [cuspAffineDerivativeTranslate_I] at basepoint
    rw [cuspRaisingVector, basepoint]
    exact raising_eq

theorem cohomological_extremal_or_analytic_obstruction (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ level : Subgroup BinaryFiniteGL,
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      ((∃ vector : cuspAffineSmoothValues cusp, vector ≠ 0 ∧
          vector ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
          cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) vector = 0) ∨
        (∃ vector : cusp.H, vector ≠ 0 ∧ vector ∈ cuspHilbertWeightValues cusp level ((degree + 1 : ℕ) + 2) ∧
          ∀ smooth : cuspAffineSmoothValues cusp, smooth ∈ cuspFiniteWeightValues cusp level (degree + 1 : ℕ) →
            inner ℂ vector (cuspRaisingOperator cusp (degree + 1 : ℕ) smooth).val = 0) ∨
        ∃ vector : cusp.H, vector ∈ cuspHilbertWeightValues cusp level (degree + 1 : ℕ) ∧
          DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet ∧
          vector ∉ cuspAffineSmoothValues cusp ∧
          cuspRaisingVector cusp (degree + 1 : ℕ) vector ∈ cuspAffineSmoothValues cusp) := by
  obtain ⟨level, level_open, level_compact, alternatives⟩ :=
    cohomological_extremal_or_raising_obstruction cusp spherical cohomological
  refine ⟨level, level_open, level_compact, ?_⟩
  rcases alternatives with extremal | ⟨vector, member, no_smooth_preimage⟩
  · exact Or.inl extremal
  · right
    have positive : (0 : ℤ) < (degree + 1 : ℕ) := by omega
    have vector_weight : vector.val ∈ cuspHilbertWeightValues cusp level ((degree + 1 : ℕ) + 2) := by
      have hilbert_member : vector.val ∈ cuspHilbertWeightValues cusp level (2 + (degree + 1 : ℕ)) := member
      simpa only [add_comm] using hilbert_member
    by_cases in_range : vector.val ∈ (cuspFiniteRaisingPMap cusp level (degree + 1 : ℕ)).closure.toFun.range
    · right
      obtain ⟨preimage, image_eq⟩ := in_range
      change ((cuspFiniteRaisingPMap cusp level (degree + 1 : ℕ)).closure preimage : cusp.H) = vector.val at image_eq
      have weights := cuspFiniteRaisingPMap_closure_weights cusp spherical level (degree + 1 : ℕ) preimage
      have actual := cuspFiniteRaisingPMap_closure_differentiable cusp spherical level (degree + 1 : ℕ) positive.le preimage
      have raised : cuspRaisingVector cusp (degree + 1 : ℕ) preimage.val = vector.val := actual.2.trans image_eq
      refine ⟨preimage.val, weights.1, actual.1, ?_, raised.symm ▸ vector.property⟩
      intro regular
      apply no_smooth_preimage
      refine ⟨⟨preimage.val, regular⟩, weights.1, ?_⟩
      exact Subtype.ext raised
    · left
      exact cuspFiniteRaising_exists_weak_kernel_of_not_mem cusp spherical level (degree + 1 : ℕ) positive
        vector.val vector_weight in_range

end TernaryPeriodPolynomials.SphericalDetection.Helpers
