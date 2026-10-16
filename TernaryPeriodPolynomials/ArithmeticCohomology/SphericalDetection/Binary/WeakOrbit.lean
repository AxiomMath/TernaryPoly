module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderClosures
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HolomorphicOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.WeakHolomorphic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryAffineInverse (point : ℂ) : ℂ := point.im⁻¹ • (Complex.I - (point.re : ℂ))

theorem binaryAffineInverse_im (point : ℂ) : (binaryAffineInverse point).im = point.im⁻¹ := by
  simp [binaryAffineInverse, Complex.real_smul]

theorem binaryAffineInverse_I : binaryAffineInverse Complex.I = Complex.I := by
  simp [binaryAffineInverse]

theorem binaryAffineInverse_hasFDerivAt :
    HasFDerivAt binaryAffineInverse (-ContinuousLinearMap.id ℝ ℂ) Complex.I := by
  have denominator := (hasDerivAt_inv (by simp : Complex.I.im ≠ 0)).comp_hasFDerivAt Complex.I Complex.imCLM.hasFDerivAt
  have numerator := (hasFDerivAt_const Complex.I Complex.I).sub
    (Complex.ofRealCLM.hasFDerivAt.comp Complex.I Complex.reCLM.hasFDerivAt)
  convert denominator.smul numerator using 1 <;> first | rfl | (ext direction; apply Complex.ext <;> simp [Complex.real_smul])

theorem binaryAffineSection_inverse (point : ℂ) (positive : 0 < point.im) :
    invertibleMatrix (binaryUpperSectionMatrix (binaryAffineInverse point)) =
      (invertibleMatrix (binaryUpperSectionMatrix point))⁻¹ := by
  have inverse_positive : 0 < (binaryAffineInverse point).im := by
    rw [binaryAffineInverse_im]
    exact inv_pos.mpr positive
  have identity : (point.re : ℂ) + (point.im : ℂ) * binaryAffineInverse point = Complex.I := by
    rw [binaryAffineInverse, Complex.real_smul, ← mul_assoc]
    norm_cast
    rw [mul_inv_cancel₀ (ne_of_gt positive), Complex.ofReal_one, one_mul, add_sub_cancel]
  have product := binaryUpperSectionMatrix_affine_mul point (binaryAffineInverse point) positive inverse_positive
  rw [identity, binaryUpperSectionMatrix_I] at product
  have group_product : invertibleMatrix (binaryUpperSectionMatrix point) *
      invertibleMatrix (binaryUpperSectionMatrix (binaryAffineInverse point)) = 1 := by
    rw [← invertibleMatrix_mul _ _ (binaryUpperSectionMatrix_invertible point positive)
      (binaryUpperSectionMatrix_invertible _ inverse_positive), ← product]
    exact invertibleMatrix_coe 1
  exact eq_inv_of_mul_eq_one_right group_product

theorem cuspAffineOrbitVector_inner_inverse (cusp : CuspidalRepresentation) (test vector : cusp.H)
    (point : ℂ) (positive : 0 < point.im) :
    inner ℂ test (cuspAffineOrbitVector cusp vector point) =
      inner ℂ (cuspAffineOrbitVector cusp test (binaryAffineInverse point)) vector := by
  let matrix := atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))
  have identity := (cuspUnitaryIsometryEquiv cusp matrix).symm.inner_map_eq_flip test vector
  change inner ℂ (cusp.π matrix⁻¹ test) vector = inner ℂ test (cusp.π matrix vector) at identity
  simp only [cuspAffineOrbitVector, binaryAffineSection_inverse point positive, atInfinity_inv]
  exact identity.symm

theorem cuspScalarAffineOrbit_hasFDerivAt_basepoint (cusp : CuspidalRepresentation) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) :
    HasFDerivAt (fun point => inner ℂ test (cuspAffineOrbitVector cusp vector point))
      ((Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ vector).restrictScalars ℝ)).comp
        (-(fderiv ℝ (cuspAffineOrbitVector cusp test) Complex.I))) Complex.I := by
  have inverse_regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) (binaryAffineInverse Complex.I) :=
    binaryAffineInverse_I.symm ▸ regular
  have derivative := inverse_regular.hasFDerivAt.comp Complex.I binaryAffineInverse_hasFDerivAt
  have paired := (Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ vector).restrictScalars ℝ)).hasFDerivAt.comp Complex.I derivative
  have equality : (fun point => inner ℂ test (cuspAffineOrbitVector cusp vector point)) =ᶠ[nhds Complex.I]
      (fun point => (Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ vector).restrictScalars ℝ))
        (cuspAffineOrbitVector cusp test (binaryAffineInverse point))) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show Complex.I.im > 0 by simp)] with point positive
    rw [cuspAffineOrbitVector_inner_inverse cusp test vector point positive]
    change inner ℂ (cuspAffineOrbitVector cusp test (binaryAffineInverse point)) vector =
      (starRingEnd ℂ) (inner ℂ vector (cuspAffineOrbitVector cusp test (binaryAffineInverse point)))
    exact (inner_conj_symm _ _).symm
  have result := paired.congr_of_eventuallyEq equality
  simpa only [binaryAffineInverse_I, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using result

theorem cuspScalarAffineOrbit_fderiv_basepoint (cusp : CuspidalRepresentation) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) (direction : ℂ) :
    fderiv ℝ (fun point => inner ℂ test (cuspAffineOrbitVector cusp vector point)) Complex.I direction =
      -inner ℂ (fderiv ℝ (cuspAffineOrbitVector cusp test) Complex.I direction) vector := by
  rw [(cuspScalarAffineOrbit_hasFDerivAt_basepoint cusp test vector regular).fderiv]
  change (starRingEnd ℂ) (inner ℂ vector (-(fderiv ℝ (cuspAffineOrbitVector cusp test) Complex.I direction))) = _
  rw [inner_neg_right, map_neg, inner_conj_symm]

theorem cuspScalarWeightedAffineOrbit_hasFDerivAt_basepoint (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) :
    HasFDerivAt (fun point => inner ℂ test (cuspWeightedAffineOrbit cusp halfWeight vector point))
      (fderiv ℝ (fun point => inner ℂ test (cuspAffineOrbitVector cusp vector point)) Complex.I +
        ((halfWeight : ℝ) • Complex.imCLM).smulRight (inner ℂ test vector)) Complex.I := by
  have coefficient := (hasDerivAt_zpow halfWeight Complex.I.im (Or.inl (by simp))).comp_hasFDerivAt
    Complex.I Complex.imCLM.hasFDerivAt
  have scalar := (cuspScalarAffineOrbit_hasFDerivAt_basepoint cusp test vector regular).differentiableAt.hasFDerivAt
  have derivative := coefficient.smul scalar
  change HasFDerivAt (fun point => point.im ^ halfWeight • inner ℂ test (cuspAffineOrbitVector cusp vector point)) _ Complex.I at derivative
  simpa only [Function.comp_apply, Complex.I_im, one_zpow, mul_one, cuspAffineOrbitVector_I,
    one_smul, cuspWeightedAffineOrbit, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    smul_eq_mul, map_one] using derivative

theorem cuspScalarWeightedAffineOrbit_cauchyRiemann_basepoint (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) :
    fderiv ℝ (fun point => inner ℂ test (cuspWeightedAffineOrbit cusp halfWeight vector point)) Complex.I 1 +
      Complex.I * fderiv ℝ (fun point => inner ℂ test (cuspWeightedAffineOrbit cusp halfWeight vector point)) Complex.I Complex.I =
        -inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test) vector := by
  rw [(cuspScalarWeightedAffineOrbit_hasFDerivAt_basepoint cusp halfWeight test vector regular).fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, Complex.imCLM_apply, Complex.one_im, Complex.I_im,
    smul_eq_mul, mul_zero, mul_one,
    cuspScalarAffineOrbit_fderiv_basepoint cusp test vector regular, cuspLoweringVector,
    inner_add_left, inner_sub_left, inner_smul_left, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, map_intCast, Int.cast_mul, Int.cast_ofNat,
    RCLike.real_smul_eq_coe_smul (K := ℂ), map_zero]
  ring

theorem cuspScalarWeightedAffineOrbit_differentiableAt_basepoint (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I)
    (annihilates : inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test) vector = 0) :
    DifferentiableAt ℂ (fun point => inner ℂ test (cuspWeightedAffineOrbit cusp halfWeight vector point)) Complex.I := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cuspScalarWeightedAffineOrbit_hasFDerivAt_basepoint cusp halfWeight test vector regular).differentiableAt, ?_⟩
  have equation := cuspScalarWeightedAffineOrbit_cauchyRiemann_basepoint cusp halfWeight test vector regular
  rw [annihilates, neg_zero] at equation
  have rotated := congrArg (fun value : ℂ => Complex.I * value) equation
  simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at rotated
  linear_combination -rotated

theorem cuspWeightedAffineOrbit_affine (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (point argument : UpperHalfPlane) :
    cuspWeightedAffineOrbit cusp halfWeight vector ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      point.im ^ halfWeight • cusp.π (atInfinity (binarySymmetricSection point))
        (cuspWeightedAffineOrbit cusp halfWeight vector argument) := by
  simp only [cuspWeightedAffineOrbit, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, zero_mul, zero_add, add_zero, UpperHalfPlane.coe_im, mul_zpow,
    cuspAffineOrbitVector_affine, LinearMap.map_smul_of_tower, smul_smul]

theorem cuspScalarWeightedAffineOrbit_holomorphic_of_tests (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test.val) vector = 0)
    (test : cusp.smooth) :
    DifferentiableOn ℂ (fun point => inner ℂ test.val (cuspWeightedAffineOrbit cusp halfWeight vector point))
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let matrix := atInfinity (binarySymmetricSection upper)
  let shifted : cusp.smooth := ⟨cusp.π matrix⁻¹ test.val, cusp.smooth_stable matrix⁻¹ test.val test.property⟩
  let pullback : ℂ → ℂ := fun argument => (upper.im : ℂ)⁻¹ * (argument - (upper.re : ℂ))
  have pullback_im (argument : ℂ) : (pullback argument).im = upper.im⁻¹ * argument.im := by
    simp [pullback, ← Complex.ofReal_inv]
  have pullback_basepoint : pullback point = Complex.I := by
    apply Complex.ext
    · simp [pullback, ← Complex.ofReal_inv, upper]
    · rw [pullback_im]
      exact inv_mul_cancel₀ (ne_of_gt positive)
  have recovers (argument : ℂ) : (upper.re : ℂ) + (upper.im : ℂ) * pullback argument = argument := by
    dsimp only [pullback]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt upper.im_pos), one_mul, add_sub_cancel]
  have shifted_regular := cuspAffineSmoothValues_differentiable cusp
    ⟨shifted.val, cuspSmooth_le_affineSmooth cusp shifted.property⟩
  have basepoint := cuspScalarWeightedAffineOrbit_differentiableAt_basepoint cusp halfWeight shifted.val vector
    shifted_regular (annihilates shifted)
  have pullback_regular : DifferentiableAt ℂ pullback point := by
    exact ((differentiableAt_id.sub_const (upper.re : ℂ)).const_mul (upper.im : ℂ)⁻¹)
  have transformed := ((pullback_basepoint.symm ▸ basepoint).comp point pullback_regular).const_smul
    (upper.im ^ halfWeight)
  apply DifferentiableAt.differentiableWithinAt
  apply transformed.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument argument_positive
  have pulled_positive : 0 < (pullback argument).im := by
    rw [pullback_im]
    exact mul_pos (inv_pos.mpr upper.im_pos) argument_positive
  have formula := cuspWeightedAffineOrbit_affine cusp halfWeight vector upper ⟨pullback argument, pulled_positive⟩
  rw [recovers] at formula
  change inner ℂ test.val (cuspWeightedAffineOrbit cusp halfWeight vector argument) =
    upper.im ^ halfWeight • inner ℂ shifted.val (cuspWeightedAffineOrbit cusp halfWeight vector (pullback argument))
  rw [formula, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  congr 1
  exact ((cuspUnitaryIsometryEquiv cusp matrix).symm.inner_map_eq_flip test.val
    (cuspWeightedAffineOrbit cusp halfWeight vector (pullback argument))).symm

theorem cuspAffineOrbitVector_continuousOn (cusp : CuspidalRepresentation) (vector : cusp.H) :
    ContinuousOn (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have upper : Continuous (fun point : UpperHalfPlane => cusp.π (atInfinity (binarySymmetricSection point)) vector) :=
    (cusp.continuous vector).comp (atInfinity_continuous.comp binarySymmetricSection_continuous)
  have continuous := upper.comp_continuousOn UpperHalfPlane.ofComplex.continuousOn
  have domain_subset : UpperHalfPlane.upperHalfPlaneSet ⊆ UpperHalfPlane.ofComplex.source := by
    simp only [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe, Set.Subset.refl]
  apply (continuous.mono domain_subset).congr
  intro point positive
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
  rw [cuspAffineOrbitVector, binaryUpperSectionMatrix_coe (⟨point, positive⟩ : UpperHalfPlane), invertibleMatrix_coe]

theorem cuspWeightedAffineOrbit_continuousOn (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H) :
    ContinuousOn (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet :=
  (Complex.continuous_im.continuousOn.zpow₀ halfWeight (fun _ positive => Or.inl (ne_of_gt positive))).smul
    (cuspAffineOrbitVector_continuousOn cusp vector)

theorem cuspWeakRaisingKernel_holomorphic (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test.val) vector = 0) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet := by
  apply differentiableOn_of_inner_dense (cusp.smooth : Set cusp.H) (sphericalCusp_smooth_dense cusp spherical)
    _ _ UpperHalfPlane.isOpen_upperHalfPlaneSet (cuspWeightedAffineOrbit_continuousOn cusp halfWeight vector)
  intro test member
  exact cuspScalarWeightedAffineOrbit_holomorphic_of_tests cusp halfWeight vector annihilates ⟨test, member⟩

theorem cuspAffineOrbitVector_analytic_of_weighted_holomorphic (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have weighted := holomorphic.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro point positive
  have coefficient : AnalyticAt ℝ (fun argument : ℂ => argument.im ^ (-halfWeight)) point :=
    (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  have analytic := coefficient.smul ((weighted point positive).restrictScalars (𝕜 := ℝ))
  apply analytic.congr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument member
  change (argument.im ^ (-halfWeight)) •
    ((argument.im ^ halfWeight) • cuspAffineOrbitVector cusp vector argument) =
      cuspAffineOrbitVector cusp vector argument
  rw [smul_smul, ← zpow_add₀ (ne_of_gt member), neg_add_cancel, zpow_zero, one_smul]

theorem cuspWeakRaisingKernel_analytic (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test.val) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  cuspAffineOrbitVector_analytic_of_weighted_holomorphic cusp halfWeight vector
    (cuspWeakRaisingKernel_holomorphic cusp spherical halfWeight vector annihilates)

theorem cuspWeakRaisingKernel_raising_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (halfWeight : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test.val) vector = 0) :
    cuspRaisingVector cusp (2 * halfWeight) vector = 0 := by
  have analytic := cuspWeakRaisingKernel_analytic cusp spherical halfWeight vector annihilates
  have regular : vector ∈ cuspAffineSmoothValues cusp :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (sphericalCusp_smooth_dense cusp spherical).eq_zero_of_inner_right ℂ
  intro test member
  have skew := cuspLoweringOperator_skew cusp (2 * halfWeight)
    ⟨test, cuspSmooth_le_affineSmooth cusp member⟩ ⟨vector, regular⟩
  change inner ℂ (cuspLoweringVector cusp (2 * halfWeight) test) vector +
    inner ℂ test (cuspRaisingVector cusp (2 * halfWeight) vector) = 0 at skew
  rw [annihilates ⟨test, member⟩, zero_add] at skew
  exact skew

end TernaryPeriodPolynomials.SphericalDetection.Helpers
