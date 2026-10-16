module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakOrbit

@[expose] public section


/-!
# Weight-generic weak raising kernels

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins, for an arbitrary integer rotation weight `wt`, of the `halfWeight` declarations of
`SphericalDetection.BinaryWeakOrbit` (base-point Cauchy-Riemann equation, affine transformation law,
holomorphy against smooth tests) and of their level-three clones: a vector annihilated by the
lowering operator of weight `wt` against all smooth tests has a weighted orbit that is holomorphic,
hence a real analytic orbit.  The real factor `point.im ^ halfWeight` is replaced by
`wtFactor wt point.im` and `2 * halfWeight` by `wt`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.MultiplicityOne

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem cuspScalarWeightedAffineOrbit_hasFDerivAt_basepointWt (cusp : CuspidalRepresentation)
    (wt : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) :
    HasFDerivAt (fun point => inner ℂ test (cuspWeightedAffineOrbitWt cusp wt vector point))
      (fderiv ℝ (fun point => inner ℂ test (cuspAffineOrbitVector cusp vector point)) Complex.I +
        (((wt : ℝ) / 2) • Complex.imCLM).smulRight (inner ℂ test vector)) Complex.I := by
  have positive : (0 : ℝ) < Complex.I.im := by simp
  have coefficient := (hasDerivAt_wtFactor wt positive).comp_hasFDerivAt
    Complex.I Complex.imCLM.hasFDerivAt
  have scalar := (cuspScalarAffineOrbit_hasFDerivAt_basepoint cusp test vector regular).differentiableAt.hasFDerivAt
  have derivative := coefficient.smul scalar
  change HasFDerivAt (fun point => wtFactor wt point.im • inner ℂ test (cuspAffineOrbitVector cusp vector point)) _ Complex.I at derivative
  simpa only [Function.comp_apply, Complex.I_im, wtFactor_one, mul_one, cuspAffineOrbitVector_I,
    one_smul, cuspWeightedAffineOrbitWt, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    smul_eq_mul, map_one] using derivative

theorem cuspScalarWeightedAffineOrbit_cauchyRiemann_basepointWt (cusp : CuspidalRepresentation)
    (wt : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I) :
    fderiv ℝ (fun point => inner ℂ test (cuspWeightedAffineOrbitWt cusp wt vector point)) Complex.I 1 +
      Complex.I * fderiv ℝ (fun point => inner ℂ test (cuspWeightedAffineOrbitWt cusp wt vector point)) Complex.I Complex.I =
        -inner ℂ (cuspLoweringVector cusp wt test) vector := by
  rw [(cuspScalarWeightedAffineOrbit_hasFDerivAt_basepointWt cusp wt test vector regular).fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply, Complex.imCLM_apply, Complex.one_im, Complex.I_im,
    smul_eq_mul, mul_zero, mul_one,
    cuspScalarAffineOrbit_fderiv_basepoint cusp test vector regular, cuspLoweringVector,
    inner_add_left, inner_sub_left, inner_smul_left, map_div₀, map_mul, map_ofNat,
    Complex.conj_I, map_intCast,
    RCLike.real_smul_eq_coe_smul (K := ℂ), map_zero]
  ring

theorem cuspScalarWeightedAffineOrbit_differentiableAt_basepointWt (cusp : CuspidalRepresentation)
    (wt : ℤ) (test vector : cusp.H)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp test) Complex.I)
    (annihilates : inner ℂ (cuspLoweringVector cusp wt test) vector = 0) :
    DifferentiableAt ℂ (fun point => inner ℂ test (cuspWeightedAffineOrbitWt cusp wt vector point)) Complex.I := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cuspScalarWeightedAffineOrbit_hasFDerivAt_basepointWt cusp wt test vector regular).differentiableAt, ?_⟩
  have equation := cuspScalarWeightedAffineOrbit_cauchyRiemann_basepointWt cusp wt test vector regular
  rw [annihilates, neg_zero] at equation
  have rotated := congrArg (fun value : ℂ => Complex.I * value) equation
  simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at rotated
  linear_combination -rotated

theorem cuspWeightedAffineOrbit_affineWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H) (point argument : UpperHalfPlane) :
    cuspWeightedAffineOrbitWt cusp wt vector ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)) =
      wtFactor wt point.im • cusp.π (atInfinity (binarySymmetricSection point))
        (cuspWeightedAffineOrbitWt cusp wt vector argument) := by
  have imaginary : ((point.re : ℂ) + (point.im : ℂ) * (argument : ℂ)).im =
      point.im * (argument : ℂ).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
      zero_add, add_zero, UpperHalfPlane.coe_im]
  have product : wtFactor wt (point.im * (argument : ℂ).im) =
      wtFactor wt point.im * wtFactor wt (argument : ℂ).im :=
    wtFactor_mul wt point.im_pos argument.im_pos
  simp only [cuspWeightedAffineOrbitWt, imaginary, product, cuspAffineOrbitVector_affine,
    LinearMap.map_smul_of_tower, smul_smul]

theorem cuspScalarWeightedAffineOrbit_holomorphic_of_testsWt (cusp : CuspidalRepresentation)
    (wt : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp wt test.val) vector = 0)
    (test : cusp.smooth) :
    DifferentiableOn ℂ (fun point => inner ℂ test.val (cuspWeightedAffineOrbitWt cusp wt vector point))
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
  have basepoint := cuspScalarWeightedAffineOrbit_differentiableAt_basepointWt cusp wt shifted.val vector
    shifted_regular (annihilates shifted)
  have pullback_regular : DifferentiableAt ℂ pullback point := by
    exact ((differentiableAt_id.sub_const (upper.re : ℂ)).const_mul (upper.im : ℂ)⁻¹)
  have transformed := ((pullback_basepoint.symm ▸ basepoint).comp point pullback_regular).const_smul
    (wtFactor wt upper.im)
  apply DifferentiableAt.differentiableWithinAt
  apply transformed.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument argument_positive
  have pulled_positive : 0 < (pullback argument).im := by
    rw [pullback_im]
    exact mul_pos (inv_pos.mpr upper.im_pos) argument_positive
  have formula := cuspWeightedAffineOrbit_affineWt cusp wt vector upper ⟨pullback argument, pulled_positive⟩
  rw [recovers] at formula
  change inner ℂ test.val (cuspWeightedAffineOrbitWt cusp wt vector argument) =
    wtFactor wt upper.im • inner ℂ shifted.val (cuspWeightedAffineOrbitWt cusp wt vector (pullback argument))
  rw [formula, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  congr 1
  exact ((cuspUnitaryIsometryEquiv cusp matrix).symm.inner_map_eq_flip test.val
    (cuspWeightedAffineOrbitWt cusp wt vector (pullback argument))).symm

theorem cuspWeakRaisingKernel_holomorphicWt (cusp : CuspidalRepresentation) (spherical :
    LevelThreeCusp cusp)
    (wt : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp wt
      test.val) vector = 0) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector)
      UpperHalfPlane.upperHalfPlaneSet := by
  apply differentiableOn_of_inner_dense (cusp.smooth : Set cusp.H) (levelThreeCusp_smooth_dense
    cusp spherical)
    _ _ UpperHalfPlane.isOpen_upperHalfPlaneSet (cuspWeightedAffineOrbit_continuousOnWt cusp
      wt vector)
  intro test member
  exact cuspScalarWeightedAffineOrbit_holomorphic_of_testsWt cusp wt vector annihilates
    ⟨test, member⟩

theorem cuspWeakRaisingKernel_analyticWt (cusp : CuspidalRepresentation) (spherical : LevelThreeCusp
    cusp)
    (wt : ℤ) (vector : cusp.H)
    (annihilates : ∀ test : cusp.smooth, inner ℂ (cuspLoweringVector cusp wt
      test.val) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  cuspAffineOrbitVector_analytic_of_weighted_holomorphicWt cusp wt vector
    (cuspWeakRaisingKernel_holomorphicWt cusp spherical wt vector annihilates)

end TernaryPeriodPolynomials.EvenLevelThree
