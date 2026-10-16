module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.HolomorphicOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCauchyRiemannRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakOrbit

@[expose] public section


/-!
# Weight-generic affine orbits

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of the `halfWeight` orbit results of `BinaryHolomorphicOrbit`,
`BinaryAffineCauchyRiemannRegularity` and `BinaryWeakOrbit` for an arbitrary integer rotation weight
`wt`, with the real factor `point.im ^ halfWeight` replaced by `wtFactor wt point.im`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

theorem analyticAt_wtFactor_im (wt : ℤ) {point : ℂ} (positive : 0 < point.im) :
    AnalyticAt ℝ (fun argument : ℂ => wtFactor wt argument.im) point := by
  have composed := (analyticAt_wtFactor wt (y := Complex.imCLM point) positive).comp
    (Complex.imCLM.analyticAt point)
  exact composed

theorem analyticOnNhd_wtFactor_im (wt : ℤ) :
    AnalyticOnNhd ℝ (fun argument : ℂ => wtFactor wt argument.im) UpperHalfPlane.upperHalfPlaneSet :=
  fun point positive => analyticAt_wtFactor_im wt (point := point) positive

def cuspWeightedAffineOrbitWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H) (point : ℂ) : cusp.H :=
  (wtFactor wt point.im) • cuspAffineOrbitVector cusp vector point

theorem cuspWeightedAffineOrbit_hasFDerivAtWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    HasFDerivAt (cuspWeightedAffineOrbitWt cusp wt vector)
      (wtFactor wt point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) +
        ((((wt : ℝ) / 2) * wtFactor (wt - 2) point.im) • Complex.imCLM).smulRight
          (cuspAffineOrbitVector cusp vector point)) (point : ℂ) := by
  have coefficient := (hasDerivAt_wtFactor wt point.im_pos).comp_hasFDerivAt
    (point : ℂ) Complex.imCLM.hasFDerivAt
  exact coefficient.smul (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt

theorem cuspWeightedAffineOrbit_fderivWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) (direction : ℂ) :
    fderiv ℝ (cuspWeightedAffineOrbitWt cusp wt vector) (point : ℂ) direction =
      wtFactor wt point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) direction +
        (((wt : ℝ) / 2) * wtFactor (wt - 2) point.im * direction.im) •
          cuspAffineOrbitVector cusp vector point := by
  rw [(cuspWeightedAffineOrbit_hasFDerivAtWt cusp wt vector regular point).fderiv]
  rfl

theorem cuspRaisingVector_translateWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    cuspAffineOrbitVector cusp (cuspRaisingVector cusp wt vector) point =
      point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) 1 +
        Complex.I • (point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) Complex.I) +
          (Complex.I * ((wt : ℂ) / 2)) • cuspAffineOrbitVector cusp vector point := by
  have coefficient : Complex.I * (wt : ℂ) / 2 = Complex.I * ((wt : ℂ) / 2) := by
    ring
  change cusp.π _ (_ + _ + _) = _
  rw [map_add, map_add, map_smul, map_smul]
  change cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1) point +
    Complex.I • cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) point +
      (Complex.I * (wt : ℂ) / 2) • cuspAffineOrbitVector cusp vector point = _
  rw [coefficient, cuspAffineOrbitVector_derivative_translate cusp vector regular,
    cuspAffineOrbitVector_derivative_translate cusp vector regular]

theorem cuspWeightedAffineOrbit_cauchyRiemannWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    fderiv ℝ (cuspWeightedAffineOrbitWt cusp wt vector) (point : ℂ) 1 +
      Complex.I • fderiv ℝ (cuspWeightedAffineOrbitWt cusp wt vector) (point : ℂ) Complex.I =
        wtFactor (wt - 2) point.im •
          cuspAffineOrbitVector cusp (cuspRaisingVector cusp wt vector) point := by
  have power : wtFactor wt point.im = wtFactor (wt - 2) point.im * point.im :=
    wtFactor_eq_mul_sub_two wt point.im_pos
  rw [cuspWeightedAffineOrbit_fderivWt cusp wt vector regular,
    cuspWeightedAffineOrbit_fderivWt cusp wt vector regular,
    cuspRaisingVector_translateWt cusp wt vector regular]
  simp only [Complex.one_im, Complex.I_im, mul_zero, mul_one, power,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem cuspWeightedAffineOrbit_holomorphicWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp wt vector = 0) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector) UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cuspWeightedAffineOrbit_hasFDerivAtWt cusp wt vector regular ⟨point, positive⟩).differentiableAt, ?_⟩
  have equation := cuspWeightedAffineOrbit_cauchyRiemannWt cusp wt vector regular ⟨point, positive⟩
  rw [raising_zero] at equation
  have orbit_zero : cuspAffineOrbitVector cusp 0 point = 0 := map_zero _
  simp only [orbit_zero, smul_zero] at equation
  have rotated := congrArg (fun value : cusp.H => Complex.I • value) equation
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, smul_zero] at rotated
  apply Eq.symm
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using rotated

theorem cuspAffineOrbitVector_analytic_of_weighted_holomorphicWt (cusp : CuspidalRepresentation)
    (wt : ℤ) (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbitWt cusp wt vector) UpperHalfPlane.upperHalfPlaneSet) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have weighted := holomorphic.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro point positive
  have coefficient : AnalyticAt ℝ (fun argument : ℂ => wtFactor (-wt) argument.im) point :=
    analyticAt_wtFactor_im (-wt) (point := point) positive
  have analytic := coefficient.smul ((weighted point positive).restrictScalars (𝕜 := ℝ))
  apply analytic.congr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument member
  change (wtFactor (-wt) argument.im) •
    ((wtFactor wt argument.im) • cuspAffineOrbitVector cusp vector argument) =
      cuspAffineOrbitVector cusp vector argument
  rw [smul_smul, mul_comm (wtFactor (-wt) argument.im), wtFactor_neg_mul, one_smul]

theorem cuspAffineOrbitVector_analytic_of_raising_zeroWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp wt vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  cuspAffineOrbitVector_analytic_of_weighted_holomorphicWt cusp wt vector
    (cuspWeightedAffineOrbit_holomorphicWt cusp wt vector regular raising_zero)

theorem cuspAffineOrbitVector_contDiffOn_top_of_raising_zeroWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp wt vector = 0) :
    ContDiffOn ℝ ⊤ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  (cuspAffineOrbitVector_analytic_of_raising_zeroWt cusp wt vector regular raising_zero).contDiffOn
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn)

theorem cuspWeightedAffineOrbit_contDiffOn_oneWt (cusp : CuspidalRepresentation) (wt : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ 1 (cuspWeightedAffineOrbitWt cusp wt vector) UpperHalfPlane.upperHalfPlaneSet := by
  have coefficient : AnalyticOnNhd ℝ (fun point : ℂ => wtFactor wt point.im) UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_wtFactor_im wt
  exact (coefficient.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn).smul
    (cuspAffineOrbitVector_contDiffOn_one cusp vector regular)

theorem cuspWeightedAffineOrbit_cauchyRiemann_contDiffOnWt (cusp : CuspidalRepresentation) (wt : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raised_smooth : cuspRaisingVector cusp wt vector ∈ cuspAffineSmoothValues cusp) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point => fderiv ℝ (cuspWeightedAffineOrbitWt cusp wt vector) point 1 +
        Complex.I • fderiv ℝ (cuspWeightedAffineOrbitWt cusp wt vector) point Complex.I)
      UpperHalfPlane.upperHalfPlaneSet := by
  have analytic : AnalyticOnNhd ℝ
      (fun point : ℂ => wtFactor (wt - 2) point.im) UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_wtFactor_im (wt - 2)
  have coefficient : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point : ℂ => wtFactor (wt - 2) point.im) UpperHalfPlane.upperHalfPlaneSet :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (coefficient.smul raised_smooth).congr
  intro point positive
  exact cuspWeightedAffineOrbit_cauchyRiemannWt cusp wt vector regular ⟨point, positive⟩

theorem cuspAffineOrbitVector_contDiffOn_of_raising_smoothWt (cusp : CuspidalRepresentation) (wt : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raised_smooth : cuspRaisingVector cusp wt vector ∈ cuspAffineSmoothValues cusp) :
    vector ∈ cuspAffineSmoothValues cusp := by
  have weighted_smooth := contDiffOn_of_contDiffOn_antiholomorphicDerivative
    (cuspWeightedAffineOrbitWt cusp wt vector) UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.isOpen_upperHalfPlaneSet
    (cuspWeightedAffineOrbit_contDiffOn_oneWt cusp wt vector regular)
    (cuspWeightedAffineOrbit_cauchyRiemann_contDiffOnWt cusp wt vector regular raised_smooth)
  have coefficient : AnalyticOnNhd ℝ (fun point : ℂ => wtFactor (-wt) point.im) UpperHalfPlane.upperHalfPlaneSet :=
    analyticOnNhd_wtFactor_im (-wt)
  have smooth := (coefficient.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn).smul weighted_smooth
  apply smooth.congr
  intro point positive
  change cuspAffineOrbitVector cusp vector point = wtFactor (-wt) point.im •
    (wtFactor wt point.im • cuspAffineOrbitVector cusp vector point)
  rw [smul_smul, mul_comm (wtFactor (-wt) point.im), wtFactor_neg_mul, one_smul]

theorem cuspWeightedAffineOrbit_continuousOnWt (cusp : CuspidalRepresentation) (wt : ℤ) (vector : cusp.H) :
    ContinuousOn (cuspWeightedAffineOrbitWt cusp wt vector) UpperHalfPlane.upperHalfPlaneSet :=
  (analyticOnNhd_wtFactor_im wt).continuousOn.smul
    (cuspAffineOrbitVector_continuousOn cusp vector)

end TernaryPeriodPolynomials.EvenLevelThree
