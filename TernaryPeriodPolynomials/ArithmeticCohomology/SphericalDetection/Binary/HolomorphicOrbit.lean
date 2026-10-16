module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalLadders
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspWeightedAffineOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (point : ℂ) : cusp.H :=
  (point.im ^ halfWeight) • cuspAffineOrbitVector cusp vector point

theorem cuspWeightedAffineOrbit_hasFDerivAt (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    HasFDerivAt (cuspWeightedAffineOrbit cusp halfWeight vector)
      (point.im ^ halfWeight • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) +
        (((halfWeight : ℝ) * point.im ^ (halfWeight - 1)) • Complex.imCLM).smulRight
          (cuspAffineOrbitVector cusp vector point)) (point : ℂ) := by
  have coefficient := (hasDerivAt_zpow halfWeight point.im (Or.inl (ne_of_gt point.im_pos))).comp_hasFDerivAt
    (point : ℂ) Complex.imCLM.hasFDerivAt
  exact coefficient.smul (regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds point.im_pos)).hasFDerivAt

theorem cuspWeightedAffineOrbit_fderiv (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) (direction : ℂ) :
    fderiv ℝ (cuspWeightedAffineOrbit cusp halfWeight vector) (point : ℂ) direction =
      point.im ^ halfWeight • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) direction +
        ((halfWeight : ℝ) * point.im ^ (halfWeight - 1) * direction.im) •
          cuspAffineOrbitVector cusp vector point := by
  rw [(cuspWeightedAffineOrbit_hasFDerivAt cusp halfWeight vector regular point).fderiv]
  rfl

theorem cuspRaisingVector_translate (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    cuspAffineOrbitVector cusp (cuspRaisingVector cusp (2 * halfWeight) vector) point =
      point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) 1 +
        Complex.I • (point.im • fderiv ℝ (cuspAffineOrbitVector cusp vector) (point : ℂ) Complex.I) +
          (Complex.I * (halfWeight : ℂ)) • cuspAffineOrbitVector cusp vector point := by
  have coefficient : Complex.I * ((2 * halfWeight : ℤ) : ℂ) / 2 = Complex.I * (halfWeight : ℂ) := by
    push_cast
    ring
  change cusp.π _ (_ + _ + _) = _
  rw [map_add, map_add, map_smul, map_smul]
  change cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I 1) point +
    Complex.I • cuspAffineOrbitVector cusp (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I Complex.I) point +
      (Complex.I * ((2 * halfWeight : ℤ) : ℂ) / 2) • cuspAffineOrbitVector cusp vector point = _
  rw [coefficient, cuspAffineOrbitVector_derivative_translate cusp vector regular,
    cuspAffineOrbitVector_derivative_translate cusp vector regular]

theorem cuspWeightedAffineOrbit_cauchyRiemann (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (point : UpperHalfPlane) :
    fderiv ℝ (cuspWeightedAffineOrbit cusp halfWeight vector) (point : ℂ) 1 +
      Complex.I • fderiv ℝ (cuspWeightedAffineOrbit cusp halfWeight vector) (point : ℂ) Complex.I =
        point.im ^ (halfWeight - 1) •
          cuspAffineOrbitVector cusp (cuspRaisingVector cusp (2 * halfWeight) vector) point := by
  have power : point.im ^ halfWeight = point.im ^ (halfWeight - 1) * point.im := by
    calc
      _ = point.im ^ ((halfWeight - 1) + 1) := by congr 1; omega
      _ = _ := by rw [zpow_add₀ (ne_of_gt point.im_pos), zpow_one]
  rw [cuspWeightedAffineOrbit_fderiv cusp halfWeight vector regular,
    cuspWeightedAffineOrbit_fderiv cusp halfWeight vector regular,
    cuspRaisingVector_translate cusp halfWeight vector regular]
  simp only [Complex.one_im, Complex.I_im, mul_zero, mul_one, power,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

theorem cuspWeightedAffineOrbit_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(cuspWeightedAffineOrbit_hasFDerivAt cusp halfWeight vector regular ⟨point, positive⟩).differentiableAt, ?_⟩
  have equation := cuspWeightedAffineOrbit_cauchyRiemann cusp halfWeight vector regular ⟨point, positive⟩
  rw [raising_zero] at equation
  have orbit_zero : cuspAffineOrbitVector cusp 0 point = 0 := map_zero _
  simp only [orbit_zero, smul_zero] at equation
  have rotated := congrArg (fun value : cusp.H => Complex.I • value) equation
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, smul_zero] at rotated
  apply Eq.symm
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using rotated

theorem cuspAffineOrbitVector_analytic_of_raising_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    AnalyticOnNhd ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  have holomorphic := cuspWeightedAffineOrbit_holomorphic cusp halfWeight vector regular raising_zero
  have weighted_analytic := holomorphic.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  intro point positive
  have coefficient : AnalyticAt ℝ (fun argument : ℂ => argument.im ^ (-halfWeight)) point :=
    (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  have analytic := coefficient.smul ((weighted_analytic point positive).restrictScalars (𝕜 := ℝ))
  apply analytic.congr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive] with argument member
  change (argument.im ^ (-halfWeight)) •
    ((argument.im ^ halfWeight) • cuspAffineOrbitVector cusp vector argument) =
      cuspAffineOrbitVector cusp vector argument
  rw [smul_smul, ← zpow_add₀ (ne_of_gt member), neg_add_cancel, zpow_zero, one_smul]

theorem cuspAffineOrbitVector_contDiffOn_top_of_raising_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector = 0) :
    ContDiffOn ℝ ⊤ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet :=
  (cuspAffineOrbitVector_analytic_of_raising_zero cusp halfWeight vector regular raising_zero).contDiffOn
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
