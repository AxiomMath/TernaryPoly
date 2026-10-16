module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineDerivativeLimit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeakOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CauchyRiemannLocalRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspAffineOrbitVector_fderiv_continuousOn (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContinuousOn (fderiv ℝ (cuspAffineOrbitVector cusp vector)) UpperHalfPlane.upperHalfPlaneSet := by
  rw [continuousOn_clm_apply]
  intro direction
  have coefficient : ContinuousOn (fun point : ℂ => point.im⁻¹) UpperHalfPlane.upperHalfPlaneSet :=
    Complex.continuous_im.continuousOn.inv₀ (fun _ positive => ne_of_gt positive)
  have translated := coefficient.smul (cuspAffineOrbitVector_continuousOn cusp
    (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction))
  apply translated.congr
  intro point positive
  dsimp only [Pi.smul_apply]
  rw [cuspAffineOrbitVector_fderiv_translate cusp vector regular point positive]
  rfl

theorem cuspAffineOrbitVector_contDiffOn_one (cusp : CuspidalRepresentation) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ 1 (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet]
  exact ⟨regular, by simp, contDiffOn_zero.mpr (cuspAffineOrbitVector_fderiv_continuousOn cusp vector regular)⟩

theorem cuspWeightedAffineOrbit_contDiffOn_one (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet) :
    ContDiffOn ℝ 1 (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet := by
  have coefficient : AnalyticOnNhd ℝ (fun point : ℂ => point.im ^ halfWeight) UpperHalfPlane.upperHalfPlaneSet :=
    fun point positive => (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  exact (coefficient.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn).smul
    (cuspAffineOrbitVector_contDiffOn_one cusp vector regular)

theorem cuspWeightedAffineOrbit_cauchyRiemann_contDiffOn (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raised_smooth : cuspRaisingVector cusp (2 * halfWeight) vector ∈ cuspAffineSmoothValues cusp) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point => fderiv ℝ (cuspWeightedAffineOrbit cusp halfWeight vector) point 1 +
        Complex.I • fderiv ℝ (cuspWeightedAffineOrbit cusp halfWeight vector) point Complex.I)
      UpperHalfPlane.upperHalfPlaneSet := by
  have analytic : AnalyticOnNhd ℝ
      (fun point : ℂ => point.im ^ (halfWeight - 1)) UpperHalfPlane.upperHalfPlaneSet :=
    fun point positive => (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  have coefficient : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (fun point : ℂ => point.im ^ (halfWeight - 1)) UpperHalfPlane.upperHalfPlaneSet :=
    analytic.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn
  apply (coefficient.smul raised_smooth).congr
  intro point positive
  exact cuspWeightedAffineOrbit_cauchyRiemann cusp halfWeight vector regular ⟨point, positive⟩

theorem cuspAffineOrbitVector_contDiffOn_of_raising_smooth (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (regular : DifferentiableOn ℝ (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (raised_smooth : cuspRaisingVector cusp (2 * halfWeight) vector ∈ cuspAffineSmoothValues cusp) :
    vector ∈ cuspAffineSmoothValues cusp := by
  have weighted_smooth := contDiffOn_of_contDiffOn_antiholomorphicDerivative
    (cuspWeightedAffineOrbit cusp halfWeight vector) UpperHalfPlane.upperHalfPlaneSet UpperHalfPlane.isOpen_upperHalfPlaneSet
    (cuspWeightedAffineOrbit_contDiffOn_one cusp halfWeight vector regular)
    (cuspWeightedAffineOrbit_cauchyRiemann_contDiffOn cusp halfWeight vector regular raised_smooth)
  have coefficient : AnalyticOnNhd ℝ (fun point : ℂ => point.im ^ (-halfWeight)) UpperHalfPlane.upperHalfPlaneSet :=
    fun point positive => (Complex.imCLM.analyticAt point).zpow (ne_of_gt positive)
  have smooth := (coefficient.contDiffOn UpperHalfPlane.isOpen_upperHalfPlaneSet.uniqueDiffOn).smul weighted_smooth
  apply smooth.congr
  intro point positive
  change cuspAffineOrbitVector cusp vector point = point.im ^ (-halfWeight) •
    (point.im ^ halfWeight • cuspAffineOrbitVector cusp vector point)
  rw [smul_smul, ← zpow_add₀ (ne_of_gt positive), neg_add_cancel, zpow_zero, one_smul]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
