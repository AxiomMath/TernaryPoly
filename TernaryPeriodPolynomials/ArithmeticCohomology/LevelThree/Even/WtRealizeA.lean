module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtEndpoint
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalar

@[expose] public section


/-!
# Scalar realization of the Hilbert-space Eichler periods, for every integer rotation weight

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `endpointCoefficient`, `binaryEndpointPeriod_realize`, `binaryEndpointPeriod_smooth`,
`hilbertLift_binaryEndpointPeriod` and `endpointScalar` of `AxiomCodeAnalytic` (files
`EndpointPeriodRealize` and `EichlerBridgeIdentity`) for an integer rotation weight `wt` in place of
`2 * halfWeight`: the real factor `y ^ halfWeight` is replaced by `wtFactor wt y`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Set
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

namespace TernaryPeriodPolynomials.EvenLevelThree

variable {n : ℕ}

/-- The scalar coefficient of the Eichler integrand, for an integer rotation weight. -/
def endpointCoefficientWt (degree : ℕ) (wt : ℤ) (z : ℂ) (position : Fin (degree + 2))
    (t : ℝ) : ℂ :=
  (z - Complex.I) * ((binaryWeightBasis (degree + 1)).coord position
      (binaryPointPower (degree + 1) (clampedPath z t)) *
    ((wtFactor wt (clampedPath z t).im : ℝ) : ℂ))

theorem endpointCoefficient_continuousWt (degree : ℕ) (wt : ℤ) (z : ℂ) (hz : 0 < z.im)
    (position : Fin (degree + 2)) :
    Continuous (endpointCoefficientWt degree wt z position) := by
  unfold endpointCoefficientWt
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · have hpoly : Continuous (fun point : ℂ => (binaryWeightBasis (degree + 1)).coord position
        (binaryPointPower (degree + 1) point)) :=
      continuous_iff_continuousAt.mpr fun point =>
        (binaryPointPower_functional_analytic (degree + 1)
          ((binaryWeightBasis (degree + 1)).coord position) point).continuousAt
    exact hpoly.comp (clampedPath_continuous z)
  · have hfactor : Continuous (fun t : ℝ => wtFactor wt (clampedPath z t).im) := by
      refine continuous_iff_continuousAt.mpr fun t => ?_
      have outer : ContinuousAt (wtFactor wt) (clampedPath z t).im :=
        wtFactor_continuousAt wt (clampedPath_im_pos z hz t)
      have inner : ContinuousAt (fun s : ℝ => (clampedPath z s).im) t :=
        (Complex.continuous_im.comp (clampedPath_continuous z)).continuousAt
      exact ContinuousAt.comp (g := wtFactor wt) (f := fun s : ℝ => (clampedPath z s).im)
        outer inner
    exact Complex.continuous_ofReal.comp hfactor

/-- **Scalar realization of the Eichler period, weight-generic.** Every coordinate of the
Hilbert-space Eichler period of a smooth finite-level vector is a smooth vector whose realization
is the scalar Eichler integral of the realized orbit. -/
theorem binaryEndpointPeriod_realizeWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (degree : ℕ) (wt : ℤ)
    (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (hz : 0 < z.im) (position : Fin (degree + 2)) :
    ∃ w : cusp.smooth, w.val = binaryEndpointPeriodWt cusp degree wt vector.val z position ∧
      ∀ h, cusp.realize w h = ∫ t in (0 : ℝ)..1, endpointCoefficientWt degree wt z position t *
        cusp.realize vector (h * atInfinity (invertibleMatrix
          (binaryUpperSectionMatrix (clampedPath z t)))) := by
  obtain ⟨w, hw, hr⟩ := commutesOn_of_continuous cusp stages vector fixed
    (fun t => binaryUpperSectionMatrix (clampedPath z t)) (endpointCoefficientWt degree wt z position)
    (upperSection_continuous z hz) (endpointCoefficient_continuousWt degree wt z hz position)
    (upperSection_det_ne_zero z hz) 0 1 zero_le_one
  refine ⟨w, ?_, hr⟩
  rw [hw]
  have hint := binaryEndpointPeriod_integrableWt cusp degree wt vector.val z hz
  have key : (binaryEndpointPeriodWt cusp degree wt vector.val z) position =
      ∫ t in (0 : ℝ)..1, ((z - Complex.I) • binaryEndpointHolomorphicFormWt cusp degree wt vector.val
        (Complex.I + t • (z - Complex.I))) position := by
    have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (degree + 2) => cusp.H)
      position).intervalIntegral_comp_comm hint
    exact this.symm
  rw [key]
  apply intervalIntegral.integral_congr
  intro t ht
  have hpath := clampedPath_eqOn z ht
  simp only [Pi.smul_apply]
  simp only at hpath
  rw [← hpath]
  simp only [binaryEndpointHolomorphicFormWt, cuspWeightedAffineOrbitWt, cuspAffineOrbitVector,
    endpointCoefficientWt, realOrbit]
  rw [← Complex.coe_smul, smul_smul, smul_smul, mul_assoc]

theorem binaryEndpointPeriod_smoothWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (positive : 0 < z.im) (position : Fin (n + 2)) :
    binaryEndpointPeriodWt cusp n wt vector.val z position ∈ cusp.smooth := by
  obtain ⟨w, value, _⟩ :=
    binaryEndpointPeriod_realizeWt cusp stages n wt vector fixed z positive position
  rw [← value]
  exact w.property

/-- The scalar weighted realization of the classical endpoint vector, for an integer weight. -/
abbrev endpointScalarWt (cusp : CuspidalRepresentation) (wt : ℤ) (vector : cusp.smooth) :
    BinaryAdelicGL → ℂ → ℂ :=
  cuspScalarWeightedRealizationWt cusp wt vector

/-- **Realization turns the Hilbert Eichler period into the scalar Eichler period.** -/
theorem hilbertLift_binaryEndpointPeriodWt (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (wt : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (positive : 0 < z.im) :
    hilbertLift cusp n (binaryEndpointPeriodWt cusp n wt vector.val z) =
      eichlerPeriod n (cuspScalarWeightedRealizationWt cusp wt vector) z := by
  funext h
  apply hilbertLift_ext
  intro position
  obtain ⟨w, value, realization⟩ :=
    binaryEndpointPeriod_realizeWt cusp stages n wt vector fixed z positive position
  rw [eichlerPeriod, Module.Basis.coord_apply, Module.Basis.repr_sum_self, ← value,
    smoothRealize_of_mem, realization]
  apply intervalIntegral.integral_congr
  intro t member
  have path : clampedPath z t = eichlerPath z t := clampedPath_eqOn z member
  simp only [endpointCoefficientWt, eichlerIntegrand, path, cuspScalarWeightedRealizationWt,
    cuspScalarAffineRealization, Complex.real_smul]
  ring

end TernaryPeriodPolynomials.EvenLevelThree
