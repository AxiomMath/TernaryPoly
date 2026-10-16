module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.RealizeIntervalIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointPeriod

@[expose] public section


/-!
# Scalar realization of the Hilbert-space Eichler periods

`SphericalDetection.Helpers.binaryEndpointPeriod` is a Bochner integral in the Hilbert space of
the cuspidal representation. Its coordinates are smooth vectors whose scalar realizations are the
scalar Eichler integrals of the realized orbit. This is the commutation `realize ∘ ∫ = ∫ ∘ realize`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Set
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.AnalyticClasses

/-- The straight path from `i` to `z`, clamped to the parameter interval. -/
def clampedPath (z : ℂ) (t : ℝ) : ℂ :=
  Complex.I + ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ)) • (z - Complex.I)

theorem clampedPath_im_pos (z : ℂ) (hz : 0 < z.im) (t : ℝ) : 0 < (clampedPath z t).im :=
  upperHalfPlane_straightPath ⟨z, hz⟩ (projIcc (0 : ℝ) 1 zero_le_one t).property

theorem clampedPath_continuous (z : ℂ) : Continuous (clampedPath z) := by
  unfold clampedPath
  exact continuous_const.add
    (((continuous_subtype_val.comp continuous_projIcc)).smul continuous_const)

theorem clampedPath_eqOn (z : ℂ) :
    EqOn (clampedPath z) (fun t : ℝ => Complex.I + t • (z - Complex.I)) (uIcc 0 1) := by
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  simp [clampedPath, projIcc_of_mem zero_le_one ht]

theorem upperSection_continuous (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t => binaryUpperSectionMatrix (clampedPath z t)) := by
  have him : Continuous (fun t => (clampedPath z t).im) :=
    Complex.continuous_im.comp (clampedPath_continuous z)
  have hre : Continuous (fun t => (clampedPath z t).re) :=
    Complex.continuous_re.comp (clampedPath_continuous z)
  have hsqrt : Continuous (fun t => Real.sqrt (clampedPath z t).im) := him.sqrt
  have hne (t : ℝ) : Real.sqrt (clampedPath z t).im ≠ 0 :=
    (Real.sqrt_pos.mpr (clampedPath_im_pos z hz t)).ne'
  unfold binaryUpperSectionMatrix
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    first
    | exact hsqrt
    | exact hre.div hsqrt hne
    | exact continuous_const
    | exact continuous_const.div hsqrt hne

theorem upperSection_det_ne_zero (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    (binaryUpperSectionMatrix (clampedPath z t)).det ≠ 0 := by
  rw [binaryUpperSectionMatrix_det _ (clampedPath_im_pos z hz t)]
  exact one_ne_zero

/-- The scalar coefficient of the Eichler integrand. -/
def endpointCoefficient (degree : ℕ) (halfWeight : ℤ) (z : ℂ) (position : Fin (degree + 2))
    (t : ℝ) : ℂ :=
  (z - Complex.I) * ((binaryWeightBasis (degree + 1)).coord position
      (binaryPointPower (degree + 1) (clampedPath z t)) *
    (((clampedPath z t).im ^ halfWeight : ℝ) : ℂ))

theorem endpointCoefficient_continuous (degree : ℕ) (halfWeight : ℤ) (z : ℂ) (hz : 0 < z.im)
    (position : Fin (degree + 2)) : Continuous (endpointCoefficient degree halfWeight z position) := by
  unfold endpointCoefficient
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · have hpoly : Continuous (fun point : ℂ => (binaryWeightBasis (degree + 1)).coord position
        (binaryPointPower (degree + 1) point)) :=
      continuous_iff_continuousAt.mpr fun point =>
        (binaryPointPower_functional_analytic (degree + 1)
          ((binaryWeightBasis (degree + 1)).coord position) point).continuousAt
    exact hpoly.comp (clampedPath_continuous z)
  · apply Complex.continuous_ofReal.comp
    exact (Complex.continuous_im.comp (clampedPath_continuous z)).zpow₀ halfWeight
      (fun t => Or.inl (clampedPath_im_pos z hz t).ne')

/-- **Scalar realization of the Eichler period.** Every coordinate of the Hilbert-space Eichler
period of a smooth finite-level vector is a smooth vector whose realization is the scalar Eichler
integral of the realized orbit. -/
theorem binaryEndpointPeriod_realize (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (degree : ℕ) (halfWeight : ℤ)
    (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (z : ℂ) (hz : 0 < z.im) (position : Fin (degree + 2)) :
    ∃ w : cusp.smooth, w.val = binaryEndpointPeriod cusp degree halfWeight vector.val z position ∧
      ∀ h, cusp.realize w h = ∫ t in (0 : ℝ)..1, endpointCoefficient degree halfWeight z position t *
        cusp.realize vector (h * atInfinity (invertibleMatrix
          (binaryUpperSectionMatrix (clampedPath z t)))) := by
  obtain ⟨w, hw, hr⟩ := commutesOn_of_continuous cusp stages vector fixed
    (fun t => binaryUpperSectionMatrix (clampedPath z t)) (endpointCoefficient degree halfWeight z position)
    (upperSection_continuous z hz) (endpointCoefficient_continuous degree halfWeight z hz position)
    (upperSection_det_ne_zero z hz) 0 1 zero_le_one
  refine ⟨w, ?_, hr⟩
  rw [hw]
  have hint := binaryEndpointPeriod_integrable cusp degree halfWeight vector.val z hz
  have key : (binaryEndpointPeriod cusp degree halfWeight vector.val z) position =
      ∫ t in (0 : ℝ)..1, ((z - Complex.I) • binaryEndpointHolomorphicForm cusp degree halfWeight vector.val
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
  simp only [binaryEndpointHolomorphicForm, cuspWeightedAffineOrbit, cuspAffineOrbitVector,
    endpointCoefficient, realOrbit]
  rw [← Complex.coe_smul, smul_smul, smul_smul, mul_assoc]

end TernaryPeriodPolynomials.AnalyticClasses
