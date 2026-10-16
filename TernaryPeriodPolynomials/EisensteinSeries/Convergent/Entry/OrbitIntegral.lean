module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.EndpointPeriodRealize

@[expose] public section


/-!
# Path integrals of the weighted orbit of a finite-level vector

`orbitIntegral_exists`: for a smooth finite-level vector `v` of a cuspidal representation (with the continuous
stages hypothesis of the library) and continuous data `c : ℝ → ℂ`, `τ : ℝ → ℂ` (`τ` in the upper half plane), the
Hilbert-space integral `∫₀¹ c(t) · (Im τ(t))^{k} π(a_{τ(t)}) v dt` is a smooth vector whose realization at `β` is
the scalar integral `∫₀¹ c(t) F(β)(τ(t)) dt` of the weighted scalar realization `F`.  This is the commutation
`realize ∘ ∫ = ∫ ∘ realize` of the library (`commutesOn_of_continuous`) for a general continuous path `τ`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Set
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

theorem upperSection_continuous' (τ : ℝ → ℂ) (hτ : Continuous τ) (hpos : ∀ t, 0 < (τ t).im) :
    Continuous (fun t => binaryUpperSectionMatrix (τ t)) := by
  have him : Continuous (fun t => (τ t).im) := Complex.continuous_im.comp hτ
  have hre : Continuous (fun t => (τ t).re) := Complex.continuous_re.comp hτ
  have hsqrt : Continuous (fun t => Real.sqrt (τ t).im) := him.sqrt
  have hne (t : ℝ) : Real.sqrt (τ t).im ≠ 0 := (Real.sqrt_pos.mpr (hpos t)).ne'
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

/-- **A path integral of the weighted orbit of a finite-level vector is a smooth vector whose realization is the
scalar integral of the realized orbit.** -/
theorem orbitIntegral_exists (cusp : CuspidalRepresentation) (stages : AnalyticScalar.ContinuousStages cusp)
    (hw : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (c : ℝ → ℂ) (τ : ℝ → ℂ) (hc : Continuous c) (hτ : Continuous τ) (hpos : ∀ t, 0 < (τ t).im) :
    ∃ w : cusp.smooth, w.val = ∫ t in (0 : ℝ)..1, c t • cuspWeightedAffineOrbit cusp hw vector.val (τ t) ∧
      ∀ β, cusp.realize w β = ∫ t in (0 : ℝ)..1, c t * cuspScalarWeightedRealization cusp hw vector β (τ t) := by
  have hγ : Continuous (fun t => binaryUpperSectionMatrix (τ t)) := upperSection_continuous' τ hτ hpos
  have hdet : ∀ t, (binaryUpperSectionMatrix (τ t)).det ≠ 0 := fun t =>
    binaryUpperSectionMatrix_invertible _ (hpos t)
  have hφ : Continuous (fun t => c t * (((τ t).im ^ hw : ℝ) : ℂ)) := by
    refine hc.mul (Complex.continuous_ofReal.comp ?_)
    exact (Complex.continuous_im.comp hτ).zpow₀ hw (fun t => Or.inl (hpos t).ne')
  obtain ⟨w, hw1, hw2⟩ := commutesOn_of_continuous cusp stages vector fixed
    (fun t => binaryUpperSectionMatrix (τ t)) (fun t => c t * (((τ t).im ^ hw : ℝ) : ℂ)) hγ hφ hdet 0 1 zero_le_one
  refine ⟨w, ?_, fun β => ?_⟩
  · rw [hw1]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [cuspWeightedAffineOrbit, cuspAffineOrbitVector, realOrbit]
    rw [← Complex.coe_smul, smul_smul]
  · rw [hw2]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization]
    rw [mul_assoc]
    congr 1

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
