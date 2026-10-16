/-
  `IsInduced D side s` is stable under right translation by a rational group
  element `g ↦ g * rationalGroup r`, under the level-normalizer condition.
  This is the last ingredient turning the source cocycle's `IsInduced` clauses
  into those of the Hecke translate.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SourceSmoothness

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.IsInducedShift

variable {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}

theorem isInduced_right_shift (r : RationalGL3)
    (hnorm : ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    {f : AdelicGL → ℂ} (hf : IsInduced D side s f) :
    IsInduced D side s (fun z => f (z * rationalGroup r)) := by
  have hdet : (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val).det ≠ 0 :=
    GeneralLinearGroup.det_ne_zero _
  have hstep : ∀ x : RealGL3,
      atInfinity x * rationalGroup r =
        rationalGroup r * atInfinity
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r) :=
    fun x => HeckeInvariance.atInfinity_mul_rationalGroup x r
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G
    have hsrc := hf.1 (G * rationalGroup r)
    have hcomp := SmoothTransport.Smooth.comp_conj
      (F := fun x' : Fin 1 → RealGL3 => f ((G * rationalGroup r) * atInfinity (x' 0)))
      hsrc (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) hdet
    refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
    simp only []
    congr 1
    calc G * atInfinity (x₁ 0) * rationalGroup r
        = G * (atInfinity (x₁ 0) * rationalGroup r) := by group
      _ = G * (rationalGroup r * atInfinity
            ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) := by rw [hstep]
      _ = (G * rationalGroup r) * atInfinity
            (invertibleMatrix ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) * (x₁ 0).val *
              ((((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val)⁻¹))) := by
          rw [← SourceSmoothness.invertibleMatrix_conj_eq r (x₁ 0)]
          group
  · intro k G
    show f (G * atFinite k.val * rationalGroup r) = f (G * rationalGroup r)
    rw [mul_assoc, HeckeInvariance.atFinite_mul_rationalGroup, ← mul_assoc]
    exact hf.2.1 ⟨_, hnorm k⟩ (G * rationalGroup r)
  · intro a
    obtain ⟨v₀, hv₁, hv₂⟩ := hf.2.2.1 (a * rationalGroup r)
    refine ⟨fun x₁ : Fin 1 → RealGL3 => v₀ (fun _ : Fin 1 =>
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
          GeneralLinearGroup.map (algebraMap ℚ ℝ) r), ?_, ?_⟩
    · have hcomp := SmoothTransport.Smooth.comp_conj
        (F := fun x' : Fin 1 → RealGL3 => (v₀ x').val) hv₁
        (((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹).val) hdet
      refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
      simp only []
      refine congrArg (Submodule.subtype D.cusp.smooth) ?_
      refine congrArg v₀ ?_
      funext i
      fin_cases i
      exact (SourceSmoothness.invertibleMatrix_conj_eq r (x₁ 0)).symm
    · intro x₁ A
      show D.cusp.realize (v₀ (fun _ : Fin 1 =>
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r)) A =
          normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n side s) *
            f (binaryLevi side A * (a * atInfinity (x₁ 0)) * rationalGroup r)
      rw [hv₂ (fun _ : Fin 1 => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
            GeneralLinearGroup.map (algebraMap ℚ ℝ) r) A]
      simp only []
      congr 1
      congr 1
      calc binaryLevi side A * ((a * rationalGroup r) * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
          = binaryLevi side A * (a * (rationalGroup r * atInfinity
              ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * (x₁ 0) *
                GeneralLinearGroup.map (algebraMap ℚ ℝ) r))) := by group
        _ = binaryLevi side A * (a * (atInfinity (x₁ 0) * rationalGroup r)) := by rw [← hstep]
        _ = binaryLevi side A * (a * atInfinity (x₁ 0)) * rationalGroup r := by group
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (planeUnipotent a b * G * rationalGroup r) = f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.1 a b (G * rationalGroup r)
      · intro t G
        show f (planeLevi 1 t * G * rationalGroup r) =
          D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s) *
            f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.2.1 t (G * rationalGroup r)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2.2 (G * rationalGroup r)
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (lineUnipotent a b * G * rationalGroup r) = f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.1 a b (G * rationalGroup r)
      · intro t G
        show f (lineLevi t 1 * G * rationalGroup r) =
          D.chi.toMonoidHom t * normPower t (2 * inductionExponent .line s) *
            f (G * rationalGroup r)
        rw [mul_assoc]; exact hf.2.2.2.2.1 t (G * rationalGroup r)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2.2 (G * rationalGroup r)

end TernaryPeriodPolynomials.HeckeTranslate.IsInducedShift

end
