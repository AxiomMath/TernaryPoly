/-
  Clause (b) transport for a single representative/coefficient term: the
  variable change `x ↦ (map r)⁻¹ x` together with the right shift
  `g ↦ g · rationalGroup r` preserves `HasSmoothCuspLift`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SnocSmoothness
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.CombineGL

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.HasSmoothCuspLiftShift

variable {n : ℕ} {D : InducingData n} {side : Side}

theorem hasSmoothCuspLift_shift {c : SourceCochain n} {r : RationalGL3} {d : Fin 3 →₀ ℕ}
    (hd : HasSmoothCuspLift D side cohomologicalPoint
      (fun x g => (c x g).val.coeff d)) :
    HasSmoothCuspLift D side cohomologicalPoint
      (fun x g => (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
           (g * rationalGroup r)).val.coeff d) := by
  intro a
  obtain ⟨v₀, hv₁, hv₂⟩ := hd (a * rationalGroup r)
  refine ⟨fun x => v₀ (Fin.snoc (fun j : Fin 3 =>
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x (Fin.castSucc j))
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x (Fin.last 3) *
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹)⁻¹)), ?_, ?_⟩
  · exact SnocSmoothness.smooth_snoc_conj (fun x' => (v₀ x').val) hv₁
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹)
  · intro x A
    rw [hv₂ _ A]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, inv_inv]
    show normPower (GeneralLinearGroup.det A)
          (-binaryInductionExponent n side cohomologicalPoint) *
        (c (fun i =>
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x (Fin.castSucc i))
          (binaryLevi side A * ((a * rationalGroup r) * atInfinity
            ((GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x (Fin.last 3) *
              GeneralLinearGroup.map (algebraMap ℚ ℝ) r)))).val.coeff d =
      normPower (GeneralLinearGroup.det A)
          (-binaryInductionExponent n side cohomologicalPoint) *
        (c (fun i =>
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x (Fin.castSucc i))
          (binaryLevi side A * (a * atInfinity (x (Fin.last 3))) * rationalGroup r)).val.coeff d
    congr 1
    congr 1
    rw [mul_assoc, ← HeckeInvariance.atInfinity_mul_rationalGroup (x (Fin.last 3)) r]
    group

end TernaryPeriodPolynomials.HeckeTranslate.HasSmoothCuspLiftShift

end
