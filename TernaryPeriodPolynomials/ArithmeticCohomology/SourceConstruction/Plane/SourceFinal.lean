module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceInduced

@[expose] public section


/-!
# The plane source cocycle

The two analytic inputs of `PlaneSourceInduced` hold: the radical is real analytic along the Iwasawa
factor and the matrix coefficients of the coefficient representation are real analytic (for a
character trivial on the real ideles). Hence, for every `O(2)`-normalized analytic Levi cocycle `E`
and every `χ` trivial on the integral units, `planeSource D E` is a source cocycle for the plane.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers (invertibleMatrix_val)

namespace TernaryPeriodPolynomials.SourceConstruction

theorem radicalAnalytic (n : ℕ) (χ : RankOneCharacter) : RadicalAnalytic n χ := by
  intro Q μ
  unfold Smooth
  have hmaps : Set.MapsTo (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => A 0)
      {A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0}
      {B : Matrix (Fin 3) (Fin 3) ℝ | B.det ≠ 0} := fun A hA => hA 0
  exact (planeRadical_iwasawaB_contDiffOn n χ Q μ).comp
    (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)).contDiffOn hmaps

theorem coefficientAnalytic (χ : RankOneCharacter)
    (hχ : ∀ u : IntegralAdelesˣ, χ.toMonoidHom (integralAdeleUnit u) = 1) :
    CoefficientAnalytic χ := by
  intro κ μ
  have hreal : ∀ t : ℝˣ, χ.toMonoidHom (realAdeleUnit t) = 1 := character_real_eq_one χ hχ
  unfold Smooth
  have hS : ContDiff ℝ ⊤ (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ =>
      algebraMap ℝ ℂ (A 0).det *
        (substitute ((A 0).map (algebraMap ℝ ℂ)) (MvPolynomial.monomial κ (1 : ℂ))).coeff μ) := by
    refine (contDiff_det_cast.comp
      (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1))).mul ?_
    exact contDiff_coeff_substitute
      (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => (A 0).map (algebraMap ℝ ℂ))
      (fun i j => (contDiff_mapEntry i j).comp
        (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)))
      (MvPolynomial.monomial κ (1 : ℂ)) μ
  refine hS.contDiffOn.congr (fun A hA => ?_)
  have hA0 : (A 0).det ≠ 0 := hA 0
  show (fullCoefficientComponent χ (invertibleMatrix (A 0))⁻¹
      (MvPolynomial.monomial κ (1 : ℂ))).coeff μ = _
  rw [fullCoefficientComponent_inv_apply, componentCharacter_eq_one hreal, one_mul,
    MvPolynomial.coeff_smul, smul_eq_mul, invertibleMatrix_val (A 0) hA0]

/-- **The plane source cocycle.** For `χ` trivial on the integral units and an `O(2)`-normalized
analytic Levi cocycle `E`, `planeSource D E` is a smooth homogeneous two-cocycle with plane-induced
coefficients. -/
theorem planeSource_isSourceCocycle {n : ℕ} (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) :
    IsSourceCocycle D .plane (planeSource D E) :=
  planeSource_isSourceCocycle_of_analytic D E hχ (radicalAnalytic n D.chi)
    (coefficientAnalytic D.chi hχ)

end TernaryPeriodPolynomials.SourceConstruction
