/-
  Clause (b) of `IsSourceCocycle` for the finite-coset Hecke translate: the
  translated (multi-variable) coefficient functions satisfy `HasSmoothCuspLift`.
  Assembled from the single-representative shift (`HasSmoothCuspLiftShift`), the
  monomial expansion of the component representation, and closure of
  `HasSmoothCuspLift` under finite linear combinations.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.HasSmoothCuspLiftShift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInduced

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TranslateHasSmoothCuspLift

variable {n : ℕ} {D : InducingData n} {side : Side}

theorem translateSource_hasSmoothCuspLift {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (t : HeckeCorrespondence) (m : Fin 3 →₀ ℕ) :
    HasSmoothCuspLift D side cohomologicalPoint
      (fun x g => (HeckeInvariance.translateSource D t c x g).val.coeff m) := by
  have hfun : (fun x g => (HeckeInvariance.translateSource D t c x g).val.coeff m)
      = fun x g => ∑ r ∈ t.representatives, ∑ d ∈ PolyExpansion.degreeMonomials n,
          (componentCharacter D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
            (action (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ)
                (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
              (MvPolynomial.monomial d 1)).coeff m) *
          (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r)).val.coeff d := by
    funext x g
    rw [HeckeInvariance.translateSource]
    rw [show (∑ r ∈ t.representatives, realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r))).val
        = ∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r))).val
        from map_sum (Submodule.subtype (homogeneousSubmodule (Fin 3) ℂ n)) _ _]
    rw [show (∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r))).val).coeff m
        = ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi
            (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r))).val).coeff m
        from map_sum (SourceSmoothness.coeffLM m) _ _]
    apply Finset.sum_congr rfl
    intro r hr
    rw [SourceSmoothness.coeff_realCoefficientComponent D.chi
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
          (g * rationalGroup r)) m, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hfun]
  apply HasSmoothCuspLiftClosure.hasSmoothCuspLift_finset_sum
  intro r hr
  apply HasSmoothCuspLiftClosure.hasSmoothCuspLift_finset_sum
  intro d hd
  exact HasSmoothCuspLiftClosure.hasSmoothCuspLift_smul _
    (HasSmoothCuspLiftShift.hasSmoothCuspLift_shift (hc.2.1 d))

end TernaryPeriodPolynomials.HeckeTranslate.TranslateHasSmoothCuspLift

end
