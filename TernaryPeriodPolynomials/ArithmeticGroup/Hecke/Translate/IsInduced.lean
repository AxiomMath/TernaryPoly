/-
  Clause (a) of `IsSourceCocycle` for the finite-coset Hecke translate: the
  translated coefficient functions are `IsInduced`.  This assembles the
  linear-combination structure (`IsInducedClosure`, `IsInducedAssembly`), the
  right-translation closure (`IsInducedShift`) and the monomial expansion of the
  component representation (`SourceSmoothness.coeff_realCoefficientComponent`).
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedAssembly
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedShift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SourceSmoothness
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.PolyExpansion

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix MvPolynomial
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.TranslateIsInduced

variable {n : ℕ} {D : InducingData n} {side : Side}

/-- One Hecke-representative coefficient function (without the right shift) is
`IsInduced`, by expanding the component representation in monomials and using
the source cocycle's `IsInduced` for each coefficient. -/
theorem repCoeff_isInduced {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (r : RationalGL3) (x : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    IsInduced D side cohomologicalPoint
      (fun g => ((realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
          (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) g)).val).coeff m) := by
  have hfun : (fun g => ((realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
          (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) g)).val).coeff m)
      = fun g => ∑ d ∈ PolyExpansion.degreeMonomials n,
          (componentCharacter D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r) *
            (action (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ)
                (GeneralLinearGroup.map (algebraMap ℚ ℝ) r))
              (MvPolynomial.monomial d 1)).coeff m) *
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) g).val.coeff d := by
    funext g
    rw [SourceSmoothness.coeff_realCoefficientComponent D.chi
        (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
        (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) g) m,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hfun]
  apply IsInducedAssembly.isInduced_finset_sum
  intro d hd
  exact IsInducedClosure.isInduced_smul _
    (hc.1 (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i) d)

/-- **Clause (a) of `IsSourceCocycle` for the Hecke translate.**  Under the
level-normalizer condition, each translated coefficient function is
`IsInduced`. -/
theorem translateSource_isInduced_coeff {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (t : HeckeCorrespondence)
    (hnorm : ∀ r ∈ t.representatives, ∀ k : finiteLevel,
      (rationalFinite r)⁻¹ * k.val * rationalFinite r ∈ finiteLevel)
    (x : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    IsInduced D side cohomologicalPoint
      (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m) := by
  have hfun : (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m)
      = fun g => ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
            (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
              (g * rationalGroup r))).val).coeff m := by
    funext g
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
  rw [hfun]
  apply IsInducedAssembly.isInduced_finset_sum
  intro r hr
  exact IsInducedShift.isInduced_right_shift r (hnorm r hr) (repCoeff_isInduced hc r x m)

end TernaryPeriodPolynomials.HeckeTranslate.TranslateIsInduced

end
