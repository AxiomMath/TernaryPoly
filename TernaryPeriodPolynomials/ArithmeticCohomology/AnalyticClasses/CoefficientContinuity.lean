module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.TernaryCoefficientRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.CoefficientDerivatives

@[expose] public section


/-!
# Continuity of the real coefficient action

Every linear functional of the ternary coefficient action of a continuously varying real matrix is
continuous, for the trivial character. Hence on a compact set of matrices it is bounded, uniformly
over the monomial basis.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem substitute_coeff_continuous (polynomial : Poly) (monomial : Fin 3 →₀ ℕ) :
    Continuous (fun M : Matrix (Fin 3) (Fin 3) ℂ => (substitute M polynomial).coeff monomial) := by
  have h := ternary_substitute_coeff_contDiffOn (order := 0) (domain := Set.univ)
    (fun M : Fin 3 → Fin 3 → ℂ => Matrix.of M)
    (fun row column => (contDiff_apply_apply ℝ ℂ row column).contDiffOn)
    polynomial monomial
  have hc : Continuous (fun M : Fin 3 → Fin 3 → ℂ => (substitute (Matrix.of M) polynomial).coeff monomial) :=
    continuousOn_univ.mp h.continuousOn
  exact hc.comp (continuous_id (X := Matrix (Fin 3) (Fin 3) ℂ))

/-- **Continuity of coefficient functionals of the real coefficient action.** -/
theorem realCoefficientComponent_functional_continuous {X : Type*} [TopologicalSpace X] {degree : ℕ}
    (matrices : X → RealGL3) (continuity : Continuous matrices)
    (polynomial : HomogeneousPoly degree) (functional : HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    Continuous (fun point => functional
      (realCoefficientComponent degree trivialCharacter (matrices point) polynomial)) := by
  simp only [realCoefficientComponent_trivial]
  have complexContinuous : Continuous (fun point =>
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) (matrices point) : GL3)) :=
    (continuous_induced_rng.mpr (by
      apply Continuous.prodMk
      · exact (Continuous.matrix_map (Units.continuous_val.comp continuity)
          Complex.continuous_ofReal)
      · change Continuous fun point => MulOpposite.op ((GeneralLinearGroup.map (algebraMap ℝ ℂ)
          (matrices point))⁻¹ : GL3).val
        apply MulOpposite.continuous_op.comp
        have : (fun point => ((GeneralLinearGroup.map (algebraMap ℝ ℂ) (matrices point))⁻¹ : GL3).val) =
            fun point => ((matrices point)⁻¹ : RealGL3).val.map (algebraMap ℝ ℂ) := by
          funext point
          rw [← map_inv]
          rfl
        rw [this]
        exact Continuous.matrix_map (Units.continuous_coe_inv.comp continuity) Complex.continuous_ofReal))
  have spanned := ternaryPolynomialDual_mem_span_coefficients functional
  induction spanned using Submodule.span_induction with
  | mem functional membership =>
    rcases membership with ⟨monomial, rfl⟩
    change Continuous (fun point => (homogeneousAction degree (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (matrices point)) polynomial).val.coeff monomial)
    simp only [homogeneousAction_coe, action_apply, coeff_smul, determinantCharacter,
      MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg_one, smul_eq_mul]
    apply Continuous.mul
    · have hdet : Continuous (fun point =>
          (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) (matrices point))).val) :=
        Continuous.matrix_det (Units.continuous_val.comp complexContinuous)
      exact hdet.inv₀ (fun point => Units.ne_zero _)
    · exact (substitute_coeff_continuous polynomial.val monomial).comp
        (Units.continuous_coe_inv.comp complexContinuous)
  | zero => exact continuous_const
  | add first second _ _ first_smooth second_smooth => exact first_smooth.add second_smooth
  | smul scalar functional _ smooth => exact smooth.const_smul scalar

end TernaryPeriodPolynomials.AnalyticClasses
