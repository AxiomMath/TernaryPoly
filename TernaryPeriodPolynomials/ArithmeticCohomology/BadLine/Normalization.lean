module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Normalization

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization

theorem polynomial_bad_line_normalization : ∀ n : ℕ, 0 < n → ∀ f : HomogeneousPoly n, SymmetricSolution f →
    ∀ F : EdgeChains →ₗ[ℂ] HomogeneousPoly n, IsPolynomialFunctional f F →
    ∀ (τ₀ : rationalLevel → EdgeChains)
      (c₀ : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
    IsPathFamily τ₀ → RealizesPathClass F τ₀ c₀ →
    ∃ (τ : rationalLevel → EdgeChains)
      (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)),
      IsPathFamily τ ∧ RealizesPathClass F τ c ∧ NormalizedBadLine f c ∧
      classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c₀ := by
  intro degree _ polynomial _ functional properties original original_cocycle
    original_paths original_realization
  have normalized_paths := TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths.normalizedPaths_isPathFamily original original_paths
  obtain ⟨changed, changed_realization, changed_class⟩ :=
    TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers.change_path_representative properties original_paths normalized_paths
      original_realization
  exact ⟨TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths.normalizedPaths original, changed, normalized_paths,
    changed_realization, TernaryPeriodPolynomials.PolynomialBadLineNormalization.Normalization.normalized_bad_line properties changed_realization,
    changed_class⟩

end TernaryPeriodPolynomials.PolynomialBadLineNormalization
