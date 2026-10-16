module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG

@[expose] public section


/-!
# Right invariance of `vhValueFull` under integral finite elements (route (b), step (B2-ii) prerequisite)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a spherical `I.vector`, the value `vhValueFull k h g∞ (X · κ)` with `κ ∈ GL₂(Ẑ)` (embedded into
`GL₂(𝔸_f)`) equals `vhValueFull k h g∞ X`. This is the sphericity absorption on the right of the
2x2 base point, used to pass between the `(Π ι A_t)·g_f` form and the `(Π ι A_t)·(g_f·ι(gp⁻¹))` form.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.SphericalRight

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem vhValueFull_mul_integral_right (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (X : BinaryFiniteGL)
    (κ : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    vhValueFull (-2 * I.halfWeight) h gInf (X * GeneralLinearGroup.map integralEmbedding κ) =
      vhValueFull (-2 * I.halfWeight) h gInf X := by
  have hsph : σ.π (atFinite (GeneralLinearGroup.map integralEmbedding κ)) I.vector.val =
      I.vector.val := I.vector_spherical κ
  have key : σ.π (atFinite (X * GeneralLinearGroup.map integralEmbedding κ)) I.vector.val =
      σ.π (atFinite X) I.vector.val := by
    rw [atFinite_mul', map_mul, Module.End.mul_apply, hsph]
  rw [← vhModel_eq_full_gen I h hform _ gInf, key, vhModel_eq_full_gen I h hform X gInf]

end TernaryPeriodPolynomials.Argument.LatticeCounts.SphericalRight

end
