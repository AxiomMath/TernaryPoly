module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinScalar
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG

@[expose] public section


/-!
# Pointwise multi-place identity on the global section (route (b), step (B2c))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a global factorisation `L * blkGL gf` with local plane data `P w` on `S` and integral off `S`,
the smoothed section at `atInfinity gInf` equals the explicit scalar times `vhValueFull` at the
2x2 base `X * gf`, where `X` has local values `blk2 (P w)` on `S` and `1` off `S`. This is
`block_multi_scalar` (which absorbs the integral part by sphericity) followed by
`smoothReal_smul_of_mem` and `vhModel_eq_full_gen`. Restriction (a): `gf` integral at every place.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlane
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti

variable {σ : CuspidalRepresentation} {n : ℕ}

theorem pointwise_multi (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (L : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w L.val))
    (gf : GeneralLinearGroup (Fin 2) FiniteAdeles)
    (hgf : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) gf).val)
    (b : ℂ) (gInf : BinaryRealGL) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then blk2 (P w).val else 1) ∧
      smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 b (L * blkGL gf)
          I.vector.val) (atInfinity gInf) =
        ((∏ w ∈ S, Complex.exp (b * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) *
          normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit
            (GeneralLinearGroup.det gf)) b) *
          vhValueFull (-2 * I.halfWeight) h gInf (X * gf) := by
  obtain ⟨X, hX, heq⟩ := block_multi_scalar S P κ hP L hS hκ hL gf hgf b
    (vec := I.vector.val) (fun kk => I.vector_spherical kk)
  refine ⟨X, hX, ?_⟩
  rw [heq, smoothReal_smul_of_mem σ _ (σ.smooth_stable _ _ I.vector.property), smul_eq_mul,
    vhModel_eq_full_gen I h hform (X * gf) gInf]

end TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti

end
