module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.PointwiseMulti
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinGlobal

@[expose] public section


/-!
# The global integrand at a finite base point (route (b), step (B2-ii) interface)

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a base point `Z ∈ GL₂(𝔸_f)` (decision (a): integral at every place, including `3`) and a pair
`z = (s, t)` of points of `FiniteAwayThree`, the global integrand is the smooth-vector value at the
plane section of `L(s, t) · blkGL Z`, where `L(s, t) = LfinGLof (awayVal s) (awayVal t)`.

Pointwise absorption: if the local factorisations `L_w = P_w κ_w` hold on a finite set `S` of
places and `L_w` is integral off `S`, then the global integrand equals the product over `S` of the
local exponentials, times `normPower(det Z)`, times `vhValueFull` at the block `X · Z`, where `X` has
local values `blk2 (P_w)` on `S` and `1` off `S`. This is `PointwiseMulti.pointwise_multi` at
`L = LfinGLof (awayVal z.1) (awayVal z.2)`, with no new analysis.
-/

open Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalGL3
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.RightTranslation
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.PointwiseMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBlockG
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinScalar
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparison
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)

open Classical

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The global exponent `b = k/2` with `k = -2 · halfWeight`. -/
def expo (I : EichlerInput σ n) : ℂ := ((-2 * I.halfWeight : ℤ) : ℂ) / 2

/-- The global integrand at a finite base point `Z`: the smooth-vector value at the plane section of
`L(s,t) · blkGL Z`, at the real place `g∞`. -/
def globalIntegrand (I : EichlerInput σ n) (Z : BinaryFiniteGL) (gInf : BinaryRealGL)
    (z : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 (expo I)
    (LfinGLof (awayVal z.1) (awayVal z.2) * blkGL Z) I.vector.val) (atInfinity gInf)

/-- **Pointwise absorption.** On a point `z` whose local factorisations hold on `S` and whose
`L(z)` is integral off `S`, the global integrand is the local scalar times `vhValueFull` at `X · Z`,
where `X` has local values `blk2 (P_w)` on `S` and `1` off `S`. -/
theorem globalIntegrand_absorb (I : EichlerInput σ n)
    (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace)
    (P κ : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (z : FiniteAwayThree × FiniteAwayThree)
    (hS : ∀ w ∈ S, evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val))
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    ∃ X : GeneralLinearGroup (Fin 2) FiniteAdeles,
      (∀ w, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
        if w ∈ S then blk2 (P w).val else 1) ∧
      globalIntegrand I Z gInf z =
        ((∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) *
          normPower (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)) *
          vhValueFull (-2 * I.halfWeight) h gInf (X * Z) := by
  obtain ⟨X, hX, heq⟩ := pointwise_multi I h hform S P κ hP
    (LfinGLof (awayVal z.1) (awayVal z.2)) hS hκ hL Z hZ (expo I) gInf
  exact ⟨X, hX, heq⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand

end
