module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Integrand

@[expose] public section


/-!
# Fibre constancy of the global integrand (route (b), step (B2))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

Two facts, both over the finite adeles and with no analysis:

* `gl2_ext`: an element of `GL₂(𝔸_f)` is determined by its local values at all finite places.
* `globalIntegrand_fibre`: if two points `z, z'` of `FiniteAwayThree²` admit local factorisations
  `L_w = P_w κ_w` on a finite set `S` with the same local blocks `blk2 (P_w)` on `S`, then the global
  integrand agrees at `z` and `z'`. The value depends on the point only through the local blocks on `S`.
  This is the fibre constancy used in (B2): the local block on `S` is the Hermite class data.
-/

open Classical Matrix PadicInt MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
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
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- Two elements of `GL₂(𝔸_f)` with the same local values at every finite place are equal. -/
theorem gl2_ext {X Y : GeneralLinearGroup (Fin 2) FiniteAdeles}
    (h : ∀ w : FinitePlace, (GeneralLinearGroup.map (finiteEvaluation w) X).val =
      (GeneralLinearGroup.map (finiteEvaluation w) Y).val) : X = Y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact IsDedekindDomain.FiniteAdeleRing.ext ℚ (fun w => congrFun (congrFun (h w) i) j)

/-- **Fibre constancy.** If `z` and `z'` have local factorisations on `S` with the same local
blocks `blk2 (P_w)`, and integral off `S`, then the global integrand agrees at `z` and `z'`. -/
theorem globalIntegrand_fibre (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace)
    (P κ P' κ' : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (hP' : ∀ w ∈ S, (P' w).val 2 0 = 0 ∧ (P' w).val 2 1 = 0)
    (z z' : FiniteAwayThree × FiniteAwayThree)
    (hS : ∀ w ∈ S, evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w (LfinGLof (awayVal z.1) (awayVal z.2)).val))
    (hS' : ∀ w ∈ S, evM3 w (LfinGLof (awayVal z'.1) (awayVal z'.2)).val = (P' w).val * (κ' w).val)
    (hκ' : ∀ w ∈ S, IntGL3 w (κ' w).val)
    (hL' : ∀ w, w ∉ S → IntGL3 w (evM3 w (LfinGLof (awayVal z'.1) (awayVal z'.2)).val))
    (hblk : ∀ w ∈ S, blk2 (P w).val = blk2 (P' w).val)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    globalIntegrand I Z gInf z = globalIntegrand I Z gInf z' := by
  obtain ⟨X, hX, heq⟩ := globalIntegrand_absorb I h hform S P κ hP z hS hκ hL Z hZ gInf
  obtain ⟨X', hX', heq'⟩ := globalIntegrand_absorb I h hform S P' κ' hP' z' hS' hκ' hL' Z hZ gInf
  have hXX : X = X' := by
    apply gl2_ext
    intro w
    rw [hX w, hX' w]
    split_ifs with hw
    · exact hblk w hw
    · rfl
  have hw : (∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))) =
      ∏ w ∈ S, Complex.exp (expo I * (Real.log ‖pe w (blk2 (P' w).val).det‖ : ℂ)) :=
    Finset.prod_congr rfl (fun w hw' => by rw [hblk w hw'])
  rw [heq, heq', hXX, hw]

end TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst

end
