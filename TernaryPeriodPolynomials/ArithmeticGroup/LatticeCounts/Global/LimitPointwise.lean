module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.Integrand
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitBoundG
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitPlane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Global.LimitLocal

@[expose] public section


/-!
# Global limit: the pointwise bound of the global integrand on `U_S`

On `U_S` the global integrand is bounded by `Cc · ∏_{w∈S} (max 1 (max ‖s_w‖ ‖t_w‖))^(-k/2)` where `(s_w, t_w)` are the `S`-local
coordinates of `z` read in `ℚ_p`, `Cc = ‖normPower(det Z) b‖ · C` and `C` is the uniform cusp-form bound; this is
`GlobalIntegrand.globalIntegrand_absorb` with the per-place data of `GlobalLimitPlane.local_plane_level`.

Formalized by Claude Sonnet 5.5.
-/

open Matrix MeasureTheory GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.Spectral.LevelOneHecke (levelOne)
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellIntegralLift
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinGlobal
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.LfinBlockMulti
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitLocal
open TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg (vhValueFull)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitBoundG (norm_vhValueFull_le)
open TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeDictionary (Fh)

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPointwise

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The real exponent `b = k/2`. -/
def bexp (I : EichlerInput σ n) : ℝ := ((-2 * I.halfWeight : ℤ) : ℝ) / 2

theorem expo_eq (I : EichlerInput σ n) : expo I = ((bexp I : ℝ) : ℂ) := by
  unfold expo bexp
  push_cast
  rfl

/-- Uniform bound on the full value for every `g∞` with `det g∞ ≠ 0`: on the positive component by `norm_vhValueFull_le`, on the negative one
`vhValueNeg` is `F_h` at a positive-determinant matrix (`det_neg_pos`). -/
theorem norm_vhValueFull_le_ne (k : ℤ) (h : CuspForm levelOne k) (C : ℝ)
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val → ‖Fh k ⇑h g‖ ≤ C)
    (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0) (X : BinaryFiniteGL) :
    ‖vhValueFull k h gInf X‖ ≤ C := by
  by_cases hpos : 0 < (Matrix.GeneralLinearGroup.det gInf).val
  · exact norm_vhValueFull_le k h C hC gInf hpos X
  · have hneg : (Matrix.GeneralLinearGroup.det gInf).val < 0 := lt_of_le_of_ne (not_lt.1 hpos) hg
    unfold vhValueFull
    rw [ite_eq_right hpos]
    exact hC _ (TernaryPeriodPolynomials.Argument.LatticeCounts.ModelComparisonNeg.det_neg_pos gInf hneg X _)

/-- The local weight at `w` of the pair of local coordinates. -/
def phiW (I : EichlerInput σ n) (w : FinitePlace) (a b : w.adicCompletion ℚ) : ℝ :=
  phiR (Rat.HeightOneSpectrum.primesEquiv w).val (bexp I) (pe w a, pe w b)

theorem norm_local_factor (I : EichlerInput σ n) (w : FinitePlace) (a b : w.adicCompletion ℚ)
    (x : ℝ) (hx : x = (max 1 (max ‖pe w a‖ ‖pe w b‖))⁻¹) :
    ‖Complex.exp (expo I * (Real.log x : ℂ))‖ = phiW I w a b := by
  have hm : 0 < max 1 (max ‖pe w a‖ ‖pe w b‖) := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [expo_eq, Complex.norm_exp, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm, hx,
    ← Real.rpow_def_of_pos (inv_pos.2 hm), Real.inv_rpow hm.le, ← Real.rpow_neg hm.le]
  rfl

/-- **The pointwise bound of the global integrand on `U_S`.** -/
theorem norm_globalIntegrand_le (I : EichlerInput σ n) (h : CuspForm levelOne (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (gInf : BinaryRealGL) (hg : (Matrix.GeneralLinearGroup.det gInf).val ≠ 0) {C : ℝ}
    (hC : ∀ g : GL (Fin 2) ℝ, 0 < (Matrix.GeneralLinearGroup.det g).val → ‖Fh (-2 * I.halfWeight) ⇑h g‖ ≤ C)
    (Z : BinaryFiniteGL) (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (S : Finset FinitePlace) {z : FiniteAwayThree × FiniteAwayThree} (hz : z ∈ UregionS S) :
    ‖globalIntegrand I Z gInf z‖ ≤
      (‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)‖ * C) *
        ∏ w ∈ S, phiW I w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2)) := by
  choose P κ hP20 hP21 hfac hκ hnorm using
    fun w : FinitePlace => local_plane_level w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2))
  obtain ⟨X, -, heq⟩ := globalIntegrand_absorb I h hform S P κ (fun w _ => ⟨hP20 w, hP21 w⟩) z
    (fun w _ => by rw [evM3_LfinGLof]; exact hfac w) (fun w _ => hκ w)
    (fun w hw => intGL3_LfinGLof_of_mem hz w hw) Z hZ gInf
  rw [heq, norm_mul, norm_mul, norm_prod]
  have hprod : ∏ w ∈ S, ‖Complex.exp (expo I * (Real.log ‖pe w (blk2 (P w).val).det‖ : ℂ))‖ =
      ∏ w ∈ S, phiW I w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2)) :=
    Finset.prod_congr rfl fun w _ => norm_local_factor I w _ _ _ (hnorm w)
  rw [hprod]
  have hv := norm_vhValueFull_le_ne (-2 * I.halfWeight) h C hC gInf hg (X * Z)
  have hphi : 0 ≤ ∏ w ∈ S, phiW I w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2)) :=
    Finset.prod_nonneg fun w _ => phiR_nonneg _ _ _
  calc (∏ w ∈ S, phiW I w _ _) * ‖normPower _ (expo I)‖ * ‖vhValueFull (-2 * I.halfWeight) h gInf (X * Z)‖
      ≤ (∏ w ∈ S, phiW I w (finiteEvaluation w (awayVal z.1)) (finiteEvaluation w (awayVal z.2))) *
          ‖normPower (Norm.finiteAdeleUnit (GeneralLinearGroup.det Z)) (expo I)‖ * C := by gcongr
    _ = _ := by ring

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitPointwise
