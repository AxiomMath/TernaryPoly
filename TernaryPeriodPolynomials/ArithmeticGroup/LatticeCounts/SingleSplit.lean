module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.FibreConst
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Local.Plane
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitTotal
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitFibreG
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.AwayThreePlaceSplitting

@[expose] public section


/-!
# Single-place pointwise identity (route (b), step (B4-single))

Formalized by Claude Haiku 5.5, with Claude Opus 5.5.

For a finite place `q ≠ 3` and local coordinates `(s, t) ∈ ℚ_q²`, the point of `FiniteAwayThree²`
with value `(s, t)` at `q` and `0` elsewhere has global integrand equal to the literal shell
integrand `shellIntegrandG q (s, t)`. The proof uses:

* `plane_factor_all`: every `LstR (ψ s) (ψ t)` factors as `P κ` with `P` of mirror-parabolic shape and
  `κ ∈ GL₃(O_q)` (from `zp2_or_shell`, `local_plane_zero`, `local_plane_shell`);
* `smooth_fibre_general`: the same fibre argument as `globalIntegrand_fibre`, for arbitrary `GL₃(𝔸_f)`
  elements instead of points of `FiniteAwayThree²`;
* `intGL3_LfinGLof_of_mem`, `intGL3_one`, and the evaluation lemmas for `ιGL3`.
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
open TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalIntegrand
open TernaryPeriodPolynomials.Argument.LatticeCounts.FibreConst
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitGL
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitPlaneG (psiV_mem_OS)
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitTotal (zp2_or_shell)
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalPlane
open TernaryPeriodPolynomials.Argument.LatticeCounts.ShellLitFibreG
open TernaryPeriodPolynomials.Argument.LatticeCounts.SeedK0

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.SingleSplit

variable {σ : CuspidalRepresentation} {n : ℕ}

/-- The value of `(LstV v (s,t))` as a matrix over `K_v`. -/
theorem LstV_val_eq (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    (LstV v (s, t)).val = LstR (psiV v s) (psiV v t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LstV, GeneralLinearGroup.map, LstGL, Lst, LstR]

/-- Evaluation of a point supported at `q` at `q` is the given value. -/
theorem eval_atPlace_self (q : FinitePlace) (hq : q ≠ placeThree) (u : q.adicCompletion ℚ) :
    finiteEvaluation q (awayVal (finiteAwayThreeAtPlace q hq u)) = u :=
  finiteAtPlaceScalar_same q u

/-- Evaluation of a point supported at `q` away from `q` is zero. -/
theorem eval_atPlace_ne (q : FinitePlace) (hq : q ≠ placeThree) (u : q.adicCompletion ℚ)
    (w : FinitePlace) (hw : w ≠ q) :
    finiteEvaluation w (awayVal (finiteAwayThreeAtPlace q hq u)) = 0 :=
  finiteAtPlaceScalar_away q u w hw

/-- A pair of points supported at `q` lies in `U_{q}`. -/
theorem atPlace_mem_UregionS (q : FinitePlace) (hq : q ≠ placeThree)
    (s t : q.adicCompletion ℚ) :
    (finiteAwayThreeAtPlace q hq s, finiteAwayThreeAtPlace q hq t) ∈
      UregionS ({q} : Finset FinitePlace) := by
  intro w hw
  have hwq : w ≠ q := by simpa using hw
  rw [eval_atPlace_ne q hq s w hwq, eval_atPlace_ne q hq t w hwq]
  exact ⟨(OS w).zero_mem, (OS w).zero_mem⟩

/-- Every `LstR (ψ s) (ψ t)` factors as `P κ` with `P` of mirror-parabolic shape and `κ ∈ GL₃(O_v)`. -/
theorem plane_factor_all (v : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime]
    (s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) :
    ∃ P κ : GeneralLinearGroup (Fin 3) (v.adicCompletion ℚ),
      P.val 2 0 = 0 ∧ P.val 2 1 = 0 ∧ LstR (psiV v s) (psiV v t) = P.val * κ.val ∧
        IntGL3 v κ.val := by
  rcases zp2_or_shell (p := (Rat.HeightOneSpectrum.primesEquiv v).val) (s, t) with hz | ⟨r, hr⟩
  · have hz' : ‖s‖ ≤ 1 ∧ ‖t‖ ≤ 1 := hz
    obtain ⟨P, κ, hP20, hP21, hfac, hκ, -⟩ :=
      local_plane_zero v (psiV_mem_OS v ⟨s, hz'.1⟩) (psiV_mem_OS v ⟨t, hz'.2⟩)
    exact ⟨P, κ, hP20, hP21, hfac, hκ⟩
  · obtain ⟨P, κ, hP20, hP21, hfac, hκ, -⟩ := local_plane_shell v (r + 1) hr
    exact ⟨P, κ, hP20, hP21, hfac, hκ⟩

/-- Extend a local element at `q` to a family indexed by all finite places (identity elsewhere). -/
def extend1 (q : FinitePlace) (x : GeneralLinearGroup (Fin 3) (q.adicCompletion ℚ)) :
    ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ) :=
  fun w => if h : w = q then h ▸ x else 1

theorem extend1_self (q : FinitePlace) (x : GeneralLinearGroup (Fin 3) (q.adicCompletion ℚ)) :
    extend1 q x q = x := by
  simp [extend1]

/-- **Fibre equality for general `GL₃(𝔸_f)` elements.** Two elements whose local factorisations
agree (same blocks `blk2 (P_w)` on `S`) and which are integral off `S` have the same smooth value
against `blkGL Z`. This is `globalIntegrand_fibre` with the point replaced by an arbitrary element. -/
theorem smooth_fibre_general (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (S : Finset FinitePlace)
    (P κ P' κ' : ∀ w : FinitePlace, GeneralLinearGroup (Fin 3) (w.adicCompletion ℚ))
    (hP : ∀ w ∈ S, (P w).val 2 0 = 0 ∧ (P w).val 2 1 = 0)
    (hP' : ∀ w ∈ S, (P' w).val 2 0 = 0 ∧ (P' w).val 2 1 = 0)
    (L L' : GeneralLinearGroup (Fin 3) FiniteAdeles)
    (hS : ∀ w ∈ S, evM3 w L.val = (P w).val * (κ w).val)
    (hκ : ∀ w ∈ S, IntGL3 w (κ w).val)
    (hL : ∀ w, w ∉ S → IntGL3 w (evM3 w L.val))
    (hS' : ∀ w ∈ S, evM3 w L'.val = (P' w).val * (κ' w).val)
    (hκ' : ∀ w ∈ S, IntGL3 w (κ' w).val)
    (hL' : ∀ w, w ∉ S → IntGL3 w (evM3 w L'.val))
    (hblk : ∀ w ∈ S, blk2 (P w).val = blk2 (P' w).val)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) :
    smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 (expo I)
        (L * blkGL Z) I.vector.val) (atInfinity gInf) =
      smoothReal σ (finitePlaneVector σ GeneralEisenstein.trivialCharacter 0 (expo I)
        (L' * blkGL Z) I.vector.val) (atInfinity gInf) := by
  obtain ⟨X, hX, heq⟩ := pointwise_multi I h hform S P κ hP L hS hκ hL Z hZ (expo I) gInf
  obtain ⟨X', hX', heq'⟩ := pointwise_multi I h hform S P' κ' hP' L' hS' hκ' hL' Z hZ (expo I) gInf
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

/-- **Single-place pointwise identity.** The global integrand at the point with value `(s,t)` at `q`
and `0` elsewhere equals the literal shell integrand at `(s,t)`. -/
theorem globalIntegrand_atPlace_eq_shell (I : EichlerInput σ n)
    (h : CuspForm TernaryPeriodPolynomials.Spectral.LevelOneHecke.levelOne
      (-2 * I.halfWeight))
    (hform : (⇑h : UpperHalfPlane → ℂ) = cuspScalarWeightedLinear σ I.halfWeight 1 I.vector)
    (q : FinitePlace) [Fact (Rat.HeightOneSpectrum.primesEquiv q).val.Prime] (hq : q ≠ placeThree)
    (Z : BinaryFiniteGL)
    (hZ : ∀ w : FinitePlace, IntGL w (GeneralLinearGroup.map (finiteEvaluation w) Z).val)
    (gInf : BinaryRealGL) (s t : ℚ_[(Rat.HeightOneSpectrum.primesEquiv q).val]) :
    globalIntegrand I Z gInf
        (finiteAwayThreeAtPlace q hq (psiV q s), finiteAwayThreeAtPlace q hq (psiV q t)) =
      shellIntegrandG q I Z gInf (s, t) := by
  obtain ⟨P0, κ0, hP20, hP21, hfac, hκ0⟩ := plane_factor_all q s t
  have hz := atPlace_mem_UregionS q hq (psiV q s) (psiV q t)
  unfold globalIntegrand shellIntegrandG
  refine smooth_fibre_general I h hform ({q} : Finset FinitePlace)
    (extend1 q P0) (extend1 q κ0) (extend1 q P0) (extend1 q κ0)
    ?_ ?_ _ (ιGL3 q (LstV q (s, t))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ Z hZ gInf
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact ⟨hP20, hP21⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact ⟨hP20, hP21⟩
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [evM3_LfinGLof, eval_atPlace_self, eval_atPlace_self, hfac, extend1_self, extend1_self]
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact hκ0
  · intro w hw
    exact intGL3_LfinGLof_of_mem hz w hw
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [ιGL3_val, evM3_ιMat3_self, LstV_val_eq, hfac, extend1_self, extend1_self]
  · intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    rw [extend1_self]
    exact hκ0
  · intro w hw
    have hwq : w ≠ q := by simpa using hw
    rw [ιGL3_val, evM3_ιMat3_ne q w hwq]
    exact intGL3_one w
  · intro w _
    rfl

end TernaryPeriodPolynomials.Argument.LatticeCounts.SingleSplit

end
