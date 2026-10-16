module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


/-!
# Weight-generic scalar realization

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins of `cuspScalarWeightedRealization` and `cuspScalarWeightedLinear` for an integer rotation
weight `wt`, where the factor `point.im ^ halfWeight` is replaced by `wtFactor wt point.im`.  The
bridge lemmas identify the new definitions with the old ones at even weight `wt = 2 * halfWeight`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

def cuspScalarWeightedRealizationWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point : ℂ) : ℂ :=
  wtFactor wt point.im • cuspScalarAffineRealization cusp vector base point

theorem cuspScalarWeightedRealization_IWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    cuspScalarWeightedRealizationWt cusp wt vector base Complex.I = cusp.realize vector base := by
  rw [cuspScalarWeightedRealizationWt, Complex.I_im, wtFactor_one, one_smul,
    cuspScalarAffineRealization_I]

theorem cuspScalarWeightedRealization_analyticWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    AnalyticOnNhd ℝ (cuspScalarWeightedRealizationWt cusp wt vector base)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  have positive_im : 0 < Complex.imCLM point := positive
  have factor : AnalyticAt ℝ (wtFactor wt ∘ ⇑Complex.imCLM) point :=
    (analyticAt_wtFactor wt positive_im).comp (Complex.imCLM.analyticAt point)
  exact factor.smul (cuspScalarAffineRealization_analytic cusp vector base point positive)

theorem cuspScalarWeightedRealization_nonzeroWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) :
    ∃ base : BinaryAdelicGL,
      cuspScalarWeightedRealizationWt cusp wt vector base Complex.I ≠ 0 := by
  classical
  by_contra no_base
  push Not at no_base
  apply nonzero
  apply cusp.injective
  ext base
  simpa only [cuspScalarWeightedRealization_IWt, map_zero, Pi.zero_apply] using no_base base

theorem cuspScalarWeightedRealization_boundWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (base : BinaryAdelicGL) (point : UpperHalfPlane),
      ‖cuspScalarWeightedRealizationWt cusp wt vector base point‖ ≤
        wtFactor wt point.im * bound := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  refine ⟨bound, (norm_nonneg _).trans (bounded 1), ?_⟩
  intro base point
  rw [cuspScalarWeightedRealizationWt, norm_smul, Real.norm_eq_abs]
  change |wtFactor wt point.im| * ‖cuspScalarAffineRealization cusp vector base point‖ ≤
    wtFactor wt point.im * bound
  rw [abs_of_pos (wtFactor_pos wt point.im)]
  exact mul_le_mul_of_nonneg_left (bounded _) (wtFactor_pos wt point.im).le

theorem cuspScalarWeightedRealization_zero_at_inftyWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (negative : wt < 0) (vector : cusp.smooth) (base : BinaryAdelicGL) :
    UpperHalfPlane.IsZeroAtImInfty
      (fun point : UpperHalfPlane => cuspScalarWeightedRealizationWt cusp wt vector base point) := by
  obtain ⟨bound, _, bounded⟩ := cuspScalarWeightedRealization_boundWt cusp wt vector
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro epsilon epsilon_positive
  have limit : Filter.Tendsto (fun value : ℝ => wtFactor wt value * bound) Filter.atTop
      (nhds 0) := by
    simpa only [zero_mul] using (tendsto_wtFactor_atTop_of_neg negative).mul_const bound
  obtain ⟨cutoff, small⟩ :=
    Filter.eventually_atTop.mp (limit.eventually (gt_mem_nhds epsilon_positive))
  exact ⟨cutoff, fun point point_large =>
    (bounded base point).trans (small point.im point_large).le⟩

theorem cuspScalarWeightedRealization_det_normalizeWt (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (wt : ℤ) (vector : cusp.smooth) (matrix : BinaryRealGL)
    (positive : 0 < matrix.val.det) (point : ℂ) :
    cuspScalarWeightedRealizationWt cusp wt vector (atInfinity matrix) point =
      cuspScalarWeightedRealizationWt cusp wt vector
        (atInfinity (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))) point := by
  unfold cuspScalarWeightedRealizationWt cuspScalarAffineRealization
  congr 1
  conv_lhs => rw [← binaryDetNormalizedMatrix_recover matrix positive]
  rw [atInfinity_mul, mul_assoc, atInfinity_scalar, cusp.central,
    central_positive _ (Real.sqrt_pos.mpr positive), one_mul]

def cuspScalarWeightedLinearWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (base : BinaryAdelicGL) : cusp.smooth →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun vector point := cuspScalarWeightedRealizationWt cusp wt vector base point
  map_add' first second := by
    funext point
    simp only [cuspScalarWeightedRealizationWt, cuspScalarAffineRealization, map_add,
      Pi.add_apply, smul_add]
  map_smul' scalar vector := by
    funext point
    simp only [cuspScalarWeightedRealizationWt, cuspScalarAffineRealization, map_smul,
      Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

theorem cuspFiniteRationalSlash_weightedWt (cusp : CuspidalRepresentation)
    (rational : BinaryRationalGL) (wt : ℤ) (vector : cusp.smooth) (point : UpperHalfPlane) :
    cuspScalarWeightedLinearWt cusp wt 1 (cuspFiniteRationalSlash cusp rational vector) point =
      cuspScalarWeightedRealizationWt cusp wt vector
        (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)) point := by
  change wtFactor wt point.im •
    cusp.realize (cuspFiniteRationalSlash cusp rational vector)
      (1 * atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) = _
  rw [one_mul, cuspFiniteRationalSlash_realize, atInfinity_mul]
  rfl

theorem cuspScalarWeightedRealizationWt_two_mul (cusp : CuspidalRepresentation) (h : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point : ℂ) (positive : 0 < point.im) :
    cuspScalarWeightedRealizationWt cusp (2 * h) vector base point =
      cuspScalarWeightedRealization cusp h vector base point := by
  rw [cuspScalarWeightedRealizationWt, cuspScalarWeightedRealization, wtFactor_even h positive]

theorem cuspScalarWeightedRealizationWt_two_mul_upperHalfPlane (cusp : CuspidalRepresentation)
    (h : ℤ) (vector : cusp.smooth) (base : BinaryAdelicGL) (point : UpperHalfPlane) :
    cuspScalarWeightedRealizationWt cusp (2 * h) vector base (point : ℂ) =
      cuspScalarWeightedRealization cusp h vector base (point : ℂ) :=
  cuspScalarWeightedRealizationWt_two_mul cusp h vector base (point : ℂ) point.im_pos

theorem cuspScalarWeightedLinearWt_two_mul (cusp : CuspidalRepresentation) (h : ℤ)
    (base : BinaryAdelicGL) (vector : cusp.smooth) :
    cuspScalarWeightedLinearWt cusp (2 * h) base vector =
      cuspScalarWeightedLinear cusp h base vector := by
  funext point
  change cuspScalarWeightedRealizationWt cusp (2 * h) vector base (point : ℂ) =
    cuspScalarWeightedRealization cusp h vector base (point : ℂ)
  exact cuspScalarWeightedRealizationWt_two_mul_upperHalfPlane cusp h vector base point

end TernaryPeriodPolynomials.EvenLevelThree
