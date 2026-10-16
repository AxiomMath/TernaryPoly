module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.ShiftIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem analyticAt_intervalIntegral_local (function : P × ℝ → F) (point : P) (center : ℝ)
    (analytic : AnalyticAt ℝ function (point, center)) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ left right,
      left ∈ Set.Icc (center - radius) (center + radius) →
      right ∈ Set.Icc (center - radius) (center + radius) → left ≤ right →
      AnalyticAt ℝ (fun parameter => ∫ sample in left..right, function (parameter, sample)) point := by
  obtain ⟨series, outerRadius, expansion⟩ := analytic
  obtain ⟨small, small_positive, small_bound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (lt_min expansion.r_pos (by norm_num : (0 : ENNReal) < 1))
  have small_pos : 0 < small := by exact_mod_cast small_positive
  let radius : NNReal := small / 4
  have positive : 0 < radius := by dsimp [radius]; positivity
  have twice_small : radius + radius < small := by
    dsimp [radius]
    exact_mod_cast (show (small : ℝ) / 4 + (small : ℝ) / 4 < small by
      have : (0 : ℝ) < small := small_pos
      linarith)
  have inside : (radius : ENNReal) + radius < outerRadius := by
    rw [← ENNReal.coe_add]
    exact (ENNReal.coe_lt_coe.mpr twice_small).trans (lt_of_lt_of_le small_bound (min_le_left _ _))
  refine ⟨radius, positive, ?_⟩
  intro left right left_inside right_inside ordered
  let : CompactSpace (Set.Icc left right) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume.restrict (Set.Icc left right)) := ⟨by simp [Measure.restrict_apply, Real.volume_Icc]⟩
  let measure : Measure (Set.Icc left right) :=
    Measure.comap Subtype.val (volume.restrict (Set.Icc left right))
  let offset (sample : Set.Icc left right) : P × ℝ := (0, sample.val - center)
  have bounded (sample : Set.Icc left right) : ‖offset sample‖₊ ≤ radius := by
    have sample_inside : sample.val ∈ Set.Icc (center - radius) (center + radius) :=
      ⟨left_inside.1.trans sample.property.1, sample.property.2.trans right_inside.2⟩
    have absolute : |sample.val - center| ≤ (radius : ℝ) := abs_le.mpr ⟨by linarith [sample_inside.1], by linarith [sample_inside.2]⟩
    have norm_bound : ‖offset sample‖ ≤ (radius : ℝ) := by
      simp only [offset, Prod.norm_def, norm_zero, Real.norm_eq_abs]
      exact max_le radius.coe_nonneg absolute
    exact_mod_cast norm_bound
  have average := analyticAt_weighted_shift_integral measure function series (point, center) outerRadius expansion
    offset (by fun_prop) (fun _ => (1 : ℂ)) continuous_const radius radius positive inside bounded
  have embedding : AnalyticAt ℝ (fun parameter : P => (parameter, center)) point :=
    analyticAt_id.prod analyticAt_const
  have composed := average.comp (f := fun parameter : P => (parameter, center)) (x := point) embedding
  have integral_eq (parameter : P) :
      (∫ sample : Set.Icc left right, (1 : ℂ) • function ((parameter, center) + offset sample) ∂measure) =
        ∫ sample in left..right, function (parameter, sample) := by
    simp only [offset, Prod.mk_add_mk, add_zero, add_sub_cancel, one_smul]
    dsimp only [measure]
    rw [integral_subtype_comap measurableSet_Icc (fun sample => function (parameter, sample)),
      Measure.restrict_restrict measurableSet_Icc, Set.inter_self,
      integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ordered]
  simpa only [Function.comp_def, integral_eq] using composed

theorem analyticAt_intervalIntegral_nearby (function : P × ℝ → F) (point : P) (center : ℝ)
    (analytic : AnalyticAt ℝ function (point, center)) :
    ∀ᶠ endpoint in nhds center,
      AnalyticAt ℝ (fun parameter => ∫ sample in center..endpoint, function (parameter, sample)) point := by
  obtain ⟨radius, positive, local_analytic⟩ := analyticAt_intervalIntegral_local function point center analytic
  filter_upwards [Metric.ball_mem_nhds center positive] with endpoint member
  have distance : |endpoint - center| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using member
  have endpoint_inside : endpoint ∈ Set.Icc (center - radius) (center + radius) :=
    ⟨by linarith [(abs_lt.mp distance).1], by linarith [(abs_lt.mp distance).2]⟩
  have center_inside : center ∈ Set.Icc (center - radius) (center + radius) := ⟨by linarith, by linarith⟩
  rcases le_total center endpoint with ordered | ordered
  · exact local_analytic center endpoint center_inside endpoint_inside ordered
  · have reverse := (local_analytic endpoint center endpoint_inside center_inside ordered).neg
    change AnalyticAt ℝ (fun parameter => -(∫ sample in endpoint..center, function (parameter, sample))) point at reverse
    simpa only [intervalIntegral.integral_symm endpoint center] using reverse

theorem analyticAt_intervalIntegral (function : P × ℝ → F) (point : P) (domain : Set P)
    (domain_open : IsOpen domain) (point_mem : point ∈ domain)
    (continuous : ∀ parameter ∈ domain, Continuous (fun sample => function (parameter, sample)))
    (analytic : ∀ center : ℝ, AnalyticAt ℝ function (point, center)) (left right : ℝ) :
    AnalyticAt ℝ (fun parameter => ∫ sample in left..right, function (parameter, sample)) point := by
  let property (endpoint : ℝ) :=
    AnalyticAt ℝ (fun parameter => ∫ sample in left..endpoint, function (parameter, sample)) point
  have local_equivalence (center : ℝ) : ∀ᶠ endpoint in nhds center, property endpoint ↔ property center := by
    filter_upwards [analyticAt_intervalIntegral_nearby function point center (analytic center)] with endpoint increment
    have addition : ∀ᶠ parameter in nhds point,
        (∫ sample in left..center, function (parameter, sample)) +
          (∫ sample in center..endpoint, function (parameter, sample)) =
            ∫ sample in left..endpoint, function (parameter, sample) := by
      filter_upwards [domain_open.mem_nhds point_mem] with parameter member
      exact intervalIntegral.integral_add_adjacent_intervals
        ((continuous parameter member).intervalIntegrable left center)
        ((continuous parameter member).intervalIntegrable center endpoint)
    constructor
    · intro endpoint_analytic
      have difference := endpoint_analytic.sub increment
      apply difference.congr
      filter_upwards [addition] with parameter equality
      exact (eq_sub_iff_add_eq.mpr equality).symm
    · intro center_analytic
      exact (center_analytic.add increment).congr addition
  have open_good : IsOpen {endpoint | property endpoint} := by
    apply isOpen_iff_mem_nhds.mpr
    intro endpoint member
    filter_upwards [local_equivalence endpoint] with nearby equivalence
    exact equivalence.mpr member
  have open_bad : IsOpen {endpoint | ¬property endpoint} := by
    apply isOpen_iff_mem_nhds.mpr
    intro endpoint member
    filter_upwards [local_equivalence endpoint] with nearby equivalence
    exact fun regular => member (equivalence.mp regular)
  have clopen : IsClopen {endpoint | property endpoint} := ⟨isOpen_compl_iff.mp open_bad, open_good⟩
  have nonempty : Set.Nonempty {endpoint | property endpoint} := by
    refine ⟨left, ?_⟩
    change AnalyticAt ℝ (fun parameter => ∫ sample in left..left, function (parameter, sample)) point
    simpa only [intervalIntegral.integral_same] using (analyticAt_const (𝕜 := ℝ) (v := (0 : F)) (x := point))
  have full := clopen.eq_univ nonempty
  have member : right ∈ {endpoint | property endpoint} := by rw [full]; trivial
  exact member

end TernaryPeriodPolynomials.SphericalDetection.Helpers
