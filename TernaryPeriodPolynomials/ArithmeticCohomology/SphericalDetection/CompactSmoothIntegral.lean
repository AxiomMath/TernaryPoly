module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SmoothIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem contDiffOn_integral_compact_measure
    {P X E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {measure : Measure X} [IsFiniteMeasure measure] {order : ℕ∞}
    {values : P → X → E} {domain : Set P} {support : Set X}
    (domain_open : IsOpen domain) (support_compact : IsCompact support)
    (supported : ∀ᵐ argument ∂measure, argument ∈ support)
    (regular : ContDiffOn ℝ order (Function.uncurry values) (domain ×ˢ Set.univ)) :
    ContDiffOn ℝ order (fun parameter => ∫ argument, values parameter argument ∂measure) domain := by
  obtain ⟨radius, positive, subset⟩ := support_compact.isBounded.subset_ball_lt 0 (0 : X)
  let cutoff : ContDiffBump (0 : X) := ⟨radius, radius + 1, positive, by linarith⟩
  let cut : P → X → E := fun parameter argument => cutoff argument • values parameter argument
  have cut_regular : ContDiffOn ℝ order (Function.uncurry cut) (domain ×ˢ Set.univ) :=
    (cutoff.contDiff.comp contDiff_snd).contDiffOn.smul regular
  have integral_regular := contDiffOn_integral_compact_support (measure := measure)
    domain_open cutoff.hasCompactSupport (values := cut)
    (fun _ argument _ outside => by
      change cutoff argument • _ = 0
      rw [image_eq_zero_of_notMem_tsupport outside, zero_smul]) cut_regular
  apply integral_regular.congr
  intro parameter _
  apply integral_congr_ae
  filter_upwards [supported] with argument member
  change values parameter argument = cutoff argument • values parameter argument
  rw [cutoff.one_of_mem_closedBall (Metric.ball_subset_closedBall (subset member)), one_smul]

theorem contDiffOn_integral_compact_image
    {P X Y E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {measure : Measure X} [IsFiniteMeasure measure] {order : ℕ∞}
    {values : P → Y → E} {domain : Set P} (embedding : X → Y) (embedding_continuous : Continuous embedding)
    (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ order (Function.uncurry values) (domain ×ˢ Set.univ)) :
    ContDiffOn ℝ order (fun parameter => ∫ argument, values parameter (embedding argument) ∂measure) domain := by
  have compact := isCompact_range embedding_continuous
  have supported := ae_map_mem_range compact.measurableSet
    embedding_continuous.measurable.aemeasurable (μ := measure)
  have integral_regular := contDiffOn_integral_compact_measure domain_open compact supported regular
  apply integral_regular.congr
  intro parameter member
  have continuous : Continuous (values parameter) :=
    regular.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨member, Set.mem_univ _⟩)
  exact (integral_map embedding_continuous.measurable.aemeasurable continuous.aestronglyMeasurable).symm

theorem contDiffOn_intervalIntegral
    {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {order : ℕ∞}
    {values : P → ℝ → E} {domain : Set P} (domain_open : IsOpen domain)
    (regular : ContDiffOn ℝ order (Function.uncurry values) (domain ×ˢ Set.univ))
    (left right : ℝ) (ordered : left ≤ right) :
    ContDiffOn ℝ order (fun parameter => ∫ argument in left..right, values parameter argument) domain := by
  have supported : ∀ᵐ argument ∂(volume.restrict (Set.Ioc left right)), argument ∈ Set.Icc left right := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with argument member
    exact ⟨member.1.le, member.2⟩
  have regular := contDiffOn_integral_compact_measure domain_open isCompact_Icc supported regular
  simpa only [intervalIntegral.integral_of_le ordered] using regular

end TernaryPeriodPolynomials.SphericalDetection.Helpers
