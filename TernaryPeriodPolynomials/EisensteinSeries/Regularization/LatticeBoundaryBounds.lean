module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.IntegerRowSummability
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.RayPoleCriterion
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integer_rows_tsum_rpow_bound (dimension : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ exponent : ℝ, exponent < -(dimension : ℝ) →
      (∑' row : Fin dimension → ℤ, ‖(fun index => (row index : ℝ))‖ ^ exponent) ≤
        constant ^ exponent * ∑' size : ℕ, (size : ℝ) ^ ((dimension : ℝ) - 1 + exponent) := by
  let lattice : Submodule ℤ (Fin dimension → ℝ) :=
    Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin dimension)))
  have member (row : Fin dimension → ℤ) : (fun index => (row index : ℝ)) ∈ lattice := by
    rw [← (Pi.basisFun ℝ (Fin dimension)).sum_repr (fun index => (row index : ℝ))]
    apply Submodule.sum_mem
    intro index _
    simp only [Pi.basisFun_repr, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem lattice (row index) (Submodule.subset_span ⟨index, rfl⟩)
  let embedding : (Fin dimension → ℤ) → lattice := fun row => ⟨_, member row⟩
  have injective : Function.Injective embedding := by
    intro first second equality
    funext index
    exact Int.cast_injective (congrFun (congrArg Subtype.val equality) index)
  have rank : Module.finrank ℤ lattice = dimension := by
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card ((Pi.basisFun ℝ (Fin dimension)).linearIndependent.restrict_scalars' (R := ℤ))
  refine ⟨ZLattice.tsumNormRPowBound lattice, ZLattice.tsumNormRPowBound_pos lattice, ?_⟩
  intro exponent small
  have lattice_small : exponent < -(Module.finrank ℤ lattice : ℝ) := by rw [rank]; exact small
  calc
    _ ≤ ∑' vector : lattice, ‖vector‖ ^ exponent :=
      Summable.tsum_le_tsum_of_inj embedding injective
        (fun vector _ => Real.rpow_nonneg (norm_nonneg vector) exponent) (fun _ => le_rfl)
        (integer_rows_summable_rpow dimension exponent small)
        (ZLattice.summable_norm_rpow lattice exponent lattice_small)
    _ ≤ _ := by simpa only [rank] using ZLattice.tsum_norm_rpow_le lattice exponent lattice_small

theorem planeFlagIntegerRow_tsum_rpow_bound :
    ∃ constant : ℝ, 0 < constant ∧ ∀ exponent : ℝ, exponent < -3 →
      (∑' flag : Flags .plane, ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ exponent) ≤
        constant ^ exponent * ∑' size : ℕ, (size : ℝ) ^ (2 + exponent) := by
  obtain ⟨constant, positive, bound⟩ := integer_rows_tsum_rpow_bound 3
  refine ⟨constant, positive, ?_⟩
  intro exponent small
  calc
    _ ≤ ∑' row : Fin 3 → ℤ, ‖(fun index => (row index : ℝ))‖ ^ exponent :=
      Summable.tsum_le_tsum_of_inj planeFlagIntegerRow planeFlagIntegerRow_injective
        (fun row _ => Real.rpow_nonneg (norm_nonneg _) exponent) (fun _ => le_rfl)
        (planeFlagIntegerRow_summable exponent small)
        (integer_rows_summable_rpow 3 exponent (by norm_num; exact small))
    _ ≤ _ := by
      simpa only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num] using
        bound exponent (by norm_num; exact small)

theorem nat_neg_rpow_tsum_zeta (exponent : ℝ) (large : 1 < exponent) :
    ((∑' size : ℕ, (size : ℝ) ^ (-exponent) : ℝ) : ℂ) = riemannZeta (exponent : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using large), Complex.ofReal_tsum]
  apply tsum_congr
  intro size
  rw [Complex.ofReal_cpow (Nat.cast_nonneg size), Complex.ofReal_neg, Complex.cpow_neg, one_div]
  rfl

theorem nat_rpow_boundary_residue :
    Tendsto (fun displacement : ℝ => displacement *
      ∑' size : ℕ, (size : ℝ) ^ (-1 - displacement))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have complex_limit := riemannZeta_residue_one.comp (positive_real_ray_tendsto 1)
  have real_limit := Complex.continuous_re.continuousAt.tendsto.comp complex_limit
  apply real_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with displacement positive
  change 0 < displacement at positive
  have series := nat_neg_rpow_tsum_zeta (1 + displacement) (by linarith)
  have exponent : -(1 + displacement) = -1 - displacement := by ring
  rw [exponent] at series
  simp only [Function.comp_def, add_sub_cancel_left]
  rw [show (1 : ℂ) + (displacement : ℂ) = ((1 + displacement : ℝ) : ℂ) by push_cast; rfl,
    ← series, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem planeFlagIntegerRow_boundary_bound :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      displacement * (∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) ≤ bound := by
  obtain ⟨constant, positive, bound⟩ := planeFlagIntegerRow_tsum_rpow_bound
  have factor_continuous : Continuous (fun displacement : ℝ => constant ^ (-3 - displacement)) := by
    simp only [Real.rpow_def_of_pos positive]
    exact (continuous_const.mul (continuous_const.sub continuous_id)).rexp
  have factor_limit : Tendsto (fun displacement : ℝ => constant ^ (-3 - displacement))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (constant ^ (-3 : ℝ))) := by
    simpa only [sub_zero] using (factor_continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  have product_limit := factor_limit.mul nat_rpow_boundary_residue
  simp only [mul_one] at product_limit
  have upper := product_limit.eventually (gt_mem_nhds (lt_add_one (constant ^ (-3 : ℝ))))
  refine ⟨constant ^ (-3 : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [self_mem_nhdsWithin, upper] with displacement displacement_positive upper
  change 0 < displacement at displacement_positive
  have estimate := mul_le_mul_of_nonneg_left (bound (-3 - displacement) (by linarith)) displacement_positive.le
  have exponent : 2 + (-3 - displacement) = -1 - displacement := by ring
  rw [exponent] at estimate
  calc
    _ ≤ displacement * (constant ^ (-3 - displacement) *
        ∑' size : ℕ, (size : ℝ) ^ (-1 - displacement)) := estimate
    _ = constant ^ (-3 - displacement) *
        (displacement * ∑' size : ℕ, (size : ℝ) ^ (-1 - displacement)) := by ring
    _ ≤ _ := upper.le

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
