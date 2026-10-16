module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Finite.CoefficientDetection
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.SpecificLimits.RCLike
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def modularFormEvaluation (group : Subgroup (GL (Fin 2) ℝ)) [group.HasDetOne]
    (weight : ℤ) (point : UpperHalfPlane) : ModularForm group weight →ₗ[ℂ] ℂ where
  toFun form := form point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finite_dimensional_modular_evaluation_detection (group : Subgroup (GL (Fin 2) ℝ))
    [group.HasDetOne] (weight : ℤ) [FiniteDimensional ℂ (ModularForm group weight)] :
    ∃ points : Finset UpperHalfPlane, ∀ form : ModularForm group weight,
      (∀ point ∈ points, form point = 0) → form = 0 := by
  apply finite_evaluation_detection (modularFormEvaluation group weight)
  intro form zero
  apply DFunLike.ext
  intro point
  exact zero point

theorem modular_norm_zero_at (source target : Subgroup (GL (Fin 2) ℝ))
    [source.HasDetOne] [target.HasDetOne] [source.IsFiniteRelIndex target]
    (weight : ℤ) (form : ModularForm source weight) (point : UpperHalfPlane) (zero : form point = 0) :
    ModularForm.norm target form point = 0 := by
  classical
  let : Fintype (target ⧸ source.subgroupOf target) := Fintype.ofFinite _
  change (ModularForm.norm target form : UpperHalfPlane → ℂ) point = 0
  rw [ModularForm.coe_norm, Finset.prod_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk (1 : target)))
  rw [SlashInvariantForm.quotientFunc_mk]
  simpa using zero

theorem modular_finite_dimensional_of_norm (source target : Subgroup (GL (Fin 2) ℝ))
    [source.HasDetOne] [target.HasDetOne] [source.IsFiniteRelIndex target] (weight : ℤ)
    [FiniteDimensional ℂ (ModularForm target (weight * (Nat.card (target ⧸ source.subgroupOf target) : ℤ)))] :
    FiniteDimensional ℂ (ModularForm source weight) := by
  classical
  obtain ⟨points, detects⟩ := finite_dimensional_modular_evaluation_detection target
    (weight * (Nat.card (target ⧸ source.subgroupOf target) : ℤ))
  have detects_source (form : ModularForm source weight) (zero : ∀ point ∈ points, form point = 0) : form = 0 := by
    have norm_zero := detects (ModularForm.norm target form)
      (fun point member => modular_norm_zero_at source target weight form point (zero point member))
    have function_zero := (ModularForm.norm_eq_zero_iff target form).mp norm_zero
    exact DFunLike.coe_injective function_zero
  let evaluation : ModularForm source weight →ₗ[ℂ] (points → ℂ) :=
    LinearMap.pi (fun point => modularFormEvaluation source weight point.val)
  apply FiniteDimensional.of_injective evaluation
  intro first second equal
  apply sub_eq_zero.mp
  apply detects_source
  intro point member
  have values := congrFun equal (⟨point, member⟩ : points)
  change first point = second point at values
  change first point - second point = 0
  exact sub_eq_zero.mpr values

theorem modular_finite_dimensional_of_finite_index (group : Subgroup (GL (Fin 2) ℝ))
    [group.HasDetOne]
    [group.IsFiniteRelIndex (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range]
    (weight : ℤ) : FiniteDimensional ℂ (ModularForm group weight) :=
  modular_finite_dimensional_of_norm group
    (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
