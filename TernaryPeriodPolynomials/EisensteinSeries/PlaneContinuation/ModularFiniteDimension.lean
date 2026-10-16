module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Evaluation
public import Mathlib.NumberTheory.ModularForms.NormTrace
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Basic
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
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
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
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
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.SetTheory.Cardinal.ENNReal
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Tactic.Ring.NamePowerVars
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.AtTopBotIxx
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ShrinkingLemma
public import Mathlib.Topology.WithTopology

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ModularFiniteDimension

noncomputable def functionLinear (group : Subgroup (GL (Fin 2) ℝ)) (weight : ℤ) [group.HasDetOne] :
    ModularForm group weight →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun form := form
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem functionLinear_injective (group : Subgroup (GL (Fin 2) ℝ)) (weight : ℤ) [group.HasDetOne] :
    Function.Injective (functionLinear group weight) := by
  intro first second equality
  exact DFunLike.coe_injective equality

theorem norm_zero_at {group fullGroup : Subgroup (GL (Fin 2) ℝ)} (weight : ℤ)
    [group.IsFiniteRelIndex fullGroup] [fullGroup.HasDetPlusMinusOne]
    (form : ModularForm group weight) (argument : UpperHalfPlane) (vanishing : form argument = 0) :
    ModularForm.norm fullGroup form argument = 0 := by
  classical
  let _ : Fintype (fullGroup ⧸ group.subgroupOf fullGroup) := Fintype.ofFinite _
  rw [ModularForm.coe_norm]
  simp only [Finset.prod_apply]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟦(1 : fullGroup)⟧ : fullGroup ⧸ group.subgroupOf fullGroup))
  rw [SlashInvariantForm.quotientFunc_mk]
  simpa using vanishing

/-- Finiteness descends along a finite-index subgroup using the norm and finite evaluations. -/
theorem finiteDimensional_of_norm {group fullGroup : Subgroup (GL (Fin 2) ℝ)} (weight : ℤ)
    [group.IsFiniteRelIndex fullGroup] [group.HasDetOne] [fullGroup.HasDetOne]
    [FiniteDimensional ℂ (ModularForm fullGroup (weight * (Nat.card (fullGroup ⧸ group.subgroupOf fullGroup) : ℤ)))] :
    FiniteDimensional ℂ (ModularForm group weight) := by
  classical
  obtain ⟨samples, determining⟩ := FiniteEvaluation.exists_samples
    (functionLinear fullGroup (weight * (Nat.card (fullGroup ⧸ group.subgroupOf fullGroup) : ℤ)))
    (functionLinear_injective _ _)
  let evaluation : ModularForm group weight →ₗ[ℂ] (↥samples → ℂ) :=
    { toFun := fun form point => form point.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective evaluation
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro form vanishing
  have normZero : ModularForm.norm fullGroup form = 0 := by
    apply determining
    intro argument membership
    apply norm_zero_at
    exact congrFun vanishing ⟨argument, membership⟩
  apply DFunLike.coe_injective
  exact (ModularForm.norm_eq_zero_iff fullGroup form).mp normZero

theorem finiteDimensional {group : Subgroup (GL (Fin 2) ℝ)} (weight : ℤ)
    [group.IsFiniteRelIndex (Matrix.SpecialLinearGroup.mapGL ℝ (R := ℤ)).range] [group.HasDetOne] :
    FiniteDimensional ℂ (ModularForm group weight) :=
  finiteDimensional_of_norm (fullGroup := (Matrix.SpecialLinearGroup.mapGL ℝ (R := ℤ)).range) weight

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ModularFiniteDimension
