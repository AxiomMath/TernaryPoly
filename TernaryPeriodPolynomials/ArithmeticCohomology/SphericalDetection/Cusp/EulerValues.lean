module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.RootBounds
public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.Algebra.Algebra.Spectrum.Pi
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.HalfPlane
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
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
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.RingTheory.Complex
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.Order.ExtrClosure
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspForm_primePowerCoefficient_bound {weight : ℤ}
    {level : Subgroup (GeneralLinearGroup (Fin 2) ℝ)} [level.IsArithmetic]
    (form : CuspForm level weight) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ (place : Nat.Primes) (exponent : ℕ),
      ‖(UpperHalfPlane.qExpansion level.strictWidthInfty form).coeff
          (place.val ^ exponent)‖ ≤
        constant * ((place.val : ℝ) ^ exponent) ^ ((weight : ℝ) / 2) := by
  obtain ⟨constant, positive, bound⟩ :=
    Asymptotics.bound_of_isBigO_nat_atTop (CuspFormClass.qExpansion_isBigO form)
  refine ⟨constant, positive, ?_⟩
  intro place exponent
  have prime_positive : (0 : ℝ) < place.val := by
    exact_mod_cast place.property.pos
  have radius_positive : 0 < ((place.val : ℝ) ^ exponent) ^ ((weight : ℝ) / 2) :=
    Real.rpow_pos_of_pos (pow_pos prime_positive exponent) _
  simpa only [Nat.cast_pow, Real.norm_eq_abs,
    abs_of_nonneg radius_positive.le] using
    bound (x := place.val ^ exponent) (by
      simpa only [Nat.cast_pow] using ne_of_gt radius_positive)

theorem levelOneCuspForm_weight_ge_twelve {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0) : 12 ≤ weight := by
  by_contra small
  have rank_zero := CuspForm.rank_eq_zero_of_weight_lt_twelve (lt_of_not_ge small)
  have : Subsingleton
      (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight) :=
    (Module.rank_zero_iff_of_free (R := ℂ)
      (M := CuspForm
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)).mp rank_zero
  exact nonzero (Subsingleton.elim _ _)

theorem levelOneCuspForm_outerCriticalEulerProducts_ne_zero {weight : ℤ}
    (form : CuspForm
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (nonzero : form ≠ 0)
    (trace determinant first_root second_root : Nat.Primes → ℂ)
    (initial : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ 0) = 1)
    (first : ∀ place : Nat.Primes,
      (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ 1) = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ (exponent + 2)) =
      trace place * (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ (exponent + 1)) -
      determinant place * (UpperHalfPlane.qExpansion
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
        form).coeff (place.val ^ exponent))
    (first_equation : ∀ place,
      first_root place ^ 2 - trace place * first_root place + determinant place = 0)
    (second_equation : ∀ place,
      second_root place ^ 2 - trace place * second_root place + determinant place = 0) :
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first_root ((weight : ℝ) - 2) place.val) *
        (1 - scaledEulerRoot second_root ((weight : ℝ) - 2) place.val))⁻¹) ≠ 0 ∧
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first_root ((weight : ℝ) - 1) place.val) *
        (1 - scaledEulerRoot second_root ((weight : ℝ) - 1) place.val))⁻¹) ≠ 0 := by
  have weight_large : 6 < (weight : ℝ) := by
    have lower : (12 : ℝ) ≤ weight := by
      exact_mod_cast levelOneCuspForm_weight_ge_twelve form nonzero
    linarith
  obtain ⟨constant, _, coefficient_bound⟩ := cuspForm_primePowerCoefficient_bound form
  exact outerCriticalEulerProducts_ne_zero_of_primePowerRecurrences
    (fun place exponent => (UpperHalfPlane.qExpansion
      (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range.strictWidthInfty
      form).coeff (place.val ^ exponent))
    trace determinant first_root second_root (weight : ℝ) (fun _ => constant)
    weight_large initial first recurrence first_equation second_equation coefficient_bound

end TernaryPeriodPolynomials.SphericalDetection.Helpers
