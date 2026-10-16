module

public import TernaryPeriodPolynomials.ModularForm.BinaryCuspOuter
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


noncomputable section
open scoped MatrixGroups
namespace TernaryPoly.BinaryCuspPeriod

/-- Actual full-level cusp forms have finite dimension, by the discriminant equivalence. -/
instance forms_finiteDimensional (d : ℕ) : FiniteDimensional ℂ (Forms d) :=
  FiniteDimensional.of_injective
    (CuspForm.discriminantEquiv (k := (d : ℤ)+2)).toLinearMap
    (CuspForm.discriminantEquiv (k := (d : ℤ)+2)).injective

/-- The exact dimension expected for the odd binary period space. -/
def cuspDimension (d : ℕ) : ℕ :=
  if d<10 then 0 else if d-10 ≡ 2 [MOD 12] then (d-10)/12 else (d-10)/12+1

/-- Mathlib's actual cusp-form dimension, in the polynomial degree convention k=d+2. -/
theorem forms_finrank (d : ℕ) (hd : Even d) :
    Module.finrank ℂ (Forms d)=cuspDimension d := by
  by_cases h : d<10
  · have he := CuspForm.rank_eq_zero_of_weight_lt_twelve
      (k := (d : ℤ)+2) (by omega)
    simpa only [cuspDimension,ite_eq_left h] using Module.finrank_eq_zero_of_rank_eq_zero he
  · have he := (CuspForm.discriminantEquiv (k := (d : ℤ)+2)).finrank_eq
    have hw : (d : ℤ)+2-12=((d-10 : ℕ) : ℤ) := by omega
    rw [hw] at he
    change Module.finrank ℂ (Forms d)=_ at he
    rw [he]
    have hd10 : Even (d-10) := by
      obtain ⟨m,hm⟩ := hd
      exact ⟨m-5,by omega⟩
    have hr := ModularForm.dimension_level_one (d-10) hd10
    have hh := congrArg Cardinal.toNat hr
    simpa only [Module.finrank,cuspDimension,ite_eq_right h,Cardinal.toNat_natCast] using hh

/-- There are no actual cusp forms in polynomial degrees below ten. -/
theorem forms_eq_zero_of_lt_ten {d : ℕ} (hd : d<10) (f : Forms d) : f=0 := by
  have hr := CuspForm.rank_eq_zero_of_weight_lt_twelve (k := (d : ℤ)+2) (by omega)
  have hsub : Subsingleton (Forms d) := Module.subsingleton_of_rank_zero hr
  exact @Subsingleton.elim (Forms d) hsub f 0

end TernaryPoly.BinaryCuspPeriod
