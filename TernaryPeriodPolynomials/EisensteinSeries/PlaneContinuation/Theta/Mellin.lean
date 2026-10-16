module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.ThetaContinuity
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.Analysis.Meromorphic.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay
open Filter Asymptotics MeasureTheory
open scoped Topology

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaMellin

def pair (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) : WeakFEPair ℂ where
  f := theta realTest finiteTest
  g := theta (FourierTransform.fourier realTest) (FiniteRectangularFourier.transform finiteTest)
  k := 6
  ε := 1
  f₀ := realTest 0 * finiteTest 0
  g₀ := FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0
  hf_int := ScalarThetaContinuity.locallyIntegrableOn realTest finiteTest
    (FiniteSchwartzClosure.continuous_of_periodic _ finiteTest finiteSupport invariant) finiteSupport
  hg_int := ScalarThetaContinuity.locallyIntegrableOn _ _
    (FiniteSchwartzClosure.transform_continuous _ finiteTest finiteSupport invariant)
    (FiniteSchwartzClosure.transform_compactSupport _ finiteTest finiteSupport invariant)
  hk := by norm_num
  hε := one_ne_zero
  h_feq := by
    intro scale positive
    simpa only [one_div, inv_inv, one_mul, smul_eq_mul, Real.rpow_ofNat] using
      poisson realTest latticeScale finiteTest finiteSupport invariant scale⁻¹ (inv_pos.mpr positive)
  hf_top := ScalarThetaContinuity.decay realTest finiteTest
    (FiniteSchwartzClosure.continuous_of_periodic _ finiteTest finiteSupport invariant) finiteSupport
  hg_top := ScalarThetaContinuity.decay _ _
    (FiniteSchwartzClosure.transform_continuous _ finiteTest finiteSupport invariant)
    (FiniteSchwartzClosure.transform_compactSupport _ finiteTest finiteSupport invariant)

theorem pair_meromorphic (data : WeakFEPair ℂ) : Meromorphic data.Λ := by
  have identity : data.Λ = fun parameter => data.Λ₀ parameter - (1 / parameter) * data.f₀ -
      (data.ε / ((data.k : ℂ) - parameter)) * data.g₀ := by
    funext parameter
    have equality := data.Λ₀_eq parameter
    simp only [smul_eq_mul] at equality
    rw [equality]
    ring
  rw [identity]
  intro parameter
  exact ((data.differentiable_Λ₀.analyticAt parameter).meromorphicAt.sub
    ((analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt).mul analyticAt_const.meromorphicAt)).sub
    ((analyticAt_const.meromorphicAt.div
      (analyticAt_const.sub analyticAt_id).meromorphicAt).mul analyticAt_const.meromorphicAt)

theorem hasMellin (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (parameter : ℂ) (right : 6 < parameter.re) :
    HasMellin (fun scale => theta realTest finiteTest scale - realTest 0 * finiteTest 0) parameter
      (pair realTest latticeScale finiteTest finiteSupport invariant |>.Λ parameter) :=
  (pair realTest latticeScale finiteTest finiteSupport invariant).hasMellin right

theorem meromorphic (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) :
    Meromorphic (pair realTest latticeScale finiteTest finiteSupport invariant).Λ :=
  pair_meromorphic _

theorem differentiableAt (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) (parameter : ℂ)
    (nonzero : parameter ≠ 0) (notSix : parameter ≠ 6) :
    DifferentiableAt ℂ (pair realTest latticeScale finiteTest finiteSupport invariant).Λ parameter :=
  (pair realTest latticeScale finiteTest finiteSupport invariant).differentiableAt_Λ
    (Or.inl nonzero) (Or.inl (by simpa only [pair, Complex.ofReal_ofNat] using notSix))

theorem residue_zero (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) :
    Tendsto (fun parameter => parameter * (pair realTest latticeScale finiteTest finiteSupport invariant).Λ parameter)
      (𝓝[≠] 0) (𝓝 (-(realTest 0 * finiteTest 0))) :=
  (pair realTest latticeScale finiteTest finiteSupport invariant).Λ_residue_zero

theorem residue_six (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value) :
    Tendsto (fun parameter => (parameter - 6) * (pair realTest latticeScale finiteTest finiteSupport invariant).Λ parameter)
      (𝓝[≠] 6) (𝓝 (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)) := by
  simpa only [pair, Complex.ofReal_ofNat, smul_eq_mul, one_mul] using
    (pair realTest latticeScale finiteTest finiteSupport invariant).Λ_residue_k

theorem entire_of_zero_constants (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value)
    (zeroValue : realTest 0 * finiteTest 0 = 0)
    (zeroFourier : FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0 = 0) :
    Differentiable ℂ (pair realTest latticeScale finiteTest finiteSupport invariant).Λ :=
  IsStrongFEPair.differentiable_Λ ⟨zeroValue, zeroFourier⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ThetaMellin
