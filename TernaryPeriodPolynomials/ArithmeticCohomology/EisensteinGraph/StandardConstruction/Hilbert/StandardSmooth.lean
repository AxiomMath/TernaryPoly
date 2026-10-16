module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.TaylorIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.SmoothCriterion
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.NormPower

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandardSmooth

theorem right_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → RealGL3 =>
      HilbertStandard.value data parameter function induced (argument * atInfinity (real 0))) :=
  RightOrbitAnalyticity.smooth_of_analyticAt_one (HilbertStandard.value data parameter function induced)
    (HilbertTaylorIntegral.value_analyticAt_one data parameter function induced halfPlane) argument

theorem lineLevi_atInfinity (binary : BinaryRealGL) :
    atInfinity (lineLevi 1 binary) = lineLevi 1 (atInfinity binary) := by
  apply InducedContinuity.adelic_ext
  · rw [InducedContinuity.realGroup_atInfinity]
    change lineLevi 1 binary = GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) _
    rw [LineDecomposition.map_lineLevi, map_one]
    rfl
  · rw [InducedContinuity.finiteGroup_atInfinity]
    change 1 = GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) _
    rw [LineDecomposition.map_lineLevi, map_one]
    change 1 = lineLevi 1 (1 : BinaryFiniteGL)
    exact (lineLeviHom FiniteAdeles).map_one.symm

theorem normalizedReal_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    Smooth (fun real : Fin 1 → BinaryRealGL =>
      HilbertUniformCompact.normalizedValue data parameter function induced (atInfinity (real 0)) argument) := by
  have lineSmooth := RightOrbitAnalyticity.left_line_smooth
    (HilbertStandard.value data parameter function induced)
    (right_smooth data parameter function induced halfPlane)
    (HilbertStandard.value_finite_invariant data parameter function induced) argument
  simp_rw [lineLevi_atInfinity] at lineSmooth
  exact (SmoothNormPower.real_power_smooth (0 : Fin 1)
    (-binaryInductionExponent degree .line parameter)).smul lineSmooth

/-- The actual full standard integral is a smooth vector throughout the
absolute convergence half-plane, in the statement's literal analytic sense. -/
theorem value_mem_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    HilbertStandard.value data parameter function induced argument ∈ data.cusp.smooth :=
  (HilbertSmoothCriterion.smooth_iff_normalizedReal data parameter function induced argument).mpr
    (normalizedReal_smooth data parameter function induced halfPlane argument)

def vector {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) : data.cusp.smooth :=
  ⟨HilbertStandard.value data parameter function induced argument,
    value_mem_smooth data parameter function induced halfPlane argument⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertStandardSmooth
