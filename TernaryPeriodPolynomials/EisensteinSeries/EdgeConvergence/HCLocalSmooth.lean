module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalFinite
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.TaylorProducer
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticBinary
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Inputs
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardSmooth
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.NormPower
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.PlaneJets

@[expose] public section


/-!
# The local Hilbert standard integral is a smooth vector

Original work by Claude Sonnet 5.5.

The local standard integral `L(g) = ∫_{(ℝ × ℚ₃)²} v_s(w⁻¹ n(u) g) du` at an argument `g` with
integral finite part is a smooth vector of the cusp representation (the first input
`EdgeInputs.LocalVectorsSmooth` of the `n = 3` totality argument). The proof is the local analogue of
`HilbertStandardSmooth.value_mem_smooth`:

* the `GL₂(ℝ)` orbit of `L(g)` is a `normPower` multiple of `x ↦ L(lineLevi 1 (atInfinity x) · g)`
  (`localValue_lineLevi_real`), which is smooth by the real right-orbit analyticity of
  `LocalTaylorProducer` combined with finite level invariance (`left_line_smooth`), applied to the
  reference function that keeps only the real part of the argument;
* `L(g)` is fixed by the open compact subgroup `LineOrbitLevel.level g` (`HCLocalFinite`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The local standard integral at the argument with the finite part of `argument` and the real part
of `other`. -/
def localReference {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument other : AdelicGL) : data.cusp.H :=
  localValue data parameter function induced
    (atFinite (finiteGroup argument) * atInfinity (realGroup other))

/-- Smoothness of the left `GL₂(ℝ)` orbit of the local standard integral at an argument with
integral finite part. -/
theorem localValue_leftLine_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    Smooth (fun real : Fin 1 → BinaryRealGL =>
      localValue data parameter function induced
        (lineLevi 1 (atInfinity (real 0)) * argument)) := by
  have referenceSmooth : ∀ base : AdelicGL, Smooth (fun real : Fin 1 → RealGL3 =>
      localReference data parameter function induced argument (base * atInfinity (real 0))) := by
    intro base
    have baseIntegral : atFinite (finiteGroup argument) * atInfinity (realGroup base) ∈
        integralArguments := by
      obtain ⟨compact, compactEquality⟩ := integral
      refine ⟨compact, ?_⟩
      rw [map_mul, InducedContinuity.finiteGroup_atFinite,
        InducedContinuity.finiteGroup_atInfinity, mul_one]
      exact compactEquality
    have smooth := localValue_right_smooth_of_integral data parameter function induced halfPlane _
      baseIntegral
    have equality : (fun real : Fin 1 → RealGL3 =>
        localReference data parameter function induced argument (base * atInfinity (real 0))) =
        fun real : Fin 1 → RealGL3 => localValue data parameter function induced
          (atFinite (finiteGroup argument) * atInfinity (realGroup base) *
            atInfinity (real 0)) := by
      funext real
      change localValue data parameter function induced (atFinite (finiteGroup argument) *
        atInfinity (realGroup (base * atInfinity (real 0)))) = _
      rw [map_mul, InducedContinuity.realGroup_atInfinity, RealTranslations.atInfinity_mul,
        ← mul_assoc]
    rw [equality]
    exact smooth
  have referenceInvariant : ∀ level : finiteLevel, ∀ other : AdelicGL,
      localReference data parameter function induced argument (other * atFinite level.val) =
        localReference data parameter function induced argument other := by
    intro level other
    change localValue data parameter function induced (atFinite (finiteGroup argument) *
      atInfinity (realGroup (other * atFinite level.val))) =
        localValue data parameter function induced (atFinite (finiteGroup argument) *
          atInfinity (realGroup other))
    rw [map_mul, InducedContinuity.realGroup_atFinite, mul_one]
  have lineSmooth := RightOrbitAnalyticity.left_line_smooth
    (localReference data parameter function induced argument) referenceSmooth referenceInvariant
    argument
  have equality : (fun real : Fin 1 → BinaryRealGL =>
      localReference data parameter function induced argument
        (atInfinity (lineLevi 1 (real 0)) * argument)) =
      fun real : Fin 1 → BinaryRealGL => localValue data parameter function induced
        (lineLevi 1 (atInfinity (real 0)) * argument) := by
    funext real
    have formula := AdelicPlaneJets.finite_local_formula
      (localValue data parameter function induced)
      (fun level other => hcLocalValue_finite_invariant data parameter function induced level other)
      (finiteGroup argument) argument (by simp) (lineLevi 1 (real 0))
    change localValue data parameter function induced (atFinite (finiteGroup argument) *
      atInfinity (realGroup (atInfinity (lineLevi 1 (real 0)) * argument))) = _
    rw [map_mul, InducedContinuity.realGroup_atInfinity, ← formula,
      HilbertStandardSmooth.lineLevi_atInfinity]
  rw [← equality]
  exact lineSmooth

/-- The `GL₂(ℝ)` orbit of the local standard integral is smooth. -/
theorem localValue_orbit_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    Smooth (fun real : Fin 1 → BinaryRealGL =>
      data.cusp.π (atInfinity (real 0)) (localValue data parameter function induced argument)) := by
  have lineSmooth := localValue_leftLine_smooth data parameter function induced halfPlane argument
    integral
  have scaled : Smooth (fun real : Fin 1 → BinaryRealGL =>
      normPower (GeneralLinearGroup.det (atInfinity (real 0)))
          (-binaryInductionExponent degree .line parameter) •
        localValue data parameter function induced
          (lineLevi 1 (atInfinity (real 0)) * argument)) :=
    (SmoothNormPower.real_power_smooth (size := 2) (0 : Fin 1)
      (-binaryInductionExponent degree .line parameter)).smul lineSmooth
  have equality : (fun real : Fin 1 → BinaryRealGL =>
      data.cusp.π (atInfinity (real 0)) (localValue data parameter function induced argument)) =
      fun real : Fin 1 → BinaryRealGL =>
        normPower (GeneralLinearGroup.det (atInfinity (real 0)))
            (-binaryInductionExponent degree .line parameter) •
          localValue data parameter function induced
            (lineLevi 1 (atInfinity (real 0)) * argument) := by
    funext real
    have cancel : normPower (GeneralLinearGroup.det (atInfinity (real 0)))
        (-binaryInductionExponent degree .line parameter) *
        normPower (GeneralLinearGroup.det (atInfinity (real 0)))
          (binaryInductionExponent degree .line parameter) = 1 := by
      simpa only [mul_one] using ParabolicInvariance.normPower_neg_mul
        (GeneralLinearGroup.det (atInfinity (real 0)))
        (binaryInductionExponent degree .line parameter) (1 : ℂ)
    rw [localValue_lineLevi_real, smul_smul, cancel, one_smul]
  rw [equality]
  exact scaled

/-- **The local Hilbert standard integral at an integral argument is a smooth vector.** -/
theorem localValue_mem_smooth {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    localValue data parameter function induced argument ∈ data.cusp.smooth := by
  apply (data.cusp.smooth_exact _).mpr
  refine ⟨localValue_orbit_smooth data parameter function induced halfPlane argument integral,
    LineOrbitLevel.level argument, LineOrbitLevel.level_isOpen argument,
    LineOrbitLevel.level_isCompact argument, ?_⟩
  intro unit
  exact localValue_fixed data parameter function induced argument unit

/-- **Input 1 (`LocalVectorsSmooth`).** -/
theorem localVectorsSmooth {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EdgeInputs.LocalVectorsSmooth data holomorphic := by
  intro sectionValue parameter halfPlane argument integral
  exact localValue_mem_smooth data parameter
    (EdgeInputs.flatFamily data holomorphic sectionValue parameter)
    ((EdgeInputs.flatFamily_flat data holomorphic sectionValue).1 parameter) halfPlane argument
    integral

end TernaryPeriodPolynomials.EdgeConvergence
