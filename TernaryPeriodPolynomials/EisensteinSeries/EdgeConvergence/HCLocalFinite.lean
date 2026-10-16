module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalMeasure
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Analytic
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.MajorantCompact
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.BinaryCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.OrbitLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Cusp.CommonLevel

@[expose] public section


/-!
# Finite level covariance and fixedness of the local Hilbert standard integral

Original work by Claude Sonnet 5.5.

For the finite embedding of an integral binary matrix of norm one, the local standard integral
satisfies `L (lineLevi 1 b · g) = π(b) L(g)`: the row action of `b` on the local coordinates is the
row action of its `3`-component on the `ℚ₃` coordinates, which preserves `localRadicalMeasure`
(`HCLocalMeasure`). Together with `L (g · k) = L (g)` for `k` in the finite level this shows that
`L (g)` is fixed by the open compact subgroup `LineOrbitLevel.level g` (local analogue of
`HilbertFixedStandard.value_fixed`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The local standard integral is invariant under right translation by the finite level (this is
`localValue_finite_invariant`, repeated here so that this file does not depend on the covariance
file). -/
theorem hcLocalValue_finite_invariant {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (level : finiteLevel) (argument : AdelicGL) :
    localValue data parameter function induced (argument * atFinite level.val) =
      localValue data parameter function induced argument := by
  unfold localValue localIntegrand
  apply integral_congr_ae
  filter_upwards [] with coordinates
  rw [← mul_assoc, CuspLift.finite_invariant]

/-- A unit of adelic norm one has trivial norm power. -/
theorem normPower_of_norm_one (unit : Adelesˣ) (norm : adeleNorm unit = 1) (exponent : ℂ) :
    normPower unit exponent = 1 := by
  simp only [normPower, norm, NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]

/-- The covariance of the local standard integrand under the finite binary group. -/
theorem localIntegrand_lineLevi_finite {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (unit : BinaryFiniteGL) (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter function induced (lineLevi 1 (atFinite unit) * argument)
        coordinates =
      normPower (GeneralLinearGroup.det (atFinite unit))
        (binaryInductionExponent degree .plane parameter) •
        data.cusp.π (atFinite unit)
          (localIntegrand data parameter function induced argument
            (localMatrixAction (GeneralLinearGroup.map finiteThree unit) coordinates)) := by
  change HilbertStandard.integrand data parameter function induced
    (lineLevi 1 (atFinite unit) * argument)
      (localAdele coordinates.1, localAdele coordinates.2) = _
  rw [HilbertBinaryCovariance.integrand_lineLevi, rowAction_atFinite_local]
  rfl

/-- The local standard integral is equivariant under the finite embedding of an integral binary
matrix of norm one. -/
theorem localValue_lineLevi_finite {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (unit : BinaryFiniteGL)
    (integral : ∃ binary : GeneralLinearGroup (Fin 2) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding binary = unit)
    (normOne : adeleNorm (GeneralLinearGroup.det (atFinite unit)) = 1) (argument : AdelicGL) :
    localValue data parameter function induced (lineLevi 1 (atFinite unit) * argument) =
      data.cusp.π (atFinite unit) (localValue data parameter function induced argument) := by
  obtain ⟨binary, rfl⟩ := integral
  have scalar := normPower_of_norm_one _ normOne
    (binaryInductionExponent degree .plane parameter)
  have commute : (∫ coordinates, data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binary))
      (localIntegrand data parameter function induced argument
        (localMatrixAction (GeneralLinearGroup.map finiteThree
          (GeneralLinearGroup.map integralEmbedding binary)) coordinates))
        ∂localRadicalMeasure) =
      data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binary))
        (∫ coordinates, localIntegrand data parameter function induced argument
          (localMatrixAction (GeneralLinearGroup.map finiteThree
            (GeneralLinearGroup.map integralEmbedding binary)) coordinates)
          ∂localRadicalMeasure) :=
    (CuspHilbertAction.isometry data.cusp
      (atFinite (GeneralLinearGroup.map integralEmbedding binary))).integral_comp_comm
      (fun coordinates => localIntegrand data parameter function induced argument
        (localMatrixAction (GeneralLinearGroup.map finiteThree
          (GeneralLinearGroup.map integralEmbedding binary)) coordinates))
  have invariance := integral_localMatrixAction_integral binary
    (localIntegrand data parameter function induced argument)
    (localIntegrand_continuous data parameter function induced argument)
  calc localValue data parameter function induced
        (lineLevi 1 (atFinite (GeneralLinearGroup.map integralEmbedding binary)) * argument)
      = ∫ coordinates, data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binary))
          (localIntegrand data parameter function induced argument
            (localMatrixAction (GeneralLinearGroup.map finiteThree
              (GeneralLinearGroup.map integralEmbedding binary)) coordinates))
          ∂localRadicalMeasure := by
        unfold localValue
        apply integral_congr_ae
        filter_upwards [] with coordinates
        rw [localIntegrand_lineLevi_finite, scalar, one_smul]
    _ = data.cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding binary))
          (∫ coordinates, localIntegrand data parameter function induced argument
            (localMatrixAction (GeneralLinearGroup.map finiteThree
              (GeneralLinearGroup.map integralEmbedding binary)) coordinates)
            ∂localRadicalMeasure) := commute
    _ = _ := by
        rw [invariance]
        rfl

/-- The principal congruence subgroup is contained in the level of an argument with integral
finite part. -/
theorem principal_le_level_of_integral (argument : AdelicGL)
    (integral : argument ∈ integralArguments) :
    CuspCommonLevel.principal ≤ LineOrbitLevel.level argument := by
  intro unit principalMembership
  refine ⟨principalMembership, ?_⟩
  obtain ⟨binary, reduced, equality⟩ := principalMembership
  obtain ⟨compact, compactEquality⟩ := integral
  change GeneralLinearGroup.map integralReduction binary = 1 at reduced
  have conjugation : LineOrbitLevel.conjugateLineHom argument unit =
      GeneralLinearGroup.map integralEmbedding (compact⁻¹ * lineLevi 1 binary * compact) := by
    change (finiteGroup argument)⁻¹ * lineLevi 1 unit * finiteGroup argument = _
    rw [compactEquality, ← equality, map_mul, map_mul, map_inv,
      LineDecomposition.map_lineLevi, map_one]
  change LineOrbitLevel.conjugateLineHom argument unit ∈ finiteLevel
  rw [conjugation]
  exact LineOrbitLevel.conjugate_principal_mem_finiteLevel binary reduced compact

/-- **Fixedness.** The local standard integral at `g` is fixed by the open compact subgroup
`LineOrbitLevel.level g` of `GL₂(𝔸_f)`. -/
theorem localValue_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (unit : LineOrbitLevel.level argument) :
    data.cusp.π (atFinite unit.val) (localValue data parameter function induced argument) =
      localValue data parameter function induced argument := by
  obtain ⟨levelElement, translation⟩ := LineOrbitLevel.level_translate argument unit
  obtain ⟨binary, _, equality⟩ := unit.property.1
  have covariance := localValue_lineLevi_finite data parameter function induced unit.val
    ⟨binary, equality⟩ (LineOrbitLevel.level_det_norm_one argument unit) argument
  rw [translation, hcLocalValue_finite_invariant] at covariance
  exact covariance.symm

end TernaryPeriodPolynomials.EdgeConvergence
