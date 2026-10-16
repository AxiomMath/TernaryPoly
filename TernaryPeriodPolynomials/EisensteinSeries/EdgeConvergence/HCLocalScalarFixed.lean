module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLocalFinite

@[expose] public section


/-!
# The scalar integrand of the local Hilbert standard integral and its finite level invariance

Original work by Claude Sonnet 5.5.

The scalar integrand is the realization `realize (v_s(w⁻¹ n(u) g)) B` of the plane cusp lift at the
point of the local standard integrand. It is continuous in the local coordinates `u`, and its integral
over the local radical, as a function of the binary adele `B`, is invariant under right translation
by an integral binary matrix of norm one lying in the level of `g`: the vector covariance
`localIntegrand_lineLevi_finite` turns the translation into the row action of the `3`-component on the
`ℚ₃` coordinates, which preserves `localRadicalMeasure`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The realization at `binary` of the plane cusp lift at the point `w⁻¹ n(u) g` of the local
standard integrand. -/
def localScalarIntegrand {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (binary : BinaryAdelicGL) (coordinates : LocalLine × LocalLine) : ℂ :=
  data.cusp.realize (CuspLift.vector data .plane parameter function induced
    (weyl⁻¹ * localRadical coordinates * argument)) binary

theorem localScalarIntegrand_continuous {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (binary : BinaryAdelicGL) :
    Continuous (localScalarIntegrand data parameter function induced argument binary) := by
  change Continuous (fun coordinates : LocalLine × LocalLine => data.cusp.realize
    (CuspLift.vector data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * argument)) binary)
  simp only [CuspLift.realizes]
  exact continuous_const.mul ((InducedContinuity.induced_continuous data .plane parameter function
    induced).comp (continuous_const.mul
      ((continuous_const.mul localRadical_continuous).mul continuous_const)))

/-- The scalar integrand is invariant under the finite level, as a function of the argument. -/
theorem localScalarIntegrand_finite_invariant {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (level : finiteLevel) (argument : AdelicGL) (binary : BinaryAdelicGL)
    (coordinates : LocalLine × LocalLine) :
    localScalarIntegrand data parameter function induced (argument * atFinite level.val) binary
        coordinates =
      localScalarIntegrand data parameter function induced argument binary coordinates := by
  unfold localScalarIntegrand
  rw [← mul_assoc, CuspLift.finite_invariant]

/-- The scalar integrand of the translate of the argument by the finite embedding of an integral
binary matrix of norm one. -/
theorem localScalarIntegrand_lineLevi_finite {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (unit : BinaryFiniteGL)
    (normOne : adeleNorm (GeneralLinearGroup.det (atFinite unit)) = 1) (argument : AdelicGL)
    (binary : BinaryAdelicGL) (coordinates : LocalLine × LocalLine) :
    localScalarIntegrand data parameter function induced (lineLevi 1 (atFinite unit) * argument)
        binary coordinates =
      localScalarIntegrand data parameter function induced argument (binary * atFinite unit)
        (localMatrixAction (GeneralLinearGroup.map finiteThree unit) coordinates) := by
  have scalar := normPower_of_norm_one _ normOne
    (binaryInductionExponent degree .plane parameter)
  have vectorEquality : CuspLift.vector data .plane parameter function induced
      (weyl⁻¹ * localRadical coordinates * (lineLevi 1 (atFinite unit) * argument)) =
      ⟨data.cusp.π (atFinite unit) (CuspLift.vector data .plane parameter function induced
        (weyl⁻¹ * localRadical (localMatrixAction (GeneralLinearGroup.map finiteThree unit)
          coordinates) * argument)).val,
        data.cusp.smooth_stable _ _ (CuspLift.vector data .plane parameter function induced
          (weyl⁻¹ * localRadical (localMatrixAction (GeneralLinearGroup.map finiteThree unit)
            coordinates) * argument)).property⟩ := by
    apply Subtype.ext
    have covariance := localIntegrand_lineLevi_finite data parameter function induced unit
      argument coordinates
    rw [scalar, one_smul] at covariance
    exact covariance
  unfold localScalarIntegrand
  rw [vectorEquality, data.cusp.equivariant]

/-- **Scalar fixedness.** The integral of the scalar integrand over the local radical is invariant
under right translation of the binary adele by an integral binary matrix of norm one in the level of
the argument. -/
theorem localScalarIntegral_fixed {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (unit : BinaryFiniteGL)
    (integral : ∃ binary : GeneralLinearGroup (Fin 2) IntegralAdeles,
      GeneralLinearGroup.map integralEmbedding binary = unit)
    (normOne : adeleNorm (GeneralLinearGroup.det (atFinite unit)) = 1) (levelElement : finiteLevel)
    (translation : lineLevi 1 (atFinite unit) * argument = argument * atFinite levelElement.val)
    (test : BinaryAdelicGL) :
    (∫ coordinates, localScalarIntegrand data parameter function induced argument
      (test * atFinite unit) coordinates ∂localRadicalMeasure) =
    ∫ coordinates, localScalarIntegrand data parameter function induced argument test
      coordinates ∂localRadicalMeasure := by
  obtain ⟨binary, rfl⟩ := integral
  calc (∫ coordinates, localScalarIntegrand data parameter function induced argument
        (test * atFinite (GeneralLinearGroup.map integralEmbedding binary)) coordinates
          ∂localRadicalMeasure)
      = ∫ coordinates, localScalarIntegrand data parameter function induced argument
          (test * atFinite (GeneralLinearGroup.map integralEmbedding binary))
          (localMatrixAction (GeneralLinearGroup.map finiteThree
            (GeneralLinearGroup.map integralEmbedding binary)) coordinates)
          ∂localRadicalMeasure :=
        (integral_localMatrixAction_integral binary
          (localScalarIntegrand data parameter function induced argument
            (test * atFinite (GeneralLinearGroup.map integralEmbedding binary)))
          (localScalarIntegrand_continuous data parameter function induced argument
            (test * atFinite (GeneralLinearGroup.map integralEmbedding binary)))).symm
    _ = ∫ coordinates, localScalarIntegrand data parameter function induced
          (lineLevi 1 (atFinite (GeneralLinearGroup.map integralEmbedding binary)) * argument)
          test coordinates ∂localRadicalMeasure := by
        apply integral_congr_ae
        filter_upwards [] with coordinates
        exact (localScalarIntegrand_lineLevi_finite data parameter function induced _ normOne
          argument test coordinates).symm
    _ = ∫ coordinates, localScalarIntegrand data parameter function induced
          (argument * atFinite levelElement.val) test coordinates ∂localRadicalMeasure := by
        rw [translation]
    _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with coordinates
        exact localScalarIntegrand_finite_invariant data parameter function induced levelElement
          argument test coordinates

end TernaryPeriodPolynomials.EdgeConvergence
