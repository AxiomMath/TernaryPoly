module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismDefect

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLinePrismLeviValue {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (coordinate : Fin 2) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (real : ℝ × ℝ) : ℂ :=
  functional (lowerRadicalLatticeContribution degree coordinate
    (realCoefficientComponent degree character
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice (radicalLatticeGenerator coordinate)))
      (sourceRealVertexPrism character source realUpperLeftLeviProjection
        (standardGoodLineRealArgument real) finite
        ![1, GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi matrix)])))

theorem goodLinePrismShiftTerm_functional {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (coordinate : Fin 2) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (real : ℝ × ℝ) :
    functional (lowerRadicalLatticeContribution degree coordinate
      (goodLinePrismShiftTerm character source real finite matrix (radicalLatticeGenerator coordinate))) =
    goodLinePrismLeviValue character source finite matrix coordinate functional
        (goodLineRadicalRealShift (radicalLatticeGenerator coordinate) real) -
      goodLinePrismLeviValue character source finite matrix coordinate functional real := by
  simp only [goodLinePrismShiftTerm, goodLinePrismLeviValue, map_sub]

/-- Moving a translated primitive moves the kernel by the inverse lattice shift. -/
theorem integral_goodLinePrismShiftTerm {degree : ℕ} (character : RankOneCharacter)
    (source : SourceCochain degree) (finite : FiniteGL) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (coordinate : Fin 2) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (parameter : ℂ)
    (original : Integrable (fun real => standardGoodLineRealKernel parameter real *
      goodLinePrismLeviValue character source finite matrix coordinate functional real)
      ((volume : Measure ℝ).prod volume))
    (translated : Integrable (fun real => standardGoodLineRealKernel parameter real *
      goodLinePrismLeviValue character source finite matrix coordinate functional
        (goodLineRadicalRealShift (radicalLatticeGenerator coordinate) real))
      ((volume : Measure ℝ).prod volume)) :
    (∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
      functional (lowerRadicalLatticeContribution degree coordinate
        (goodLinePrismShiftTerm character source real finite matrix (radicalLatticeGenerator coordinate)))
      ∂((volume : Measure ℝ).prod volume)) =
    ∫ real : ℝ × ℝ,
      (standardGoodLineRealKernel parameter
          (goodLineRadicalRealShift (radicalLatticeGenerator coordinate)⁻¹ real) -
        standardGoodLineRealKernel parameter real) *
      goodLinePrismLeviValue character source finite matrix coordinate functional real
      ∂((volume : Measure ℝ).prod volume) := by
  simp_rw [goodLinePrismShiftTerm_functional]
  exact integral_goodLineKernel_difference parameter (radicalLatticeGenerator coordinate)
    (goodLinePrismLeviValue character source finite matrix coordinate functional) original translated

/-- This equality keeps the two terms inside one integral and needs no separate integrability. -/
theorem goodLineSourceKernelIntegral_prism_defect {degree : ℕ} (positive : 0 < degree)
    (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (diagonal : ∀ vertex argument, source (fun _ => vertex) argument = 0)
    (parameter : ℂ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ)
    (finite : FiniteAwayThree × FiniteAwayThree) :
    goodLineSourceKernelIntegral data.chi source parameter matrix functional finite =
    ∫ real : ℝ × ℝ, standardGoodLineRealKernel parameter real *
      (functional
          (lowerRadicalLatticeContribution degree 0
              (goodLinePrismRadicalTerm data.chi source real (standardGoodLineFiniteArgument finite)
                matrix radicalLatticeFirst) +
            lowerRadicalLatticeContribution degree 1
              (goodLinePrismRadicalTerm data.chi source real (standardGoodLineFiniteArgument finite)
                matrix radicalLatticeSecond)) -
        (goodLinePrismLeviValue data.chi source (standardGoodLineFiniteArgument finite) matrix 0 functional
            (goodLineRadicalRealShift radicalLatticeFirst real) -
          goodLinePrismLeviValue data.chi source (standardGoodLineFiniteArgument finite) matrix 0 functional real +
          (goodLinePrismLeviValue data.chi source (standardGoodLineFiniteArgument finite) matrix 1 functional
              (goodLineRadicalRealShift radicalLatticeSecond real) -
            goodLinePrismLeviValue data.chi source (standardGoodLineFiniteArgument finite) matrix 1 functional real)))
      ∂((volume : Measure ℝ).prod volume) := by
  apply integral_congr_ae
  filter_upwards [] with real
  rw [goodLineMixedRealCoordinate_prism_defect positive data trivial source cocycle diagonal, map_sub, map_add]
  have first := goodLinePrismShiftTerm_functional data.chi source (standardGoodLineFiniteArgument finite)
    matrix 0 functional real
  have second := goodLinePrismShiftTerm_functional data.chi source (standardGoodLineFiniteArgument finite)
    matrix 1 functional real
  change functional (lowerRadicalLatticeContribution degree 0
    (goodLinePrismShiftTerm data.chi source real (standardGoodLineFiniteArgument finite) matrix radicalLatticeFirst)) = _ at first
  change functional (lowerRadicalLatticeContribution degree 1
    (goodLinePrismShiftTerm data.chi source real (standardGoodLineFiniteArgument finite) matrix radicalLatticeSecond)) = _ at second
  rw [map_add, first, second]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
