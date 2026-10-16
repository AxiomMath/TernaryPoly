module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlacePadicCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finitePadicEvaluation (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    FiniteAdeles →+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] :=
  (finiteCompletionPadicEquiv place).toRingHom.comp (finiteEvaluation place)

def finitePadicPlaneCoordinates (first second : FiniteAdeles) :
    FinitePlaneInductionCoordinates (planeOppositeStandardMatrix first second) :=
  finitePlaneCoordinatesFromLocal first second (fun place =>
    finitePlacePadicCoordinates place (finiteEvaluation place first) (finiteEvaluation place second))

theorem finitePadicPlaneCoordinates_block (first second : FiniteAdeles) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup.map (finitePadicEvaluation place) (finitePadicPlaneCoordinates first second).block =
      (padicPlanePivotCoordinates (finitePadicEvaluation place first) (finitePadicEvaluation place second)).block := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  change GeneralLinearGroup.map (finiteCompletionPadicEquiv place).toRingHom
    (GeneralLinearGroup.map (finiteEvaluation place) (finitePadicPlaneCoordinates first second).block) = _
  rw [finitePadicPlaneCoordinates, finitePlaneCoordinatesFromLocal_block]
  exact finitePlacePadicCoordinates_block place _ _

def standardGoodLineFinitePadicCoordinates (finite : FiniteAwayThree × FiniteAwayThree) :
    FinitePlaneInductionCoordinates (standardGoodLineFiniteArgument finite) :=
  let coordinates := finitePadicPlaneCoordinates finite.1.val finite.2.val
  { first := coordinates.first
    second := coordinates.second
    scalar := coordinates.scalar
    block := coordinates.block
    compact := coordinates.compact
    factorization := (standardGoodLineFiniteArgument_pivot finite).trans coordinates.factorization }

theorem standardGoodLineFinitePadicCoordinates_block (finite : FiniteAwayThree × FiniteAwayThree)
    (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup.map (finitePadicEvaluation place) (standardGoodLineFinitePadicCoordinates finite).block =
      (padicPlanePivotCoordinates (finitePadicEvaluation place finite.1.val)
        (finitePadicEvaluation place finite.2.val)).block :=
  finitePadicPlaneCoordinates_block _ _ place

theorem standardGoodLineFinitePadicCoordinates_det_norm (finite : FiniteAwayThree × FiniteAwayThree)
    (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ‖finitePadicEvaluation place (GeneralLinearGroup.det (standardGoodLineFinitePadicCoordinates finite).block).val‖ =
      (max 1 (max ‖finitePadicEvaluation place finite.1.val‖ ‖finitePadicEvaluation place finite.2.val‖))⁻¹ := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have equality := congrArg (fun matrix : GeneralLinearGroup (Fin 2)
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] => (GeneralLinearGroup.det matrix).val)
    (standardGoodLineFinitePadicCoordinates_block finite place)
  rw [generalLinearGroup_det_map] at equality
  change finitePadicEvaluation place (GeneralLinearGroup.det (standardGoodLineFinitePadicCoordinates finite).block).val = _ at equality
  rw [equality]
  exact padicPlanePivotCoordinates_det_norm _ _

theorem standardGoodLineFinitePadicCoordinates_block_integral (finite : FiniteAwayThree × FiniteAwayThree)
    (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ‖finitePadicEvaluation place finite.1.val‖ ≤ 1 → ‖finitePadicEvaluation place finite.2.val‖ ≤ 1 →
      GeneralLinearGroup.map (finitePadicEvaluation place) (standardGoodLineFinitePadicCoordinates finite).block = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro first_integral second_integral
  rw [standardGoodLineFinitePadicCoordinates_block, padicPlanePivotCoordinates_integral _ _ first_integral second_integral]

/-- These coordinates connect the actual finite average to the p-adic norm choices used in the local shell formula. -/
theorem goodLineFiniteVectorIntegral_padic (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      ∫ finite : FiniteAwayThree × FiniteAwayThree,
        normPower (finiteAdeleUnit (GeneralLinearGroup.det
          (standardGoodLineFinitePadicCoordinates finite).block)) ((degree : ℂ) / 2 + 3 + parameter) *
        cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates finite).block)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  goodLineFiniteVectorIntegral_eq_coordinates degree cusp parameter vector spherical standardGoodLineFinitePadicCoordinates

end TernaryPeriodPolynomials.SphericalDetection.Helpers
