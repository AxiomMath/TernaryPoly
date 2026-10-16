module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.PlaneCoordinateTransport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePlaneCoordinates_exists_local_blocks (first second : FiniteAdeles)
    (locals : ∀ place : FinitePlace, LocalPlanePivotCoordinates (place.adicCompletionIntegers ℚ).toSubring
      (finiteEvaluation place first) (finiteEvaluation place second)) :
    ∃ coordinates : FinitePlaneInductionCoordinates (planeOppositeStandardMatrix first second),
      ∀ place : FinitePlace, GeneralLinearGroup.map (finiteEvaluation place) coordinates.block = (locals place).block := by
  let compact := integralGLFromLocal (fun place => (locals place).compact)
  let parabolicValue := planeOppositeStandardMatrix first second * (GeneralLinearGroup.map integralEmbedding compact)⁻¹
  have evaluated (place : FinitePlace) : GeneralLinearGroup.map (finiteEvaluation place) parabolicValue =
      (planeInductionParabolic (locals place).radicalFirst (locals place).radicalSecond
        (locals place).scalar (locals place).block).val := by
    dsimp only [parabolicValue, compact]
    rw [map_mul, map_inv, planeOppositeStandardMatrix_map, integralGLFromLocal_eval]
    exact localPlanePivotCoordinates_parabolic (locals place)
  have parabolic_member : parabolicValue ∈ planeParabolic FiniteAdeles := by
    have entry_zero (column : Fin 2) : parabolicValue.val 2 column.castSucc = 0 := by
      apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
      intro place
      change (GeneralLinearGroup.map (finiteEvaluation place) parabolicValue).val 2 column.castSucc = 0
      rw [evaluated]
      fin_cases column
      · exact (planeInductionParabolic _ _ _ _).property.1
      · exact (planeInductionParabolic _ _ _ _).property.2
    exact ⟨entry_zero 0, entry_zero 1⟩
  let parabolic : planeParabolic FiniteAdeles := ⟨parabolicValue, parabolic_member⟩
  obtain ⟨radicalFirst, radicalSecond, scalar, block, factors⟩ := planeParabolic_exists_decomposition parabolic
  let coordinates : FinitePlaneInductionCoordinates (planeOppositeStandardMatrix first second) :=
    { first := radicalFirst
      second := radicalSecond
      scalar := scalar
      block := block
      compact := compact
      factorization := by
        have equality := congrArg (fun matrix : FiniteGL => matrix * GeneralLinearGroup.map integralEmbedding compact) factors
        simpa only [parabolic, parabolicValue, mul_assoc, inv_mul_cancel, mul_one] using equality }
  refine ⟨coordinates, ?_⟩
  intro place
  apply Units.ext
  funext row column
  rw [GeneralLinearGroup.map_apply, ← finitePlaneInductionCoordinates_block_entry _ coordinates]
  change (GeneralLinearGroup.map (finiteEvaluation place) parabolicValue).val row.castSucc column.castSucc = _
  rw [evaluated]
  exact planeInduction_block_entry _ _ _ _ row column

def finitePlaneCoordinatesFromLocal (first second : FiniteAdeles)
    (locals : ∀ place : FinitePlace, LocalPlanePivotCoordinates (place.adicCompletionIntegers ℚ).toSubring
      (finiteEvaluation place first) (finiteEvaluation place second)) :
    FinitePlaneInductionCoordinates (planeOppositeStandardMatrix first second) :=
  Classical.choose (finitePlaneCoordinates_exists_local_blocks first second locals)

theorem finitePlaneCoordinatesFromLocal_block (first second : FiniteAdeles)
    (locals : ∀ place : FinitePlace, LocalPlanePivotCoordinates (place.adicCompletionIntegers ℚ).toSubring
      (finiteEvaluation place first) (finiteEvaluation place second)) (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place) (finitePlaneCoordinatesFromLocal first second locals).block =
      (locals place).block :=
  Classical.choose_spec (finitePlaneCoordinates_exists_local_blocks first second locals) place

end TernaryPeriodPolynomials.SphericalDetection.Helpers
