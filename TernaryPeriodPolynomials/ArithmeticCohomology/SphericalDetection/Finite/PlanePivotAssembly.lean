module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.PlanePivotValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finitePlanePivotLocalCoordinates (first second : FiniteAdeles) (place : FinitePlace) :
    LocalPlanePivotCoordinates (place.adicCompletionIntegers ℚ).toSubring
      (finiteEvaluation place first) (finiteEvaluation place second) :=
  valuedPlanePivotCoordinates Valued.v (finiteEvaluation place first) (finiteEvaluation place second)

def finitePlanePivotCompact (first second : FiniteAdeles) : GeneralLinearGroup (Fin 3) IntegralAdeles :=
  integralGLFromLocal (fun place => (finitePlanePivotLocalCoordinates first second place).compact)

theorem finitePlanePivotCompact_eval (first second : FiniteAdeles) (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place)
      (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second)) =
        GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).toSubring.subtype
          (finitePlanePivotLocalCoordinates first second place).compact :=
  integralGLFromLocal_eval _ place

theorem finitePlanePivot_parabolic_eval (first second : FiniteAdeles) (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place)
      (planeOppositeStandardMatrix first second *
        (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))⁻¹) =
    (planeInductionParabolic
      (finitePlanePivotLocalCoordinates first second place).radicalFirst
      (finitePlanePivotLocalCoordinates first second place).radicalSecond
      (finitePlanePivotLocalCoordinates first second place).scalar
      (finitePlanePivotLocalCoordinates first second place).block).val := by
  rw [map_mul, map_inv, planeOppositeStandardMatrix_map, finitePlanePivotCompact_eval]
  exact localPlanePivotCoordinates_parabolic _

def finitePlanePivotParabolic (first second : FiniteAdeles) : planeParabolic FiniteAdeles :=
  ⟨planeOppositeStandardMatrix first second *
      (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))⁻¹, by
    have entry_zero (column : Fin 2) :
        (planeOppositeStandardMatrix first second *
          (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))⁻¹).val
            2 column.castSucc = 0 := by
      apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
      intro place
      change (GeneralLinearGroup.map (finiteEvaluation place)
        (planeOppositeStandardMatrix first second *
          (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))⁻¹)).val
            2 column.castSucc = 0
      rw [finitePlanePivot_parabolic_eval]
      fin_cases column
      · exact (planeInductionParabolic _ _ _ _).property.1
      · exact (planeInductionParabolic _ _ _ _).property.2
    exact ⟨entry_zero 0, entry_zero 1⟩⟩

structure PlaneParabolicInductionCoordinates {R : Type*} [CommRing R] (parabolic : planeParabolic R) where
  first : R
  second : R
  scalar : Rˣ
  block : GeneralLinearGroup (Fin 2) R
  factorization : parabolic.val = planeUnipotent first second * (planeLevi 1 scalar * planeLevi block 1)

def planeParabolicInductionCoordinates {R : Type*} [CommRing R] (parabolic : planeParabolic R) :
    PlaneParabolicInductionCoordinates parabolic :=
  Classical.choice (by
    obtain ⟨first, second, scalar, block, factors⟩ := planeParabolic_exists_decomposition parabolic
    exact ⟨⟨first, second, scalar, block, factors⟩⟩)

def finitePlanePivotCoordinates (first second : FiniteAdeles) :
    FinitePlaneInductionCoordinates (planeOppositeStandardMatrix first second) :=
  let chosen := planeParabolicInductionCoordinates (finitePlanePivotParabolic first second)
  { first := chosen.first
    second := chosen.second
    scalar := chosen.scalar
    block := chosen.block
    compact := finitePlanePivotCompact first second
    factorization := by
      have factors := congrArg (fun matrix : FiniteGL =>
        matrix * GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))
        chosen.factorization
      simpa only [finitePlanePivotParabolic, mul_assoc, inv_mul_cancel, mul_one] using factors }

theorem finitePlaneInductionCoordinates_block_entry (finite : FiniteGL)
    (coordinates : FinitePlaneInductionCoordinates finite) (row column : Fin 2) :
    (finite * (GeneralLinearGroup.map integralEmbedding coordinates.compact)⁻¹).val
      row.castSucc column.castSucc = coordinates.block.val row column := by
  have factors := congrArg (fun matrix : FiniteGL =>
    matrix * (GeneralLinearGroup.map integralEmbedding coordinates.compact)⁻¹)
    (finitePlaneInductionCoordinates_parabolic finite coordinates)
  rw [mul_inv_cancel_right] at factors
  exact (congrArg (fun matrix : FiniteGL => matrix.val row.castSucc column.castSucc) factors).trans
    (planeInduction_block_entry _ _ _ _ row column)

theorem finitePlanePivotCoordinates_block_eval (first second : FiniteAdeles) (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place) (finitePlanePivotCoordinates first second).block =
      (finitePlanePivotLocalCoordinates first second place).block := by
  apply Units.ext
  funext row column
  rw [GeneralLinearGroup.map_apply,
    ← finitePlaneInductionCoordinates_block_entry _ (finitePlanePivotCoordinates first second)]
  change finiteEvaluation place
    ((planeOppositeStandardMatrix first second *
      (GeneralLinearGroup.map integralEmbedding (finitePlanePivotCompact first second))⁻¹).val
        row.castSucc column.castSucc) = _
  rw [← GeneralLinearGroup.map_apply, finitePlanePivot_parabolic_eval]
  exact planeInduction_block_entry _ _ _ _ row column

end TernaryPeriodPolynomials.SphericalDetection.Helpers
