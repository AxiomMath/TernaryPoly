module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalHeight
public import Mathlib.Topology.Instances.Matrix

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact

instance integralCompletionTopologicalRing (place : FinitePlace) :
    IsTopologicalRing (place.adicCompletionIntegers ℚ) :=
  inferInstanceAs (IsTopologicalRing (place.adicCompletionIntegers ℚ).toSubring)

noncomputable def finiteCompact : Subgroup FiniteGL := (GeneralLinearGroup.map integralEmbedding).range

theorem orthogonal_inv (matrix : RealGL3)
    (orthogonality : matrix.val.transpose * matrix.val = 1) :
    (matrix⁻¹).val.transpose * (matrix⁻¹).val = 1 := by
  have inverseEquality : matrix.inv = matrix.val.transpose := by
    calc
      matrix.inv = 1 * matrix.inv := (one_mul _).symm
      _ = (matrix.val.transpose * matrix.val) * matrix.inv := by rw [orthogonality]
      _ = matrix.val.transpose := by rw [mul_assoc, matrix.val_inv, mul_one]
  change matrix.inv.transpose * matrix.inv = 1
  rw [inverseEquality, Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff _ _).mp
    ((Matrix.mem_orthogonalGroup_iff' _ _).mpr orthogonality)

noncomputable def maximalCompact : Subgroup AdelicGL where
  carrier := {matrix | inMaximalCompact matrix}
  one_mem' := by
    constructor
    · simp only [map_one, Units.val_one, Matrix.transpose_one, one_mul]
    · exact ⟨1, by rw [map_one, map_one]⟩
  mul_mem' {first second} firstCompact secondCompact := by
    constructor
    · rw [map_mul, Units.val_mul, Matrix.transpose_mul, mul_assoc,
        ← mul_assoc (realGroup first).val.transpose, firstCompact.1, one_mul]
      exact secondCompact.1
    · obtain ⟨firstIntegral, firstEquality⟩ := firstCompact.2
      obtain ⟨secondIntegral, secondEquality⟩ := secondCompact.2
      exact ⟨firstIntegral * secondIntegral, by rw [map_mul, firstEquality, secondEquality, map_mul]⟩
  inv_mem' {matrix} compactness := by
    constructor
    · rw [map_inv]
      exact orthogonal_inv _ compactness.1
    · obtain ⟨integralMatrix, equality⟩ := compactness.2
      exact ⟨integralMatrix⁻¹, by rw [map_inv, equality, map_inv]⟩

theorem mem_maximalCompact (matrix : AdelicGL) :
    matrix ∈ maximalCompact ↔ inMaximalCompact matrix := Iff.rfl

theorem finiteCompact_atFinite (matrix : finiteCompact) :
    inMaximalCompact (atFinite matrix.val) := by
  constructor
  · change (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose * 1 = 1
    simp
  · exact matrix.property

theorem integralMap_continuous :
    Continuous (GeneralLinearGroup.map integralEmbedding (n := Fin 3)) := by
  apply Units.continuous_map
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  exact integralEmbedding_isOpenEmbedding.continuous.comp
    ((continuous_apply column).comp (continuous_apply row))

theorem finiteCompact_isCompact : IsCompact (finiteCompact : Set FiniteGL) := by
  let : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  exact isCompact_range integralMap_continuous

theorem finiteCompact_mem_iff (matrix : FiniteGL) : matrix ∈ finiteCompact ↔
    (∀ row column, matrix.val row column ∈ Set.range integralEmbedding) ∧
    (∀ row column, matrix.inv row column ∈ Set.range integralEmbedding) := by
  constructor
  · rintro ⟨integralMatrix, rfl⟩
    exact ⟨fun row column => ⟨integralMatrix.val row column, rfl⟩,
      fun row column => ⟨integralMatrix.inv row column, rfl⟩⟩
  · rintro ⟨values, inverses⟩
    choose valueEntries valueProperty using values
    choose inverseEntries inverseProperty using inverses
    let valueMatrix : Matrix (Fin 3) (Fin 3) IntegralAdeles := valueEntries
    let inverseMatrix : Matrix (Fin 3) (Fin 3) IntegralAdeles := inverseEntries
    have valueEquality : valueMatrix.map integralEmbedding = matrix.val := by
      apply Matrix.ext
      intro row column
      exact valueProperty row column
    have inverseEquality : inverseMatrix.map integralEmbedding = matrix.inv := by
      apply Matrix.ext
      intro row column
      exact inverseProperty row column
    let integralMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL :=
      ⟨valueMatrix, inverseMatrix, by
        apply Matrix.map_injective integralEmbedding_injective
        change integralEmbedding.mapMatrix (valueMatrix * inverseMatrix) =
          integralEmbedding.mapMatrix 1
        rw [map_mul]
        change valueMatrix.map integralEmbedding * inverseMatrix.map integralEmbedding = _
        rw [valueEquality, inverseEquality, matrix.val_inv, map_one],
       by
        apply Matrix.map_injective integralEmbedding_injective
        change integralEmbedding.mapMatrix (inverseMatrix * valueMatrix) =
          integralEmbedding.mapMatrix 1
        rw [map_mul]
        change inverseMatrix.map integralEmbedding * valueMatrix.map integralEmbedding = _
        rw [valueEquality, inverseEquality, matrix.inv_val, map_one]⟩
    exact ⟨integralMatrix, Units.ext valueEquality⟩

theorem finiteCompact_isOpen : IsOpen (finiteCompact : Set FiniteGL) := by
  have valuesOpen : IsOpen {matrix : FiniteGL |
      ∀ row column, matrix.val row column ∈ Set.range integralEmbedding} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro row
    apply isOpen_iInter_of_finite
    intro column
    exact integralLattice_isOpen.preimage
      ((continuous_apply column).comp ((continuous_apply row).comp
        (Units.continuous_val : Continuous (fun matrix : FiniteGL => matrix.val))))
  have inversesOpen : IsOpen {matrix : FiniteGL |
      ∀ row column, matrix.inv row column ∈ Set.range integralEmbedding} := by
    change IsOpen {matrix : FiniteGL |
      ∀ row column, (matrix⁻¹).val row column ∈ Set.range integralEmbedding}
    exact valuesOpen.preimage continuous_inv
  have equality : (finiteCompact : Set FiniteGL) =
      {matrix : FiniteGL | ∀ row column, matrix.val row column ∈ Set.range integralEmbedding} ∩
      {matrix : FiniteGL | ∀ row column, matrix.inv row column ∈ Set.range integralEmbedding} := by
    ext matrix
    exact finiteCompact_mem_iff matrix
  rw [equality]
  exact valuesOpen.inter inversesOpen

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact
