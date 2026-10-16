module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

instance integralAdelesContinuousMul : ContinuousMul IntegralAdeles :=
  Topology.IsInducing.continuousMul integralEmbedding integralEmbedding_isOpenEmbedding.isInducing

instance integralAdelesContinuousAdd : ContinuousAdd IntegralAdeles :=
  Topology.IsInducing.continuousAdd integralEmbedding integralEmbedding_isOpenEmbedding.isInducing

def finiteIntegralGLLevel (dimension : ℕ) :
    Subgroup (GeneralLinearGroup (Fin dimension) FiniteAdeles) :=
  (GeneralLinearGroup.map (n := Fin dimension) integralEmbedding).range

theorem finiteIntegralGLLevel_mem_iff {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    matrix ∈ finiteIntegralGLLevel dimension ↔
      (∀ row column, matrix.val row column ∈ Set.range integralEmbedding) ∧
      ∀ row column, matrix⁻¹.val row column ∈ Set.range integralEmbedding := by
  constructor
  · rintro ⟨original, rfl⟩
    constructor
    · intro row column
      exact ⟨original.val row column, rfl⟩
    · intro row column
      exact ⟨original⁻¹.val row column, rfl⟩
  · rintro ⟨value_integral, inverse_integral⟩
    choose value value_eq using value_integral
    choose inverse inverse_eq using inverse_integral
    let value_matrix : Matrix (Fin dimension) (Fin dimension) IntegralAdeles := value
    let inverse_matrix : Matrix (Fin dimension) (Fin dimension) IntegralAdeles := inverse
    have value_map : integralEmbedding.mapMatrix value_matrix = matrix.val := by
      funext row column
      exact value_eq row column
    have inverse_map : integralEmbedding.mapMatrix inverse_matrix = matrix⁻¹.val := by
      funext row column
      exact inverse_eq row column
    have injective : Function.Injective
        (integralEmbedding.mapMatrix : Matrix (Fin dimension) (Fin dimension) IntegralAdeles →
          Matrix (Fin dimension) (Fin dimension) FiniteAdeles) :=
      Matrix.map_injective integralEmbedding_injective
    have value_inverse : value_matrix * inverse_matrix = 1 := by
      apply injective
      rw [map_mul, value_map, inverse_map, map_one]
      exact matrix.mul_inv
    have inverse_value : inverse_matrix * value_matrix = 1 := by
      apply injective
      rw [map_mul, value_map, inverse_map, map_one]
      exact matrix.inv_mul
    refine ⟨⟨value_matrix, inverse_matrix, value_inverse, inverse_value⟩, ?_⟩
    apply Units.ext
    exact value_map

theorem finiteIntegralGLLevel_isOpen (dimension : ℕ) :
    IsOpen (finiteIntegralGLLevel dimension : Set (GeneralLinearGroup (Fin dimension) FiniteAdeles)) := by
  have value_continuous : Continuous
      (fun matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles => matrix.val) := Units.continuous_val
  have inverse_continuous : Continuous
      (fun matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles => matrix⁻¹.val) :=
    value_continuous.comp continuous_inv
  have characterization : (finiteIntegralGLLevel dimension : Set (GeneralLinearGroup (Fin dimension) FiniteAdeles)) =
      {matrix | (∀ row column, matrix.val row column ∈ Set.range integralEmbedding) ∧
        ∀ row column, matrix⁻¹.val row column ∈ Set.range integralEmbedding} := by
    ext matrix
    exact finiteIntegralGLLevel_mem_iff matrix
  rw [characterization]
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsOpen.inter
  · apply isOpen_iInter_of_finite
    intro row
    apply isOpen_iInter_of_finite
    intro column
    exact integralLattice_isOpen.preimage
      ((continuous_apply column).comp ((continuous_apply row).comp value_continuous))
  · apply isOpen_iInter_of_finite
    intro row
    apply isOpen_iInter_of_finite
    intro column
    exact integralLattice_isOpen.preimage ((continuous_apply column).comp
      ((continuous_apply row).comp inverse_continuous))

theorem finiteIntegralGLLevel_isCompact (dimension : ℕ) :
    IsCompact (finiteIntegralGLLevel dimension : Set (GeneralLinearGroup (Fin dimension) FiniteAdeles)) := by
  change IsCompact (Set.range (GeneralLinearGroup.map (n := Fin dimension) integralEmbedding))
  let : CompactSpace IntegralAdeles := inferInstance
  let : CompactSpace (Matrix (Fin dimension) (Fin dimension) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin dimension → Fin dimension → IntegralAdeles))
  let : T1Space (Matrix (Fin dimension) (Fin dimension) IntegralAdeles) := inferInstance
  let : ContinuousMul (Matrix (Fin dimension) (Fin dimension) IntegralAdeles) :=
    ⟨continuous_fst.matrix_mul continuous_snd⟩
  let : CompactSpace (GeneralLinearGroup (Fin dimension) IntegralAdeles) := inferInstance
  apply isCompact_range
  exact Units.continuous_map (continuous_id.matrix_map integralEmbedding_isOpenEmbedding.continuous)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
