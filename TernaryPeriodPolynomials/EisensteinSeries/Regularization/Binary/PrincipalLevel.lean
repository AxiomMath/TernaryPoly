module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.InducedVectors
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.Realization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def binaryPrincipalLevel : Subgroup BinaryFiniteGL :=
  (MonoidHom.ker (GeneralLinearGroup.map (n := Fin 2) integralReduction)).map
    (GeneralLinearGroup.map integralEmbedding)

theorem binaryPrincipalLevel_isOpen : IsOpen (binaryPrincipalLevel : Set BinaryFiniteGL) := by
  let : TopologicalSpace (ZMod 3) := ⊥
  let : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  have source_open : IsOpen
      ((MonoidHom.ker (GeneralLinearGroup.map (n := Fin 2) integralReduction) :
        Subgroup (GeneralLinearGroup (Fin 2) IntegralAdeles)) : Set (GeneralLinearGroup (Fin 2) IntegralAdeles)) :=
    (isOpen_discrete {1}).preimage
      (generalLinearGroup_map_continuous integralReduction integralReduction_continuous 2)
  exact generalLinearGroup_map_isOpen integralEmbedding integralEmbedding_isOpenEmbedding 2 _ source_open

theorem integralMatrixGroup_compactSpace (size : ℕ) :
    CompactSpace (GeneralLinearGroup (Fin size) IntegralAdeles) := by
  let : ContinuousMul IntegralAdeles :=
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing.continuousMul integralEmbedding
  let : ContinuousAdd IntegralAdeles :=
    integralEmbedding_isOpenEmbedding.isEmbedding.isInducing.continuousAdd integralEmbedding
  let : CompactSpace (Matrix (Fin size) (Fin size) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin size → Fin size → IntegralAdeles))
  let : ContinuousMul (Matrix (Fin size) (Fin size) IntegralAdeles) :=
    ⟨continuous_fst.matrix_mul continuous_snd⟩
  infer_instance

theorem binaryPrincipalLevel_isCompact : IsCompact (binaryPrincipalLevel : Set BinaryFiniteGL) := by
  let : CompactSpace (GeneralLinearGroup (Fin 2) IntegralAdeles) := integralMatrixGroup_compactSpace 2
  have compact := isCompact_range
    (generalLinearGroup_map_continuous integralEmbedding integralEmbedding_isOpenEmbedding.continuous 2)
  apply compact.of_isClosed_subset (binaryPrincipalLevel.isClosed_of_isOpen binaryPrincipalLevel_isOpen)
  rintro matrix ⟨integralMatrix, _, represents⟩
  exact ⟨integralMatrix, represents⟩

theorem binaryPrincipalLevel_levi_conjugate_mem (binary : binaryPrincipalLevel)
    (matrix : GeneralLinearGroup (Fin 3) IntegralAdeles) :
    (GeneralLinearGroup.map integralEmbedding matrix)⁻¹ * planeLevi binary.val 1 *
      GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel := by
  obtain ⟨integralBinary, reduced, represents⟩ := binary.property
  refine ⟨matrix⁻¹ * planeLevi integralBinary 1 * matrix, ?_, ?_⟩
  · change GeneralLinearGroup.map integralReduction (matrix⁻¹ * planeLevi integralBinary 1 * matrix) ∈
      GeneralEisenstein.rowStabilizer
    have reduced_one : GeneralLinearGroup.map integralReduction integralBinary = 1 := reduced
    have levi_one : planeLevi (1 : GeneralLinearGroup (Fin 2) (ZMod 3)) 1 = 1 :=
      (planeLeviHom (ZMod 3)).map_one
    simp only [map_mul, map_inv, map_planeLevi, map_one, reduced_one, levi_one,
      mul_one, inv_mul_cancel, Subgroup.one_mem]
  · simp only [map_mul, map_inv, map_planeLevi, map_one, represents]

theorem binaryPrincipalLevel_levi_mem (binary : binaryPrincipalLevel) :
    planeLevi binary.val 1 ∈ finiteLevel := by
  simpa using binaryPrincipalLevel_levi_conjugate_mem binary 1

theorem atFinite_planeLevi (binary : BinaryFiniteGL) :
    atFinite (planeLevi binary 1) = planeLevi (atFinite binary) 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atFinite, combineGL, pairMatrix, planeLevi, planeBlock]

theorem binaryPrincipalLevel_det_normPower (binary : binaryPrincipalLevel) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atFinite binary.val)) exponent = 1 := by
  have norm_one := normPower_det_compact _
    (atFinite_level_compact ⟨planeLevi binary.val 1, binaryPrincipalLevel_levi_mem binary⟩) exponent
  simpa only [atFinite_planeLevi, det_planeLevi, mul_one] using norm_one

theorem atFinite_left_conjugate (finiteMatrix : FiniteGL) (matrix : AdelicGL) :
    atFinite finiteMatrix * matrix =
      matrix * atFinite ((finiteGroup matrix)⁻¹ * finiteMatrix * finiteGroup matrix) := by
  apply adelicGroup_eq_of_components
  · simp only [map_mul, realGroup_atFinite, one_mul, mul_one]
  · simp only [map_mul, finiteGroup_atFinite]
    group

theorem normalizedCuspVector_binaryPrincipalLevel_fixed
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (parameter : ℂ) (matrix : AdelicGL)
    (finite_integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding))
    (binary : binaryPrincipalLevel) :
    inducingData.cusp.π (atFinite binary.val) (normalizedCuspVector induced parameter matrix).val =
      (normalizedCuspVector induced parameter matrix).val := by
  obtain ⟨integralMatrix, represents⟩ := finite_integral
  have in_level : (finiteGroup matrix)⁻¹ * planeLevi binary.val 1 * finiteGroup matrix ∈ finiteLevel := by
    rw [← represents]
    exact binaryPrincipalLevel_levi_conjugate_mem binary integralMatrix
  have identity := normalizedCuspVector_binary induced parameter matrix (atFinite binary.val)
  rw [binaryPrincipalLevel_det_normPower, one_smul, ← atFinite_planeLevi,
    atFinite_left_conjugate, normalizedCuspVector_finite_level induced parameter _ ⟨_, in_level⟩] at identity
  exact (congrArg Subtype.val identity).symm

def cuspFiniteFixedSubmodule (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    Submodule ℂ cusp.smooth where
  carrier := {vector | ∀ binary : level, cusp.π (atFinite binary.val) vector.val = vector.val}
  zero_mem' := by intro binary; exact map_zero _
  add_mem' {first second} first_fixed second_fixed := by
    intro binary
    change cusp.π (atFinite binary.val) (first.val + second.val) = first.val + second.val
    rw [map_add, first_fixed, second_fixed]
  smul_mem' scalar vector fixed := by
    intro binary
    change cusp.π (atFinite binary.val) (scalar • vector.val) = scalar • vector.val
    rw [map_smul, fixed]

theorem normalizedCuspVector_compact_span_fixed
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    Submodule.span ℂ (normalizedCuspVector flat.1 0 '' {matrix | inMaximalCompact matrix}) ≤
      cuspFiniteFixedSubmodule inducingData.cusp binaryPrincipalLevel := by
  apply Submodule.span_le.mpr
  rintro vector ⟨matrix, compact, rfl⟩ binary
  exact normalizedCuspVector_binaryPrincipalLevel_fixed flat.1 0 matrix compact.2 binary

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
