module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Recovery.Coefficients

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactFiniteFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteProfileResidues
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniversalFiniteProfiles

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteBoxSymmetry

theorem zero_one_locallyConstant {X : Type*} [TopologicalSpace X] (function : X → ℂ)
    (continuous : Continuous function) (values : ∀ point, function point = 0 ∨ function point = 1) :
    IsLocallyConstant function := by
  apply (IsLocallyConstant.iff_exists_open function).mpr
  intro point
  obtain zero | one := values point
  · refine ⟨{other | function other ≠ 1}, isOpen_ne.preimage continuous, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, zero] using (zero_ne_one : (0 : ℂ) ≠ 1)
    · intro other membership
      exact ((values other).resolve_right membership).trans zero.symm
  · refine ⟨{other | function other ≠ 0}, isOpen_ne.preimage continuous, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, one] using (one_ne_zero : (1 : ℂ) ≠ 0)
    · intro other membership
      exact ((values other).resolve_left membership).trans one.symm

theorem boxes_locallyConstant {degree : ℕ} (data : InducingData degree) (key : Key data) :
    IsLocallyConstant (boxes data key).test :=
  zero_one_locallyConstant _ (RecoveryCoefficients.boxes_continuous _) (boxes_values data key)

theorem integral_action_continuous :
    Continuous (fun pair : IntegralFiniteGL × IntegralSpace => pair.1.val * pair.2) := by
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum
  intro index _
  exact (((continuous_apply index).comp ((continuous_apply row).comp
    (Units.continuous_val (M := Matrix (Fin 3) (Fin 3) IntegralAdeles)))).comp continuous_fst).mul
      ((continuous_apply column).comp ((continuous_apply index).comp continuous_snd))

theorem embedding_mul (matrix : IntegralFiniteGL) (value : IntegralSpace) :
    embedding (matrix.val * value) = (GeneralLinearGroup.map integralEmbedding matrix).val * embedding value :=
  Matrix.map_mul

theorem integral_iff_action (matrix : IntegralFiniteGL) (value : Rectangular FiniteAdeles) :
    (GeneralLinearGroup.map integralEmbedding matrix).val * value ∈ Set.range embedding ↔ value ∈ Set.range embedding := by
  constructor
  · rintro ⟨preimage, equality⟩
    refine ⟨matrix⁻¹.val * preimage, ?_⟩
    rw [embedding_mul, equality, ← Matrix.mul_assoc]
    have inverse : (GeneralLinearGroup.map integralEmbedding matrix⁻¹).val *
        (GeneralLinearGroup.map integralEmbedding matrix).val = 1 := by
      rw [map_inv]
      exact (GeneralLinearGroup.map integralEmbedding matrix).inv_val
    rw [inverse, Matrix.one_mul]
  · rintro ⟨preimage, rfl⟩
    exact ⟨matrix.val * preimage, embedding_mul matrix preimage⟩

theorem exists_normal {degree : ℕ} (data : InducingData degree) :
    ∃ subgroup : OpenNormalSubgroup IntegralFiniteGL,
      (∀ matrix ∈ subgroup, GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel) ∧
      (∀ matrix ∈ subgroup, character data matrix = 1) ∧
      ∀ matrix ∈ subgroup, ∀ key : Key data, ∀ value : Rectangular FiniteAdeles,
        (boxes data key).test ((GeneralLinearGroup.map integralEmbedding matrix).val * value) =
          (boxes data key).test value := by
  let _ : CompactSpace (Matrix (Fin 3) (Fin 3) IntegralAdeles) :=
    inferInstanceAs (CompactSpace (Fin 3 → Fin 3 → IntegralAdeles))
  let _ : CompactSpace IntegralSpace := inferInstanceAs (CompactSpace (Fin 3 → Fin 2 → IntegralAdeles))
  have relationOpen (key : Key data) : IsOpen {pair : IntegralFiniteGL × IntegralSpace |
      (boxes data key).test (embedding (pair.1.val * pair.2)) = (boxes data key).test (embedding pair.2)} := by
    have first := (boxes_locallyConstant data key).comp_continuous
      (embedding_isOpenEmbedding.continuous.comp integral_action_continuous)
    have second : IsLocallyConstant (fun pair : IntegralFiniteGL × IntegralSpace =>
        (boxes data key).test (embedding pair.2)) := (boxes_locallyConstant data key).comp_continuous
      (embedding_isOpenEmbedding.continuous.comp continuous_snd)
    simpa using
      (first.comp₂ second (fun left right => left = right)).isOpen_fiber True
  let relation : Set (IntegralFiniteGL × IntegralSpace) := {pair | ∀ key : Key data,
    (boxes data key).test (embedding (pair.1.val * pair.2)) = (boxes data key).test (embedding pair.2)}
  have relationIsOpen : IsOpen relation := by
    have equality : relation = ⋂ key : Key data, {pair : IntegralFiniteGL × IntegralSpace |
        (boxes data key).test (embedding (pair.1.val * pair.2)) = (boxes data key).test (embedding pair.2)} := by
      ext pair
      simp only [relation, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [equality]
    exact isOpen_iInter_of_finite relationOpen
  have contains : ({1} : Set IntegralFiniteGL) ×ˢ Set.univ ⊆ relation := by
    rintro ⟨matrix, value⟩ ⟨rfl, _⟩ key
    simp only [Units.val_one, Matrix.one_mul]
  obtain ⟨left, right, leftOpen, _, oneIn, allIn, productIn⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ relationIsOpen contains
  have levelOpen : IsOpen {matrix : IntegralFiniteGL | GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel} :=
    InducedContinuity.level_isOpen.preimage BinaryLevel.integralMap_continuous
  have characterOpen : IsOpen {matrix : IntegralFiniteGL | character data matrix = 1} :=
    (FiniteProfileRegularity.character_locallyConstant data).isOpen_fiber 1
  obtain ⟨subgroup, contained⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((leftOpen.inter levelOpen).inter characterOpen)
    (show (1 : IntegralFiniteGL) ∈ (left ∩ {matrix | GeneralLinearGroup.map integralEmbedding matrix ∈ finiteLevel}) ∩
      {matrix | character data matrix = 1} from
        ⟨⟨oneIn (Set.mem_singleton 1), by simp only [Set.mem_ofPred_eq, map_one, Subgroup.one_mem]⟩,
          (FiniteProfileRegularity.finiteCharacter data).map_one⟩)
  refine ⟨subgroup, fun matrix membership => (contained membership).1.2,
    fun matrix membership => (contained membership).2, ?_⟩
  intro matrix membership key value
  by_cases integral : value ∈ Set.range embedding
  · obtain ⟨preimage, rfl⟩ := integral
    rw [← embedding_mul]
    exact productIn (a := (matrix, preimage)) ⟨(contained membership).1.1, allIn (Set.mem_univ preimage)⟩ key
  · rw [boxes_supported data key value integral, boxes_supported data key _
      (fun inside => integral ((integral_iff_action matrix value).mp inside))]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteBoxSymmetry
