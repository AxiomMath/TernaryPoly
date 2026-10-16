module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization.Geometry

open TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers

def IsRationalLevi (element : RationalGL3) : Prop :=
  element.val 0 1 = 0 ∧ element.val 0 2 = 0 ∧
    element.val 1 0 = 0 ∧ element.val 2 0 = 0

def IsRationalRadical (element : RationalGL3) : Prop :=
  ∃ first second : ℚ, element = lineUnipotent first second

theorem translateChain_single (element : RationalGL3) (edge : Edges) (coefficient : ℂ) :
    translateChain element (Finsupp.single edge coefficient) =
      Finsupp.single (element • edge) coefficient := by
  simp [translateChain, Finsupp.lmapDomain_apply]

theorem translateChain_mul (first second : RationalGL3) (chain : EdgeChains) :
    translateChain (first * second) chain =
      translateChain first (translateChain second chain) := by
  classical
  induction chain using Finsupp.induction with
  | zero => simp
  | @single_add edge coefficient chain _ _ induction_hypothesis =>
    simp only [map_add, translateChain_single, induction_hypothesis, mul_smul]

theorem translateChain_one (chain : EdgeChains) : translateChain 1 chain = chain := by
  classical
  induction chain using Finsupp.induction with
  | zero => simp
  | @single_add edge coefficient chain _ _ induction_hypothesis =>
    simp only [map_add, translateChain_single, induction_hypothesis, one_smul]

theorem radical_fixes_base (first second : ℚ) :
    translateVertex (lineUnipotent first second) pathBase = pathBase := by
  apply congrArg Sum.inl
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change Adelic.InPlaneParabolic (swapLastTwo⁻¹ *
    (lineUnipotent first second * swapLastTwo))
  constructor <;>
    simp [swapLastTwo, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two]

noncomputable def connector : EdgeChains :=
  Finsupp.single (QuotientGroup.mk (weyl * swapFirstTwo)) 1 -
    Finsupp.single (QuotientGroup.mk (weyl ^ 2)) 1

def otherBase : BuildingVertices := .inl (QuotientGroup.mk (weyl : RationalGL3))

theorem connector_boundary : chainBoundary connector =
    Finsupp.single otherBase 1 - Finsupp.single pathBase 1 := by
  have first_plane : endpoint .plane (QuotientGroup.mk (weyl * swapFirstTwo)) =
      (QuotientGroup.mk (weyl : RationalGL3) : Flags .plane) := by
    apply QuotientGroup.eq.mpr
    change Adelic.InPlaneParabolic ((weyl * swapFirstTwo)⁻¹ * weyl)
    simp only [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    constructor <;> rfl
  have second_plane : endpoint .plane (QuotientGroup.mk (weyl ^ 2)) =
      (QuotientGroup.mk swapLastTwo : Flags .plane) := by
    apply QuotientGroup.eq.mpr
    change Adelic.InPlaneParabolic ((weyl ^ 2)⁻¹ * swapLastTwo)
    constructor <;>
      norm_num [pow_two, weyl, swapLastTwo, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two]
  have common_line : endpoint .line (QuotientGroup.mk (weyl * swapFirstTwo)) =
      endpoint .line (QuotientGroup.mk (weyl ^ 2)) := by
    apply QuotientGroup.eq.mpr
    change Adelic.InLineParabolic ((weyl * swapFirstTwo)⁻¹ * weyl ^ 2)
    constructor <;>
      norm_num [pow_two, weyl, swapFirstTwo, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two]
  simp only [connector, map_sub, chainBoundary, Finsupp.linearCombination_single,
    one_smul, first_plane, second_plane, common_line]
  change _ = Finsupp.single (Sum.inl (QuotientGroup.mk weyl)) 1 -
    Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo)) 1
  abel

theorem levi_fixes_otherBase (element : RationalGL3) (levi : IsRationalLevi element) :
    translateVertex element otherBase = otherBase := by
  apply congrArg Sum.inl
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change Adelic.InPlaneParabolic (weyl⁻¹ * (element * weyl))
  constructor
  · simpa [weyl, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two] using levi.1
  · simpa [weyl, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two] using levi.2.1

theorem arithmetic_last_row (element : arithmeticLevel) (column : Fin 3) :
    (element.val.val 2 column : ZMod 3) = lastRow column := by
  have row := element.property
  change lastRow ᵥ* (reductionThree element.val).val = lastRow at row
  have entry := congrFun row column
  simpa [lastRow, Matrix.single_vecMul, reductionThree,
    GeneralLinearGroup.map_apply] using entry

theorem goodFlag_translate (element : rationalLevel) (side : Side) (flag : Flags side)
    (good : GoodFlag side flag) : GoodFlag side (element.val • flag) := by
  rcases element.property with ⟨integral_element, inclusion⟩
  change GeneralLinearGroup.map (Int.castRingHom ℚ) integral_element.val = element.val at inclusion
  rcases good with ⟨vector, ⟨frame, frame_flag, coordinates, coordinates_support, vector_eq⟩,
    vector_good⟩
  let new_vector : Fin 3 → ℤ := integral_element.val.val *ᵥ vector
  refine ⟨new_vector, ⟨element.val * frame, ?_, coordinates, ?_, ?_⟩, ?_⟩
  · change element.val • (QuotientGroup.mk frame : Flags side) = element.val • flag
    rw [frame_flag]
  · cases side <;> exact coordinates_support
  · rw [GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, vector_eq, ← inclusion]
    ext index
    simp [new_vector, GeneralLinearGroup.map_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  · have first := arithmetic_last_row integral_element 0
    have second := arithmetic_last_row integral_element 1
    have third := arithmetic_last_row integral_element 2
    change (integral_element.val.val 2 0 : ZMod 3) = 0 at first
    change (integral_element.val.val 2 1 : ZMod 3) = 0 at second
    change (integral_element.val.val 2 2 : ZMod 3) = 1 at third
    simpa [new_vector, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      first, second, third] using vector_good

theorem goodChain_single (edge : Edges) (coefficient : ℂ)
    (plane_good : GoodFlag .plane (endpoint .plane edge))
    (line_good : GoodFlag .line (endpoint .line edge)) :
    GoodChain (Finsupp.single edge coefficient) := by
  classical
  intro other_edge membership
  by_cases same : other_edge = edge
  · subst other_edge
    exact ⟨plane_good, line_good⟩
  · simp [Finsupp.mem_support_iff, Finsupp.single_eq_of_ne same] at membership

theorem goodChain_translate (element : rationalLevel) {chain : EdgeChains}
    (good : GoodChain chain) : GoodChain (translateChain element.val chain) := by
  classical
  induction chain using Finsupp.induction with
  | zero => simpa only [map_zero] using goodChain_zero
  | @single_add edge coefficient chain absent nonzero induction_hypothesis =>
    have single_good := good edge (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp absent, add_zero]
      exact nonzero)
    have remainder_good : GoodChain chain := by
      intro other_edge membership
      apply good other_edge
      have different : other_edge ≠ edge := by
        intro same
        subst other_edge
        exact absent membership
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne different, zero_add]
      exact Finsupp.mem_support_iff.mp membership
    rw [map_add, translateChain_single]
    apply goodChain_add
    · apply goodChain_single
      · rw [endpoint_smul]
        exact goodFlag_translate element .plane _ single_good.1
      · rw [endpoint_smul]
        exact goodFlag_translate element .line _ single_good.2
    · exact induction_hypothesis remainder_good

theorem connector_good : GoodChain connector := by
  have first_line : GoodFlag .line
      (endpoint .line (QuotientGroup.mk (weyl * swapFirstTwo))) := by
    refine ⟨![0, 0, 1], ⟨weyl * swapFirstTwo, rfl, ![1, 0, 0], ?_, ?_⟩, ?_⟩
    · exact ⟨rfl, rfl⟩
    · ext index
      fin_cases index <;>
        norm_num [weyl, swapFirstTwo, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
    · norm_num [Matrix.cons_val_two]
  have first_plane : GoodFlag .plane
      (endpoint .plane (QuotientGroup.mk (weyl * swapFirstTwo))) := by
    refine ⟨![0, 0, 1], ⟨weyl * swapFirstTwo, rfl, ![1, 0, 0], rfl, ?_⟩, ?_⟩
    · ext index
      fin_cases index <;>
        norm_num [weyl, swapFirstTwo, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
    · norm_num [Matrix.cons_val_two]
  have second_line : GoodFlag .line (endpoint .line (QuotientGroup.mk (weyl ^ 2))) := by
    refine ⟨![0, 0, 1], ⟨weyl ^ 2, rfl, ![1, 0, 0], ?_, ?_⟩, ?_⟩
    · exact ⟨rfl, rfl⟩
    · ext index
      fin_cases index <;>
        norm_num [pow_two, weyl, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
    · norm_num [Matrix.cons_val_two]
  have second_plane : GoodFlag .plane (endpoint .plane (QuotientGroup.mk (weyl ^ 2))) := by
    refine ⟨![0, 0, 1], ⟨weyl ^ 2, rfl, ![1, 0, 0], rfl, ?_⟩, ?_⟩
    · ext index
      fin_cases index <;>
        norm_num [pow_two, weyl, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Fin.sum_univ_three, Matrix.cons_val_two]
    · norm_num [Matrix.cons_val_two]
  exact goodChain_sub (goodChain_single _ _ first_plane first_line)
    (goodChain_single _ _ second_plane second_line)

theorem chainBoundary_translate (element : RationalGL3) (chain : EdgeChains) :
    chainBoundary (translateChain element chain) =
      Finsupp.lmapDomain ℂ ℂ (translateVertex element) (chainBoundary chain) := by
  classical
  induction chain using Finsupp.induction with
  | zero => simp
  | @single_add edge coefficient chain _ _ induction_hypothesis =>
    rw [map_add, map_add, map_add, induction_hypothesis]
    simp only [translateChain_single,
      chainBoundary, Finsupp.linearCombination_single,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_add, Finsupp.mapDomain_sub,
      Finsupp.mapDomain_smul, Finsupp.mapDomain_single, endpoint_smul]
    rfl

end TernaryPeriodPolynomials.PolynomialBadLineNormalization.Geometry
