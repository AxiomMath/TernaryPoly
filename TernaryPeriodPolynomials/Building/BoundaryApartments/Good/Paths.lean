module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Helpers

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem line_flag_eq_of_column {first second : RationalGL3} (scalar : ℚ)
    (column_eq : ∀ index, second.val index 0 = scalar * first.val index 0) :
    (QuotientGroup.mk first : Flags .line) = QuotientGroup.mk second := by
  apply QuotientGroup.eq.mpr
  change (first⁻¹ * second).val 1 0 = 0 ∧ (first⁻¹ * second).val 2 0 = 0
  have product (index : Fin 3) :
      (first⁻¹ * second).val index 0 = scalar * (first⁻¹ * first).val index 0 := by
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, column_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro summand _
    ring
  constructor <;> rw [product, inv_mul_cancel] <;> simp

def baseEdgeFrame : RationalGL3 := Adelic.weyl ^ 2

def baseEdge : Edges := QuotientGroup.mk baseEdgeFrame

theorem baseEdgeFrame_entries :
    baseEdgeFrame.val = !![0,1,0;0,0,1;1,0,0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [baseEdgeFrame, pow_two, Adelic.weyl, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem baseEdge_plane : endpoint .plane baseEdge = QuotientGroup.mk swapLastTwo := by
  change (QuotientGroup.mk baseEdgeFrame : Flags .plane) = QuotientGroup.mk swapLastTwo
  apply QuotientGroup.eq.mpr
  change (baseEdgeFrame⁻¹ * swapLastTwo).val 2 0 = 0 ∧
    (baseEdgeFrame⁻¹ * swapLastTwo).val 2 1 = 0
  constructor <;>
    norm_num [baseEdgeFrame, pow_two, _root_.mul_inv_rev, Adelic.weyl, swapLastTwo,
      GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem baseEdge_line_good : GoodFlag .line (endpoint .line baseEdge) := by
  refine ⟨![0,0,1], ⟨baseEdgeFrame, rfl, ![1,0,0], ⟨rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [baseEdgeFrame_entries]
    ext index
    fin_cases index <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
  · change (1 : ZMod 3) ≠ 0
    norm_num

theorem plane_good_of_firstColumn (frame : RationalGL3)
    (column_eq : ∀ index, frame.val index 0 = (![0,0,1] : Fin 3 → ℚ) index) :
    GoodFlag .plane (QuotientGroup.mk frame) := by
  refine ⟨![0,0,1], ⟨frame, rfl, ![1,0,0], rfl, ?_⟩, ?_⟩
  · ext index
    have coordinate := column_eq index
    fin_cases index <;> simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail] using coordinate
  · change (1 : ZMod 3) ≠ 0
    norm_num

theorem baseEdge_plane_good : GoodFlag .plane (endpoint .plane baseEdge) := by
  exact plane_good_of_firstColumn baseEdgeFrame (by
    intro index
    rw [baseEdgeFrame_entries]
    fin_cases index <;> rfl)

theorem goodChain_single {edge : Edges}
    (plane_good : GoodFlag .plane (endpoint .plane edge))
    (line_good : GoodFlag .line (endpoint .line edge)) :
    GoodChain (Finsupp.single edge (1 : ℂ)) := by
  classical
  intro candidate candidate_mem
  have candidate_eq : candidate = edge :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset candidate_mem)
  subst candidate
  exact ⟨plane_good, line_good⟩

theorem baseEdge_good : GoodChain (Finsupp.single baseEdge (1 : ℂ)) :=
  goodChain_single baseEdge_plane_good baseEdge_line_good

theorem chainBoundary_single (edge : Edges) :
    chainBoundary (Finsupp.single edge (1 : ℂ)) =
      Finsupp.single (Sum.inl (endpoint .plane edge)) 1 -
        Finsupp.single (Sum.inr (endpoint .line edge)) 1 := by
  simp [chainBoundary, Finsupp.linearCombination_single]

theorem plane_flag_swap (frame : RationalGL3) :
    (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane) =
      QuotientGroup.mk frame := by
  apply QuotientGroup.mk_mul_of_mem
  change swapFirstTwo.val 2 0 = 0 ∧ swapFirstTwo.val 2 1 = 0
  exact ⟨rfl, rfl⟩

theorem frame_swap_firstColumn (frame : RationalGL3) (index : Fin 3) :
    (frame * swapFirstTwo).val index 0 = frame.val index 1 := by
  simp [swapFirstTwo, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem translated_base_firstColumn (matrix : RationalGL3) (index : Fin 3) :
    (matrix * baseEdgeFrame).val index 0 = matrix.val index 2 := by
  rw [GeneralLinearGroup.coe_mul, baseEdgeFrame_entries]
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem twoEdge_path {matrix : rationalLevel} {frame : RationalGL3}
    (first_column : ∀ index, frame.val index 0 =
      (![0,0,1] : Fin 3 → ℚ) index)
    (second_column : ∀ index, frame.val index 1 = matrix.val.val index 2) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (translateVertex matrix.val pathBase) 1 -
        Finsupp.single pathBase 1 := by
  let first_edge : Edges := QuotientGroup.mk frame
  let second_edge : Edges := QuotientGroup.mk (frame * swapFirstTwo)
  have first_line : endpoint .line first_edge = endpoint .line baseEdge := by
    exact (line_flag_eq_of_column 1 (by
      intro index
      change frame.val index 0 = 1 * baseEdgeFrame.val index 0
      rw [baseEdgeFrame_entries, first_column]
      rw [one_mul]
      fin_cases index <;> rfl)).symm
  have second_line : endpoint .line second_edge =
      endpoint .line (matrix.val • baseEdge) := by
    exact (line_flag_eq_of_column 1 (by
      intro index
      change (frame * swapFirstTwo).val index 0 =
        1 * (matrix.val * baseEdgeFrame).val index 0
      rw [frame_swap_firstColumn, second_column, translated_base_firstColumn,
        one_mul])).symm
  have common_plane : endpoint .plane second_edge = endpoint .plane first_edge :=
    plane_flag_swap frame
  have first_plane_good : GoodFlag .plane (endpoint .plane first_edge) :=
    plane_good_of_firstColumn frame first_column
  have first_good : GoodChain (Finsupp.single first_edge (1 : ℂ)) :=
    goodChain_single first_plane_good (first_line ▸ baseEdge_line_good)
  have second_good : GoodChain (Finsupp.single second_edge (1 : ℂ)) := by
    apply goodChain_single
    · rw [common_plane]
      exact first_plane_good
    · rw [second_line, endpoint_translate]
      exact goodFlag_translate .line matrix _ baseEdge_line_good
  refine ⟨translateChain matrix.val (Finsupp.single baseEdge 1) -
    Finsupp.single second_edge 1 + Finsupp.single first_edge 1 -
      Finsupp.single baseEdge 1, ?_, ?_⟩
  · exact goodChain_sub
      (goodChain_add (goodChain_sub (goodChain_translate matrix baseEdge_good) second_good)
        first_good) baseEdge_good
  · simp only [translateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      map_sub, map_add, chainBoundary_single, first_line, second_line, common_plane,
      endpoint_translate, baseEdge_plane]
    change _ = Finsupp.single
      (Sum.inl (matrix.val • (QuotientGroup.mk swapLastTwo : Flags .plane))) 1 -
        Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)) 1
    abel

theorem good_path_exists (matrix : rationalLevel) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (translateVertex matrix.val pathBase) 1 -
        Finsupp.single pathBase 1 := by
  classical
  by_cases second_nonzero : matrix.val.val 1 2 ≠ 0
  · let frame_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
      !![0,matrix.val.val 0 2,1;0,matrix.val.val 1 2,0;1,matrix.val.val 2 2,0]
    have determinant_nonzero : frame_matrix.det ≠ 0 := by
      simpa [frame_matrix, Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
        using second_nonzero
    let frame := GeneralLinearGroup.mkOfDetNeZero frame_matrix determinant_nonzero
    apply twoEdge_path (frame := frame)
    · intro index
      fin_cases index <;> rfl
    · intro index
      fin_cases index <;> rfl
  · by_cases first_nonzero : matrix.val.val 0 2 ≠ 0
    · let frame_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
        !![0,matrix.val.val 0 2,0;0,matrix.val.val 1 2,1;1,matrix.val.val 2 2,0]
      have determinant_nonzero : frame_matrix.det ≠ 0 := by
        simpa [frame_matrix, Matrix.det_fin_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
          using first_nonzero
      let frame := GeneralLinearGroup.mkOfDetNeZero frame_matrix determinant_nonzero
      apply twoEdge_path (frame := frame)
      · intro index
        fin_cases index <;> rfl
      · intro index
        fin_cases index <;> rfl
    · have first_zero := not_ne_iff.mp first_nonzero
      have second_zero := not_ne_iff.mp second_nonzero
      have same_line : endpoint .line (matrix.val • baseEdge) =
          endpoint .line baseEdge := by
        exact (line_flag_eq_of_column (matrix.val.val 2 2) (by
          intro index
          change (matrix.val * baseEdgeFrame).val index 0 =
            matrix.val.val 2 2 * baseEdgeFrame.val index 0
          rw [translated_base_firstColumn, baseEdgeFrame_entries]
          fin_cases index <;> simp [first_zero, second_zero,
            Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.vecHead, Matrix.vecTail])).symm
      refine ⟨translateChain matrix.val (Finsupp.single baseEdge 1) -
        Finsupp.single baseEdge 1,
          goodChain_sub (goodChain_translate matrix baseEdge_good) baseEdge_good, ?_⟩
      simp only [translateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        map_sub, chainBoundary_single, same_line, endpoint_translate, baseEdge_plane]
      change _ = Finsupp.single
        (Sum.inl (matrix.val • (QuotientGroup.mk swapLastTwo : Flags .plane))) 1 -
          Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)) 1
      abel

def goodPaths (matrix : rationalLevel) : EdgeChains :=
  Classical.choose (good_path_exists matrix)

theorem goodPaths_isPathFamily : IsPathFamily goodPaths := by
  intro matrix
  exact Classical.choose_spec (good_path_exists matrix)

theorem good_line_path_exists (flag : Flags .line) (flag_good : GoodFlag .line flag) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (Sum.inr flag) 1 - Finsupp.single pathBase 1 := by
  classical
  induction flag using Quotient.inductionOn with
  | _ representative =>
    have construct {frame : RationalGL3}
        (first_column : ∀ index, frame.val index 0 =
          (![0,0,1] : Fin 3 → ℚ) index)
        (second_column : ∀ index, frame.val index 1 = representative.val index 0) :
        ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
          Finsupp.single (Sum.inr (QuotientGroup.mk representative : Flags .line)) 1 -
            Finsupp.single pathBase 1 := by
      let first_edge : Edges := QuotientGroup.mk frame
      let second_edge : Edges := QuotientGroup.mk (frame * swapFirstTwo)
      have first_line : endpoint .line first_edge = endpoint .line baseEdge := by
        apply (line_flag_eq_of_column 1 _).symm
        intro index
        change frame.val index 0 = 1 * baseEdgeFrame.val index 0
        rw [baseEdgeFrame_entries, first_column, one_mul]
        fin_cases index <;> rfl
      have second_line : endpoint .line second_edge = QuotientGroup.mk representative := by
        apply (line_flag_eq_of_column 1 _).symm
        intro index
        change (frame * swapFirstTwo).val index 0 = 1 * representative.val index 0
        rw [frame_swap_firstColumn, second_column, one_mul]
      have common_plane : endpoint .plane second_edge = endpoint .plane first_edge :=
        plane_flag_swap frame
      have plane_good : GoodFlag .plane (endpoint .plane first_edge) :=
        plane_good_of_firstColumn frame first_column
      refine ⟨Finsupp.single first_edge 1 - Finsupp.single second_edge 1 -
        Finsupp.single baseEdge 1, ?_, ?_⟩
      · apply goodChain_sub _ baseEdge_good
        apply goodChain_sub
        · apply goodChain_single plane_good
          rw [first_line]
          exact baseEdge_line_good
        · apply goodChain_single
          · rw [common_plane]
            exact plane_good
          · rw [second_line]
            exact flag_good
      · simp only [map_sub, chainBoundary_single, first_line, second_line,
          common_plane, baseEdge_plane]
        change _ = Finsupp.single (Sum.inr (QuotientGroup.mk representative : Flags .line)) 1 -
          Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)) 1
        abel
    by_cases second_nonzero : representative.val 1 0 ≠ 0
    · let frame_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
        !![0,representative.val 0 0,1;0,representative.val 1 0,0;1,representative.val 2 0,0]
      have determinant_nonzero : frame_matrix.det ≠ 0 := by
        simpa [frame_matrix, Matrix.det_fin_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
          using second_nonzero
      apply construct (frame := GeneralLinearGroup.mkOfDetNeZero frame_matrix determinant_nonzero)
      · intro index
        fin_cases index <;> rfl
      · intro index
        fin_cases index <;> rfl
    · by_cases first_nonzero : representative.val 0 0 ≠ 0
      · let frame_matrix : Matrix (Fin 3) (Fin 3) ℚ :=
          !![0,representative.val 0 0,0;0,representative.val 1 0,1;1,representative.val 2 0,0]
        have determinant_nonzero : frame_matrix.det ≠ 0 := by
          simpa [frame_matrix, Matrix.det_fin_three, Matrix.cons_val_zero,
            Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
            using first_nonzero
        apply construct (frame := GeneralLinearGroup.mkOfDetNeZero frame_matrix determinant_nonzero)
        · intro index
          fin_cases index <;> rfl
        · intro index
          fin_cases index <;> rfl
      · have same_line : (QuotientGroup.mk representative : Flags .line) =
            endpoint .line baseEdge := by
          apply (line_flag_eq_of_column (representative.val 2 0) _).symm
          intro index
          change representative.val index 0 = representative.val 2 0 * baseEdgeFrame.val index 0
          rw [baseEdgeFrame_entries]
          fin_cases index <;> simp [not_ne_iff.mp first_nonzero,
            not_ne_iff.mp second_nonzero, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
        refine ⟨0 - Finsupp.single baseEdge 1, goodChain_sub goodChain_zero baseEdge_good, ?_⟩
        simp only [map_sub, map_zero, chainBoundary_single, same_line, baseEdge_plane]
        change _ = Finsupp.single (Sum.inr (endpoint .line baseEdge)) 1 -
          Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)) 1
        abel

theorem good_plane_incident_edge (flag : Flags .plane) (flag_good : GoodFlag .plane flag) :
    ∃ edge : Edges, endpoint .plane edge = flag ∧ GoodFlag .line (endpoint .line edge) := by
  classical
  rcases flag_good with ⟨vector, ⟨representative, representative_eq, weights,
    weights_condition, weights_eq⟩, vector_good⟩
  have construct {matrix : Matrix (Fin 3) (Fin 3) ℚ}
      (determinant_nonzero : matrix.det ≠ 0)
      (first_column : ∀ index, matrix index 0 = weights index)
      (last_zero : matrix 2 0 = 0 ∧ matrix 2 1 = 0) :
      ∃ edge : Edges, endpoint .plane edge = flag ∧ GoodFlag .line (endpoint .line edge) := by
    let change_frame := GeneralLinearGroup.mkOfDetNeZero matrix determinant_nonzero
    let frame := representative * change_frame
    refine ⟨QuotientGroup.mk frame, ?_, vector, ⟨frame, rfl, ![1,0,0], ⟨rfl,rfl⟩, ?_⟩,
      vector_good⟩
    · change (QuotientGroup.mk (representative * change_frame) : Flags .plane) = flag
      rw [QuotientGroup.mk_mul_of_mem representative (show change_frame ∈ parabolic .plane from
        last_zero), representative_eq]
    · ext index
      have coordinate := congrFun weights_eq index
      change (representative * change_frame).val.mulVec ![1,0,0] index = _
      have frame_column (row : Fin 3) : change_frame.val row 0 = weights row :=
        first_column row
      simpa [GeneralLinearGroup.coe_mul, Matrix.mulVec, dotProduct, Matrix.mul_apply,
        Fin.sum_univ_three, frame_column, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using coordinate
  by_cases second_nonzero : weights 1 ≠ 0
  · apply construct (matrix := !![weights 0,1,0;weights 1,0,0;0,0,1])
    · simpa [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using second_nonzero
    · intro index
      fin_cases index <;> simp [weights_condition, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    · exact ⟨rfl,rfl⟩
  · have first_nonzero : weights 0 ≠ 0 := by
      intro first_zero
      have weights_zero : weights = 0 := by
        ext index
        fin_cases index <;> simp [first_zero, not_ne_iff.mp second_nonzero, weights_condition]
      have vector_zero : vector 2 = 0 := by
        have coordinate := congrFun weights_eq 2
        rw [weights_zero] at coordinate
        simpa using coordinate.symm
      exact vector_good (by rw [vector_zero]; rfl)
    apply construct (matrix := !![weights 0,0,0;weights 1,1,0;0,0,1])
    · simpa [Matrix.det_fin_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using first_nonzero
    · intro index
      fin_cases index <;> simp [weights_condition, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    · exact ⟨rfl,rfl⟩

theorem good_plane_path_exists (flag : Flags .plane) (flag_good : GoodFlag .plane flag) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (Sum.inl flag) 1 - Finsupp.single pathBase 1 := by
  rcases good_plane_incident_edge flag flag_good with ⟨edge, plane_eq, line_good⟩
  rcases good_line_path_exists (endpoint .line edge) line_good with
    ⟨chain, chain_good, chain_boundary⟩
  refine ⟨Finsupp.single edge 1 + chain,
    goodChain_add (goodChain_single (plane_eq ▸ flag_good) line_good) chain_good, ?_⟩
  rw [map_add, chainBoundary_single, chain_boundary, plane_eq]
  abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
