module

public import TernaryPeriodPolynomials.Building.Paths.GoodCusps.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers

def vectorFrame (vector : Fin 3 → ℚ) (index : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun row column => if column = index then vector row else (1 : Matrix (Fin 3) (Fin 3) ℚ) row column

theorem vectorFrame_det (vector : Fin 3 → ℚ) (index : Fin 3) :
    (vectorFrame vector index).det = vector index := by
  fin_cases index <;> simp [vectorFrame, Matrix.det_fin_three]

def vectorGL (vector : Fin 3 → ℚ) (index : Fin 3) (nonzero : vector index ≠ 0) :
    RationalGL3 :=
  GeneralLinearGroup.mkOfDetNeZero (vectorFrame vector index) (by
    rw [vectorFrame_det]
    exact nonzero)

theorem vectorGL_val (vector : Fin 3 → ℚ) (index : Fin 3) (nonzero : vector index ≠ 0) :
    (vectorGL vector index nonzero).val = vectorFrame vector index := by rfl

theorem vectorGL_column (vector : Fin 3 → ℚ) (index : Fin 3)
    (nonzero : vector index ≠ 0) :
    (vectorGL vector index nonzero).val *ᵥ Pi.single index 1 = vector := by
  ext row
  simp [vectorGL_val, Matrix.col, vectorFrame]

theorem goodFlag_of_column (side : Side) (matrix : RationalGL3)
    (vector : Fin 3 → ℤ) (index : Fin 3)
    (allowed : match side with | .plane => index ≠ 2 | .line => index = 0)
    (column_eq : matrix.val *ᵥ Pi.single index 1 = fun row => (vector row : ℚ))
    (last_nonzero : (vector 2 : ZMod 3) ≠ 0) :
    GoodFlag side (QuotientGroup.mk matrix) := by
  refine ⟨vector, ⟨matrix, rfl, Pi.single index 1, ?_, column_eq⟩, last_nonzero⟩
  cases side with
  | plane => simp [Ne.symm allowed]
  | line => subst index; simp

def axisPermutation : Fin 3 → RationalGL3
  | 0 => 1
  | 1 => swapFirstTwo
  | 2 => weyl ^ 2

theorem axisPermutation_column (index : Fin 3) :
    (axisPermutation index).val *ᵥ Pi.single 0 1 = Pi.single index 1 := by
  fin_cases index <;> ext row <;> fin_cases row <;>
    simp [axisPermutation, swapFirstTwo, weyl, pow_two, Units.val_mul,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.mul_apply, Pi.single_apply]

theorem exists_incident_good_line (side : Side) (flag : Flags side)
    (flag_good : GoodFlag side flag) :
    ∃ edge : Edges, endpoint side edge = flag ∧
      GoodFlag .plane (endpoint .plane edge) ∧ GoodFlag .line (endpoint .line edge) := by
  rcases flag_good with ⟨vector, ⟨matrix, flag_eq, coordinates, allowed, vector_eq⟩,
    last_nonzero⟩
  have vector_nonzero : (fun row => (vector row : ℚ)) ≠ 0 := by
    intro zero_eq
    have last_zero : vector 2 = 0 := by
      have : (vector 2 : ℚ) = 0 := congrFun zero_eq 2
      exact_mod_cast this
    exact last_nonzero (by simp [last_zero])
  have coordinates_nonzero : coordinates ≠ 0 := by
    intro zero_eq
    apply vector_nonzero
    rw [← vector_eq, zero_eq, Matrix.mulVec_zero]
  have some_nonzero : ∃ index, coordinates index ≠ 0 := by
    by_contra! all_zero
    exact coordinates_nonzero (funext all_zero)
  rcases some_nonzero with ⟨index, coordinate_nonzero⟩
  let basisChange := vectorGL coordinates index coordinate_nonzero * axisPermutation index
  let newMatrix := matrix * basisChange
  have new_column : newMatrix.val *ᵥ Pi.single 0 1 = fun row => (vector row : ℚ) := by
    change (matrix.val * ((vectorGL coordinates index coordinate_nonzero).val *
      (axisPermutation index).val)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, axisPermutation_column,
      vectorGL_column, vector_eq]
  have same_flag : QuotientGroup.mk newMatrix = flag := by
    rw [← flag_eq]
    symm
    apply QuotientGroup.eq.mpr
    change matrix⁻¹ * (matrix * basisChange) ∈ parabolic side
    rw [inv_mul_cancel_left]
    cases side with
    | plane =>
      change InPlaneParabolic basisChange
      have index_allowed : index ≠ 2 := by
        intro eq_two
        exact coordinate_nonzero (eq_two ▸ allowed)
      fin_cases index
      · simpa [basisChange, axisPermutation, InPlaneParabolic, vectorGL_val,
          vectorFrame] using allowed
      · simp [basisChange, axisPermutation, InPlaneParabolic, Units.val_mul,
          Matrix.mul_apply, Fin.sum_univ_three, vectorGL_val, vectorFrame,
          swapFirstTwo, allowed]
      · exact False.elim (index_allowed rfl)
    | line =>
      change InLineParabolic basisChange
      have index_zero : index = 0 := by
        fin_cases index
        · rfl
        · exact False.elim (coordinate_nonzero allowed.1)
        · exact False.elim (coordinate_nonzero allowed.2)
      subst index
      simp [basisChange, axisPermutation, vectorGL_val,
        InLineParabolic, vectorFrame, allowed.1, allowed.2]
  refine ⟨QuotientGroup.mk newMatrix, same_flag, ?_, ?_⟩
  · exact goodFlag_of_column .plane newMatrix vector 0 (by decide) new_column last_nonzero
  · exact goodFlag_of_column .line newMatrix vector 0 rfl new_column last_nonzero

theorem line_eq_of_column_eq (left right : RationalGL3)
    (column_eq : left.val *ᵥ Pi.single 0 1 = right.val *ᵥ Pi.single 0 1) :
    (QuotientGroup.mk left : Flags .line) = QuotientGroup.mk right := by
  apply QuotientGroup.eq.mpr
  change InLineParabolic (left⁻¹ * right)
  have relative_column : (left⁻¹ * right).val *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    change (left⁻¹.val * right.val) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, ← column_eq, Matrix.mulVec_mulVec]
    change (left⁻¹ * left).val *ᵥ Pi.single 0 1 = _
    rw [inv_mul_cancel]
    exact Matrix.one_mulVec _
  have first_zero := congrFun relative_column 1
  have second_zero := congrFun relative_column 2
  simpa [InLineParabolic] using
    (show (left⁻¹ * right).val 1 0 = 0 ∧ (left⁻¹ * right).val 2 0 = 0 from
      ⟨by simpa using first_zero, by simpa using second_zero⟩)

theorem plane_swap (matrix : RationalGL3) :
    (QuotientGroup.mk (matrix * swapFirstTwo) : Flags .plane) =
      QuotientGroup.mk matrix := by
  symm
  apply QuotientGroup.eq.mpr
  change matrix⁻¹ * (matrix * swapFirstTwo) ∈ parabolic .plane
  rw [inv_mul_cancel_left]
  change InPlaneParabolic swapFirstTwo
  exact ⟨rfl, rfl⟩

def verticalEdge : Edges := QuotientGroup.mk (swapLastTwo * swapFirstTwo)

theorem verticalEdge_plane :
    .inl (endpoint .plane verticalEdge) = pathBase := by
  change Sum.inl (QuotientGroup.mk (swapLastTwo * swapFirstTwo)) =
    Sum.inl (QuotientGroup.mk swapLastTwo)
  rw [plane_swap]

theorem verticalEdge_column :
    (swapLastTwo * swapFirstTwo).val *ᵥ Pi.single 0 1 = Pi.single 2 1 := by
  ext row
  fin_cases row <;> simp [Units.val_mul, swapLastTwo, swapFirstTwo]

theorem verticalEdge_good :
    GoodFlag .plane (endpoint .plane verticalEdge) ∧
      GoodFlag .line (endpoint .line verticalEdge) := by
  have column_eq : (swapLastTwo * swapFirstTwo).val *ᵥ Pi.single 0 1 =
      fun row => ((Pi.single 2 1 : Fin 3 → ℤ) row : ℚ) := by
    rw [verticalEdge_column]
    ext row
    fin_cases row <;> simp
  exact ⟨goodFlag_of_column .plane _ _ 0 (by decide) column_eq (by simp),
    goodFlag_of_column .line _ _ 0 rfl column_eq (by simp)⟩

def bridgeFrame (vector : Fin 3 → ℚ) (index : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  fun row column =>
    if column = 0 then vector row
    else if column = 1 then (Pi.single 2 1 : Fin 3 → ℚ) row
    else (Pi.single index 1 : Fin 3 → ℚ) row

theorem bridgeFrame_det (vector : Fin 3 → ℚ) :
    (bridgeFrame vector 0).det = vector 1 ∧
      (bridgeFrame vector 1).det = -vector 0 := by
  simp [bridgeFrame, Matrix.det_fin_three]

theorem exists_good_path_to_line (flag : Flags .line) (flag_good : GoodFlag .line flag) :
    ∃ chain : EdgeChains, GoodChain chain ∧
      chainBoundary chain = Finsupp.single (.inr flag) 1 - Finsupp.single pathBase 1 := by
  rcases flag_good with ⟨vector, ⟨matrix, matrix_flag, coordinates, allowed, vector_eq⟩,
    last_nonzero⟩
  let rationalVector : Fin 3 → ℚ := fun row => (vector row : ℚ)
  have last_rational_nonzero : rationalVector 2 ≠ 0 := by
    intro last_zero
    have last_zero_cast : (vector 2 : ℚ) = 0 := last_zero
    have : vector 2 = 0 := by exact_mod_cast last_zero_cast
    exact last_nonzero (by simp [this])
  let lineMatrix := vectorGL rationalVector 2 last_rational_nonzero * axisPermutation 2
  have line_column : lineMatrix.val *ᵥ Pi.single 0 1 = rationalVector := by
    change ((vectorGL rationalVector 2 last_rational_nonzero).val *
      (axisPermutation 2).val) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, axisPermutation_column, vectorGL_column]
  have flag_column : matrix.val *ᵥ Pi.single 0 (coordinates 0) = rationalVector := by
    change _ = fun row => (vector row : ℚ)
    rw [← vector_eq]
    congr 1
    ext row
    fin_cases row <;> simp [allowed.1, allowed.2]
  have scalar_nonzero : coordinates 0 ≠ 0 := by
    intro scalar_zero
    have zero_vector : rationalVector = 0 := by
      rw [← flag_column, scalar_zero]
      simp
    exact last_rational_nonzero (congrFun zero_vector 2)
  have scalar_single_nonzero : (Pi.single 0 (coordinates 0) : Fin 3 → ℚ) 0 ≠ 0 := by
    simpa using scalar_nonzero
  let rescaled := matrix * vectorGL (Pi.single 0 (coordinates 0)) 0 scalar_single_nonzero
  have rescaled_column : rescaled.val *ᵥ Pi.single 0 1 = rationalVector := by
    change (matrix.val * (vectorGL (Pi.single 0 (coordinates 0)) 0 scalar_single_nonzero).val) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec]
    rw [vectorGL_column (Pi.single 0 (coordinates 0)) 0 scalar_single_nonzero, flag_column]
  have rescaled_flag : (QuotientGroup.mk rescaled : Flags .line) = flag := by
    rw [← matrix_flag]
    symm
    apply QuotientGroup.eq.mpr
    change matrix⁻¹ * (matrix * _) ∈ parabolic .line
    rw [inv_mul_cancel_left]
    change InLineParabolic (vectorGL (Pi.single 0 (coordinates 0)) 0 scalar_single_nonzero)
    unfold InLineParabolic
    rw [vectorGL_val]
    simp [vectorFrame]
  have line_flag : (QuotientGroup.mk lineMatrix : Flags .line) = flag := by
    rw [← rescaled_flag]
    exact line_eq_of_column_eq _ _ (line_column.trans rescaled_column.symm)
  by_cases horizontal_zero : rationalVector 0 = 0 ∧ rationalVector 1 = 0
  · have vertical_column : lineMatrix.val *ᵥ Pi.single 0 1 =
        (swapLastTwo * swapFirstTwo).val *ᵥ Pi.single 0 (rationalVector 2) := by
      rw [line_column]
      ext row
      fin_cases row <;>
        simp [Units.val_mul, swapLastTwo, swapFirstTwo, horizontal_zero.1,
          horizontal_zero.2]
    have vertical_single_nonzero : (Pi.single 0 (rationalVector 2) : Fin 3 → ℚ) 0 ≠ 0 := by
      simpa using last_rational_nonzero
    let scaledVertical := (swapLastTwo * swapFirstTwo) *
      vectorGL (Pi.single 0 (rationalVector 2)) 0 vertical_single_nonzero
    have scaled_column : scaledVertical.val *ᵥ Pi.single 0 1 =
        lineMatrix.val *ᵥ Pi.single 0 1 := by
      change ((swapLastTwo * swapFirstTwo).val *
        (vectorGL (Pi.single 0 (rationalVector 2)) 0 vertical_single_nonzero).val) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec]
      rw [vectorGL_column (Pi.single 0 (rationalVector 2)) 0 vertical_single_nonzero,
        ← vertical_column]
    have scaled_flag : (QuotientGroup.mk scaledVertical : Flags .line) =
        endpoint .line verticalEdge := by
      symm
      apply QuotientGroup.eq.mpr
      change (swapLastTwo * swapFirstTwo)⁻¹ * ((swapLastTwo * swapFirstTwo) * _) ∈ _
      rw [inv_mul_cancel_left]
      change InLineParabolic (vectorGL (Pi.single 0 (rationalVector 2)) 0 vertical_single_nonzero)
      unfold InLineParabolic
      rw [vectorGL_val]
      simp [vectorFrame]
    have flag_vertical : flag = endpoint .line verticalEdge := by
      rw [← line_flag, ← scaled_flag]
      exact (line_eq_of_column_eq _ _ scaled_column).symm
    refine ⟨-Finsupp.single verticalEdge 1, goodChain_neg
      (goodChain_single _ verticalEdge_good.1 verticalEdge_good.2), ?_⟩
    rw [map_neg, chainBoundary_single, one_smul, flag_vertical]
    have := verticalEdge_plane
    rw [this]
    abel
  · have bridge_exists : ∃ bridge : RationalGL3,
        bridge.val *ᵥ Pi.single 0 1 = rationalVector ∧
        bridge.val *ᵥ Pi.single 1 1 = Pi.single 2 1 := by
      by_cases first_nonzero : rationalVector 0 ≠ 0
      · let bridge := GeneralLinearGroup.mkOfDetNeZero (bridgeFrame rationalVector 1)
          (by rw [bridgeFrame_det rationalVector |>.2]; exact neg_ne_zero.mpr first_nonzero)
        refine ⟨bridge, ?_, ?_⟩ <;> ext row <;>
          simp [bridge, bridgeFrame, GeneralLinearGroup.mkOfDetNeZero]
      · have second_nonzero : rationalVector 1 ≠ 0 := by
          intro second_zero
          exact horizontal_zero ⟨not_ne_iff.mp first_nonzero, second_zero⟩
        let bridge := GeneralLinearGroup.mkOfDetNeZero (bridgeFrame rationalVector 0)
          (by rw [bridgeFrame_det rationalVector |>.1]; exact second_nonzero)
        refine ⟨bridge, ?_, ?_⟩ <;> ext row <;>
          simp [bridge, bridgeFrame, GeneralLinearGroup.mkOfDetNeZero]
    rcases bridge_exists with ⟨bridge, bridge_column, vertical_column⟩
    let firstEdge : Edges := QuotientGroup.mk bridge
    let secondEdge : Edges := QuotientGroup.mk (bridge * swapFirstTwo)
    have first_line : endpoint .line firstEdge = flag := by
      rw [← line_flag]
      exact line_eq_of_column_eq _ _ (bridge_column.trans line_column.symm)
    have second_column : (bridge * swapFirstTwo).val *ᵥ Pi.single 0 1 = Pi.single 2 1 := by
      change (bridge.val * swapFirstTwo.val) *ᵥ _ = _
      rw [← Matrix.mulVec_mulVec]
      have swap_column : swapFirstTwo.val *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
        ext row; fin_cases row <;> simp [swapFirstTwo]
      rw [swap_column, vertical_column]
    have second_line : endpoint .line secondEdge = endpoint .line verticalEdge :=
      line_eq_of_column_eq _ _ (second_column.trans verticalEdge_column.symm)
    have same_plane : endpoint .plane secondEdge = endpoint .plane firstEdge := plane_swap bridge
    have first_good : GoodFlag .plane (endpoint .plane firstEdge) ∧
        GoodFlag .line (endpoint .line firstEdge) := by
      exact ⟨goodFlag_of_column .plane bridge vector 0 (by decide) bridge_column last_nonzero,
        first_line ▸ (show GoodFlag .line flag from
          ⟨vector, ⟨matrix, matrix_flag, coordinates, allowed, vector_eq⟩, last_nonzero⟩)⟩
    have second_good : GoodFlag .plane (endpoint .plane secondEdge) ∧
        GoodFlag .line (endpoint .line secondEdge) := by
      rw [same_plane, second_line]
      exact ⟨first_good.1, verticalEdge_good.2⟩
    refine ⟨Finsupp.single secondEdge 1 - Finsupp.single firstEdge 1 -
      Finsupp.single verticalEdge 1,
      goodChain_sub (goodChain_sub (goodChain_single _ second_good.1 second_good.2)
        (goodChain_single _ first_good.1 first_good.2))
        (goodChain_single _ verticalEdge_good.1 verticalEdge_good.2), ?_⟩
    simp only [map_sub, chainBoundary_single, one_smul]
    rw [same_plane, second_line, first_line, verticalEdge_plane]
    abel

theorem exists_good_path (vertex : BuildingVertices) (vertex_good : GoodVertex vertex) :
    ∃ chain : EdgeChains, GoodChain chain ∧
      chainBoundary chain = Finsupp.single vertex 1 - Finsupp.single pathBase 1 := by
  cases vertex with
  | inr flag => exact exists_good_path_to_line flag vertex_good
  | inl flag =>
    rcases exists_incident_good_line .plane flag vertex_good with
      ⟨edge, endpoint_eq, plane_good, line_good⟩
    rcases exists_good_path_to_line (endpoint .line edge) line_good with
      ⟨chain, chain_good, boundary_eq⟩
    refine ⟨chain + Finsupp.single edge 1,
      goodChain_add chain_good (goodChain_single edge plane_good line_good), ?_⟩
    rw [map_add, boundary_eq, chainBoundary_single, one_smul, endpoint_eq]
    abel

def chosenPath (vertex : BuildingVertices) : EdgeChains := by
  classical
  exact if vertex_good : GoodVertex vertex then (exists_good_path vertex vertex_good).choose else 0

theorem chosenPath_good (vertex : BuildingVertices) : GoodChain (chosenPath vertex) := by
  classical
  unfold chosenPath
  split
  · rename_i vertex_good
    exact (exists_good_path vertex vertex_good).choose_spec.1
  · exact goodChain_zero

theorem chosenPath_boundary (vertex : BuildingVertices) (vertex_good : GoodVertex vertex) :
    chainBoundary (chosenPath vertex) =
      Finsupp.single vertex 1 - Finsupp.single pathBase 1 := by
  classical
  unfold chosenPath
  rw [dite_eq_left vertex_good]
  exact (exists_good_path vertex vertex_good).choose_spec.2

theorem goodFlag_translate (group_element : rationalLevel) (side : Side)
    (flag : Flags side) (flag_good : GoodFlag side flag) :
    GoodFlag side (group_element.val • flag) := by
  rcases group_element.property with ⟨integral, integral_eq⟩
  rcases flag_good with ⟨vector, ⟨matrix, matrix_eq, coordinates, allowed, vector_eq⟩,
    last_nonzero⟩
  let newVector := integral.val.val *ᵥ vector
  have integral_row : lastRow ᵥ* (reductionThree integral.val).val = lastRow :=
    integral.property
  have row_zero : (integral.val.val 2 0 : ZMod 3) = 0 := by
    simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Pi.single_apply] using congrFun integral_row 0
  have row_one : (integral.val.val 2 1 : ZMod 3) = 0 := by
    simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Pi.single_apply] using congrFun integral_row 1
  have row_two : (integral.val.val 2 2 : ZMod 3) = 1 := by
    simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      Pi.single_apply] using congrFun integral_row 2
  have new_last_nonzero : (newVector 2 : ZMod 3) ≠ 0 := by
    simpa [newVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three, row_zero,
      row_one, row_two] using last_nonzero
  refine ⟨newVector, ⟨group_element.val * matrix, ?_, coordinates, ?_, ?_⟩,
    new_last_nonzero⟩
  · rw [← matrix_eq]
    rfl
  · cases side <;> exact allowed
  · change (group_element.val.val * matrix.val) *ᵥ coordinates = _
    rw [← Matrix.mulVec_mulVec, vector_eq, ← integral_eq]
    ext row
    simp [rationalInclusion, newVector, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem goodVertex_translate (group_element : rationalLevel) (vertex : BuildingVertices)
    (vertex_good : GoodVertex vertex) :
    GoodVertex (translateVertex group_element.val vertex) := by
  cases vertex with
  | inl flag => exact goodFlag_translate group_element .plane flag vertex_good
  | inr flag => exact goodFlag_translate group_element .line flag vertex_good

theorem goodChain_translate (group_element : rationalLevel) {chain : EdgeChains}
    (chain_good : GoodChain chain) : GoodChain (translateChain group_element.val chain) := by
  classical
  intro edge edge_mem
  have edge_support : edge ∈ chain.support.image (fun other => group_element.val • other) :=
    Finsupp.mapDomain_support edge_mem
  rcases Finset.mem_image.mp edge_support with ⟨other, other_mem, rfl⟩
  rw [endpoint_smul, endpoint_smul]
  exact ⟨goodFlag_translate group_element .plane _ (chain_good other other_mem).1,
    goodFlag_translate group_element .line _ (chain_good other other_mem).2⟩

end TernaryPeriodPolynomials.PolynomialPathGoodCusps.Helpers
