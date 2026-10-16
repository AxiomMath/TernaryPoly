module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.GoodBuildingPaths.Helpers

noncomputable section

def baseEdge : RationalGL3 := swapLastTwo * swapFirstTwo

theorem baseEdge_column (index : Fin 3) :
    baseEdge.val index 0 = if index = 2 then 1 else 0 := by
  fin_cases index <;>
    simp [baseEdge, swapLastTwo, swapFirstTwo, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem baseEdge_plane :
    endpoint .plane (QuotientGroup.mk baseEdge) = QuotientGroup.mk swapLastTwo := by
  change QuotientGroup.mk (swapLastTwo * swapFirstTwo) =
    (QuotientGroup.mk swapLastTwo : Flags .plane)
  apply QuotientGroup.mk_mul_of_mem
  change InPlaneParabolic swapFirstTwo
  exact ⟨rfl, rfl⟩

theorem good_edge_of_column (frame : RationalGL3) (vector : Fin 3 → ℤ)
    (column : ∀ index, frame.val index 0 = (vector index : ℚ))
    (good : (vector 2 : ZMod 3) ≠ 0) :
    GoodFlag .plane (endpoint .plane (QuotientGroup.mk frame)) ∧
      GoodFlag .line (endpoint .line (QuotientGroup.mk frame)) := by
  have contains (side : Side) :
      IntegralVectorInFlag side (endpoint side (QuotientGroup.mk frame)) vector := by
    refine ⟨frame, rfl, ![1, 0, 0], ?_, ?_⟩
    · cases side <;> simp
    · ext index
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using column index
  exact ⟨⟨vector, contains .plane, good⟩, ⟨vector, contains .line, good⟩⟩

theorem good_single (edge : Edges)
    (good : GoodFlag .plane (endpoint .plane edge) ∧
      GoodFlag .line (endpoint .line edge)) :
    GoodChain (Finsupp.single edge (1 : ℂ)) := by
  classical
  intro other member
  have equality : other = edge := by simpa using member
  subst other
  exact good

theorem good_sub {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first - second) := by
  classical
  intro edge member
  rcases Finset.mem_union.mp (Finsupp.support_sub member) with member | member
  · exact first_good edge member
  · exact second_good edge member

theorem good_add {first second : EdgeChains}
    (first_good : GoodChain first) (second_good : GoodChain second) :
    GoodChain (first + second) := by
  classical
  intro edge member
  rcases Finset.mem_union.mp (Finsupp.support_add member) with member | member
  · exact first_good edge member
  · exact second_good edge member

theorem line_eq_of_column_eq (first second : RationalGL3)
    (column : ∀ index, first.val index 0 = second.val index 0) :
    endpoint .line (QuotientGroup.mk first) =
      endpoint .line (QuotientGroup.mk second) := by
  change (QuotientGroup.mk first : Flags .line) = QuotientGroup.mk second
  apply QuotientGroup.eq.mpr
  change InLineParabolic (first⁻¹ * second)
  have product (index : Fin 3) :
      (first⁻¹ * second).val index 0 = (1 : Matrix (Fin 3) (Fin 3) ℚ) index 0 := by
    calc
      (first⁻¹ * second).val index 0 = (first⁻¹ * first).val index 0 := by
        simp only [Units.val_mul, Matrix.mul_apply]
        congr 1
        ext coordinate
        rw [column]
      _ = _ := by rw [inv_mul_cancel, Units.val_one]
  exact ⟨product 1, product 2⟩

theorem swap_plane (frame : RationalGL3) :
    endpoint .plane (QuotientGroup.mk (frame * swapFirstTwo)) =
      endpoint .plane (QuotientGroup.mk frame) := by
  change (QuotientGroup.mk (frame * swapFirstTwo) : Flags .plane) =
    QuotientGroup.mk frame
  apply QuotientGroup.mk_mul_of_mem
  change InPlaneParabolic swapFirstTwo
  exact ⟨rfl, rfl⟩

theorem boundary_single (edge : Edges) :
    chainBoundary (Finsupp.single edge 1) =
      Finsupp.single (Sum.inl (endpoint .plane edge)) 1 -
        Finsupp.single (Sum.inr (endpoint .line edge)) 1 := by
  simp [chainBoundary]

theorem line_eq_of_scaled_column (first second : RationalGL3) (scalar : ℚ)
    (column : ∀ index, second.val index 0 = scalar * first.val index 0) :
    endpoint .line (QuotientGroup.mk first) =
      endpoint .line (QuotientGroup.mk second) := by
  change (QuotientGroup.mk first : Flags .line) = QuotientGroup.mk second
  apply QuotientGroup.eq.mpr
  change InLineParabolic (first⁻¹ * second)
  have product (index : Fin 3) :
      (first⁻¹ * second).val index 0 =
        scalar * (1 : Matrix (Fin 3) (Fin 3) ℚ) index 0 := by
    calc
      (first⁻¹ * second).val index 0 = scalar * (first⁻¹ * first).val index 0 := by
        simp only [Units.val_mul, Matrix.mul_apply, column, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro coordinate _
        ring
      _ = _ := by rw [inv_mul_cancel, Units.val_one]
  exact ⟨by simpa using product 1, by simpa using product 2⟩

theorem chain_from_bridge (target bridge : RationalGL3)
    (target_good : GoodFlag .plane (endpoint .plane (QuotientGroup.mk target)) ∧
      GoodFlag .line (endpoint .line (QuotientGroup.mk target)))
    (bridge_good : GoodFlag .plane (endpoint .plane (QuotientGroup.mk bridge)) ∧
      GoodFlag .line (endpoint .line (QuotientGroup.mk bridge)))
    (swapped_good : GoodFlag .plane
        (endpoint .plane (QuotientGroup.mk (bridge * swapFirstTwo))) ∧
      GoodFlag .line (endpoint .line (QuotientGroup.mk (bridge * swapFirstTwo))))
    (first_line : endpoint .line (QuotientGroup.mk bridge) =
      endpoint .line (QuotientGroup.mk baseEdge))
    (second_line : endpoint .line (QuotientGroup.mk (bridge * swapFirstTwo)) =
      endpoint .line (QuotientGroup.mk target)) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (Sum.inl (endpoint .plane (QuotientGroup.mk target))) 1 -
        Finsupp.single pathBase 1 := by
  have base_good := good_edge_of_column baseEdge ![0, 0, 1]
    (by intro index; rw [baseEdge_column]; fin_cases index <;> rfl)
    (by change (1 : ZMod 3) ≠ 0; exact one_ne_zero)
  refine ⟨(Finsupp.single (QuotientGroup.mk target) 1 -
      Finsupp.single (QuotientGroup.mk (bridge * swapFirstTwo)) 1) +
    (Finsupp.single (QuotientGroup.mk bridge) 1 -
      Finsupp.single (QuotientGroup.mk baseEdge) 1), ?_, ?_⟩
  · exact good_add (good_sub (good_single _ target_good) (good_single _ swapped_good))
      (good_sub (good_single _ bridge_good) (good_single _ base_good))
  · rw [map_add, map_sub, map_sub, boundary_single, boundary_single,
      boundary_single, boundary_single, swap_plane, first_line, second_line,
      baseEdge_plane]
    change _ = _ - Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo)) 1
    abel

theorem chain_to_integral_column (target : RationalGL3) (vector : Fin 3 → ℤ)
    (column : ∀ index, target.val index 0 = (vector index : ℚ))
    (good : (vector 2 : ZMod 3) ≠ 0) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (Sum.inl (endpoint .plane (QuotientGroup.mk target))) 1 -
        Finsupp.single pathBase 1 := by
  classical
  have target_good := good_edge_of_column target vector column good
  by_cases first_nonzero : vector 0 ≠ 0
  · let matrix : Matrix (Fin 3) (Fin 3) ℚ :=
      !![0, (vector 0 : ℚ), 0; 0, (vector 1 : ℚ), 1; 1, (vector 2 : ℚ), 0]
    have determinant : matrix.det ≠ 0 := by
      simpa [matrix, Matrix.det_fin_three] using
        (Int.cast_ne_zero.mpr first_nonzero : (vector 0 : ℚ) ≠ 0)
    let bridge := GeneralLinearGroup.mkOfDetNeZero matrix determinant
    have bridge_column (index : Fin 3) :
        bridge.val index 0 = ((![0, 0, 1] : Fin 3 → ℤ) index : ℚ) := by
      fin_cases index <;> simp [bridge, matrix]
    have swapped_column (index : Fin 3) :
        (bridge * swapFirstTwo).val index 0 = (vector index : ℚ) := by
      fin_cases index <;> simp [bridge, matrix, swapFirstTwo, Units.val_mul,
        Matrix.mul_apply, Fin.sum_univ_three]
    apply chain_from_bridge target bridge target_good
      (good_edge_of_column bridge ![0, 0, 1] bridge_column
        (by change (1 : ZMod 3) ≠ 0; exact one_ne_zero))
      (good_edge_of_column (bridge * swapFirstTwo) vector swapped_column good)
    · apply line_eq_of_column_eq
      intro index
      rw [bridge_column, baseEdge_column]
      fin_cases index <;> rfl
    · apply line_eq_of_column_eq
      intro index
      rw [swapped_column, column]
  · by_cases second_nonzero : vector 1 ≠ 0
    · let matrix : Matrix (Fin 3) (Fin 3) ℚ :=
        !![0, (vector 0 : ℚ), 1; 0, (vector 1 : ℚ), 0; 1, (vector 2 : ℚ), 0]
      have determinant : matrix.det ≠ 0 := by
        simpa [matrix, Matrix.det_fin_three] using
          (Int.cast_ne_zero.mpr second_nonzero : (vector 1 : ℚ) ≠ 0)
      let bridge := GeneralLinearGroup.mkOfDetNeZero matrix determinant
      have bridge_column (index : Fin 3) :
          bridge.val index 0 = ((![0, 0, 1] : Fin 3 → ℤ) index : ℚ) := by
        fin_cases index <;> simp [bridge, matrix]
      have swapped_column (index : Fin 3) :
          (bridge * swapFirstTwo).val index 0 = (vector index : ℚ) := by
        fin_cases index <;> simp [bridge, matrix, swapFirstTwo, Units.val_mul,
          Matrix.mul_apply, Fin.sum_univ_three]
      apply chain_from_bridge target bridge target_good
        (good_edge_of_column bridge ![0, 0, 1] bridge_column
          (by change (1 : ZMod 3) ≠ 0; exact one_ne_zero))
        (good_edge_of_column (bridge * swapFirstTwo) vector swapped_column good)
      · apply line_eq_of_column_eq
        intro index
        rw [bridge_column, baseEdge_column]
        fin_cases index <;> rfl
      · apply line_eq_of_column_eq
        intro index
        rw [swapped_column, column]
    · have first_zero : vector 0 = 0 := not_ne_iff.mp first_nonzero
      have second_zero : vector 1 = 0 := not_ne_iff.mp second_nonzero
      have same_line : endpoint .line (QuotientGroup.mk baseEdge) =
          endpoint .line (QuotientGroup.mk target) := by
        apply line_eq_of_scaled_column baseEdge target (vector 2 : ℚ)
        intro index
        rw [column, baseEdge_column]
        fin_cases index <;> simp [first_zero, second_zero]
      have base_good := good_edge_of_column baseEdge ![0, 0, 1]
        (by intro index; rw [baseEdge_column]; fin_cases index <;> rfl)
        (by change (1 : ZMod 3) ≠ 0; exact one_ne_zero)
      refine ⟨Finsupp.single (QuotientGroup.mk target) 1 -
        Finsupp.single (QuotientGroup.mk baseEdge) 1,
        good_sub (good_single _ target_good) (good_single _ base_good), ?_⟩
      rw [map_sub, boundary_single, boundary_single, same_line, baseEdge_plane]
      change _ = _ - Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo)) 1
      abel

theorem chain_to_translate (group : rationalLevel) :
    ∃ chain : EdgeChains, GoodChain chain ∧ chainBoundary chain =
      Finsupp.single (translateVertex group.val pathBase) 1 -
        Finsupp.single pathBase 1 := by
  rcases group.property with ⟨integral, equality⟩
  let vector : Fin 3 → ℤ := fun index => integral.val.val index 2
  have column (index : Fin 3) :
      (group.val * baseEdge).val index 0 = (vector index : ℚ) := by
    rw [← equality]
    simp [rationalInclusion, Units.val_mul, Matrix.mul_apply,
      baseEdge_column, vector]
  have reduction : (vector 2 : ZMod 3) = 1 := by
    have row := integral.property
    change lastRow ᵥ* (reductionThree integral.val).val = lastRow at row
    have last := congrFun row 2
    simpa [vector, lastRow, reductionThree, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three] using last
  have good : (vector 2 : ZMod 3) ≠ 0 := by rw [reduction]; exact one_ne_zero
  rcases chain_to_integral_column (group.val * baseEdge) vector column good with
    ⟨chain, chain_good, boundary⟩
  refine ⟨chain, chain_good, ?_⟩
  have plane : endpoint .plane (QuotientGroup.mk (group.val * baseEdge)) =
      group.val • (QuotientGroup.mk swapLastTwo : Flags .plane) := by
    change endpoint .plane (group.val • QuotientGroup.mk baseEdge) = _
    rw [endpoint_smul, baseEdge_plane]
  simpa only [plane, translateVertex, pathBase] using boundary

end

end TernaryPeriodPolynomials.GoodBuildingPaths.Helpers
