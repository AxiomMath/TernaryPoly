module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.SubdivisionInduction

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols TernaryPeriodPolynomials.GoodApartmentFunctional.BalancedReduction TernaryPeriodPolynomials.GoodApartmentFunctional.ReductionCompatibility
open TernaryPeriodPolynomials.GoodApartmentFunctional.SubdivisionInduction

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralDescent

noncomputable section

theorem determinant_updateCol_collinear (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (vector : Fin 3 → ℤ) (column replaced : Fin 3) (distinct : column ≠ replaced)
    (membership : integerVectorMap vector ∈ Submodule.span ℚ {integerVectorMap (matrix.col column)}) :
    (matrix.updateCol replaced vector).det = 0 := by
  obtain ⟨scalar, equality⟩ := Submodule.mem_span_singleton.mp membership
  apply Int.cast_injective (α := ℚ)
  rw [← rationalMatrix_det, rationalMatrix, Matrix.map_updateCol]
  change ((rationalMatrix matrix).updateCol replaced (integerVectorMap vector)).det = 0
  rw [← equality, Matrix.det_updateCol_smul]
  have zero : ((rationalMatrix matrix).updateCol replaced
      (integerVectorMap (matrix.col column))).det = 0 :=
    Matrix.det_updateCol_eq_zero distinct
  rw [zero, mul_zero]

theorem reducedSymbol_updateCol_collinear (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (vectorNormalized : (vector 2 : ZMod 3) = 1) (column : Fin 3)
    (membership : integerVectorMap vector ∈ Submodule.span ℚ {integerVectorMap (matrix.col column)}) :
    reducedSymbol (matrix.updateCol column vector)
      (normalized_updateCol matrix normalized vector vectorNormalized column) =
      reducedSymbol matrix normalized := by
  classical
  have subdivision := reducedSymbol_subdivision matrix normalized vector vectorNormalized
  unfold ReducedSubdivision at subdivision
  have entry (replaced : Fin 3) :
      reducedSymbol (matrix.updateCol replaced vector)
        (normalized_updateCol matrix normalized vector vectorNormalized replaced) =
        if replaced = column then reducedSymbol (matrix.updateCol column vector)
          (normalized_updateCol matrix normalized vector vectorNormalized column) else 0 := by
    by_cases equality : replaced = column
    · subst replaced
      rw [ite_eq_left rfl]
    · rw [ite_eq_right equality]
      exact reducedSymbol_zero _ _
        (determinant_updateCol_collinear matrix vector column replaced (Ne.symm equality) membership)
  have sumEquality : (∑ replaced, reducedSymbol (matrix.updateCol replaced vector)
      (normalized_updateCol matrix normalized vector vectorNormalized replaced)) =
      reducedSymbol (matrix.updateCol column vector)
        (normalized_updateCol matrix normalized vector vectorNormalized column) := by
    calc
      _ = ∑ replaced, if replaced = column then reducedSymbol (matrix.updateCol column vector)
          (normalized_updateCol matrix normalized vector vectorNormalized column) else 0 :=
        Finset.sum_congr rfl (fun replaced _membership => entry replaced)
      _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left]
  exact (subdivision.trans sumEquality).symm

theorem reducedSymbol_eq_of_column_spans_eq (first second : Matrix (Fin 3) (Fin 3) ℤ)
    (firstNormalized : normalizedIntegralMatrix first)
    (secondNormalized : normalizedIntegralMatrix second)
    (columns : ∀ column, Submodule.span ℚ {integerVectorMap (first.col column)} =
      Submodule.span ℚ {integerVectorMap (second.col column)}) :
    reducedSymbol first firstNormalized = reducedSymbol second secondNormalized := by
  let firstUpdate := first.updateCol 0 (second.col 0)
  let firstUpdateNormalized := normalized_updateCol first firstNormalized
    (second.col 0) (secondNormalized 0) 0
  let secondUpdate := firstUpdate.updateCol 1 (second.col 1)
  let secondUpdateNormalized := normalized_updateCol firstUpdate firstUpdateNormalized
    (second.col 1) (secondNormalized 1) 1
  have firstMembership : integerVectorMap (second.col 0) ∈
      Submodule.span ℚ {integerVectorMap (first.col 0)} := by
    rw [columns]
    exact Submodule.mem_span_singleton_self _
  have secondMembership : integerVectorMap (second.col 1) ∈
      Submodule.span ℚ {integerVectorMap (firstUpdate.col 1)} := by
    have columnEquality : firstUpdate.col 1 = first.col 1 := by ext row; simp [firstUpdate, Matrix.col]
    rw [columnEquality, columns]
    exact Submodule.mem_span_singleton_self _
  have thirdMembership : integerVectorMap (second.col 2) ∈
      Submodule.span ℚ {integerVectorMap (secondUpdate.col 2)} := by
    have columnEquality : secondUpdate.col 2 = first.col 2 := by
      ext row
      simp [secondUpdate, firstUpdate, Matrix.col]
    rw [columnEquality, columns]
    exact Submodule.mem_span_singleton_self _
  have finalEquality : secondUpdate.updateCol 2 (second.col 2) = second := by
    ext row column
    fin_cases column <;> simp [secondUpdate, firstUpdate, Matrix.col]
  exact (reducedSymbol_updateCol_collinear first firstNormalized (second.col 0)
    (secondNormalized 0) 0 firstMembership).symm.trans
      ((reducedSymbol_updateCol_collinear firstUpdate firstUpdateNormalized (second.col 1)
        (secondNormalized 1) 1 secondMembership).symm.trans
        ((reducedSymbol_updateCol_collinear secondUpdate secondUpdateNormalized (second.col 2)
          (secondNormalized 2) 2 thirdMembership).symm.trans
          (reducedSymbol_eq_of_matrix_eq _ _ _ _ finalEquality)))

def lineVector (line : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) : Fin 3 → ℤ :=
  (normalized_line_integral_frame line.val line.property).choose.val.val.col 0

theorem lineVector_normalized (line : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    (lineVector line 2 : ZMod 3) = 1 :=
  (normalized_line_integral_frame line.val line.property).choose.property 0

theorem lineVector_subspace (line : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    Submodule.span ℚ {integerVectorMap (lineVector line)} = flagSubspace .line line.val := by
  have equality := congrArg (flagSubspace .line)
    (normalized_line_integral_frame line.val line.property).choose_spec
  rw [flagSubspace_mk, line_frame_subspace] at equality
  exact equality

def tripleMatrix (vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun row column => ![lineVector vertices.1 row, lineVector vertices.2.1 row,
    lineVector vertices.2.2 row] column

theorem tripleMatrix_normalized (vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples) :
    normalizedIntegralMatrix (tripleMatrix vertices) := by
  intro column
  fin_cases column
  · exact lineVector_normalized vertices.1
  · exact lineVector_normalized vertices.2.1
  · exact lineVector_normalized vertices.2.2

def tripleValue (vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples) : SymbolSpace :=
  reducedSymbol (tripleMatrix vertices) (tripleMatrix_normalized vertices)

theorem tripleValue_eq_of_column_spans (vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples)
    (matrix : Matrix (Fin 3) (Fin 3) ℤ) (normalized : normalizedIntegralMatrix matrix)
    (columns : ∀ column, Submodule.span ℚ {integerVectorMap ((tripleMatrix vertices).col column)} =
      Submodule.span ℚ {integerVectorMap (matrix.col column)}) :
    tripleValue vertices = reducedSymbol matrix normalized :=
  reducedSymbol_eq_of_column_spans_eq _ _ _ _ columns

theorem cycleMatrix_as_swaps (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix matrix = swapColumns (swapColumns matrix 0 1) 1 2 := by
  ext row column
  fin_cases column <;> simp [TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix_entry, swapColumns,
    Equiv.swap_apply_def]

theorem reducedSymbol_cycle (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) :
    reducedSymbol (TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix matrix)
      (TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix_normalized matrix normalized) =
      reducedSymbol matrix normalized := by
  calc
    _ = reducedSymbol (swapColumns (swapColumns matrix 0 1) 1 2)
        (swapColumns_normalized _ (swapColumns_normalized matrix normalized 0 1) 1 2) :=
      reducedSymbol_eq_of_matrix_eq _ _ _ _ (cycleMatrix_as_swaps matrix)
    _ = -reducedSymbol (swapColumns matrix 0 1)
        (swapColumns_normalized matrix normalized 0 1) := reducedSymbol_swap _ _ _ _ (by decide)
    _ = reducedSymbol matrix normalized := by
      rw [reducedSymbol_swap matrix normalized 0 1 (by decide), neg_neg]

theorem tripleValue_cycle (first second third : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    tripleValue (first, second, third) = tripleValue (second, third, first) := by
  have equality : tripleMatrix (second, third, first) =
      TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix (tripleMatrix (first, second, third)) := by
    ext row column
    fin_cases column <;> simp [tripleMatrix, TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.cycleMatrix_entry]
  exact ((reducedSymbol_eq_of_matrix_eq _ _ _ _ equality).trans (reducedSymbol_cycle _ _)).symm

theorem tripleValue_swap (first second third : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    tripleValue (second, first, third) = -tripleValue (first, second, third) := by
  have equality : tripleMatrix (second, first, third) =
      swapColumns (tripleMatrix (first, second, third)) 0 1 := by
    ext row column
    fin_cases column <;> simp [tripleMatrix, swapColumns, Equiv.swap_apply_def]
  exact (reducedSymbol_eq_of_matrix_eq _ _ _ _ equality).trans
    (reducedSymbol_swap _ _ 0 1 (by decide))

theorem tripleMatrix_update_first (first second third inserted : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    (tripleMatrix (first, second, third)).updateCol 0 (lineVector inserted) =
      tripleMatrix (inserted, second, third) := by
  ext row column
  fin_cases column <;> simp [tripleMatrix]

theorem tripleMatrix_update_second (first second third inserted : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    (tripleMatrix (first, second, third)).updateCol 1 (lineVector inserted) =
      tripleMatrix (first, inserted, third) := by
  ext row column
  fin_cases column <;> simp [tripleMatrix]

theorem tripleMatrix_update_third (first second third inserted : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    (tripleMatrix (first, second, third)).updateCol 2 (lineVector inserted) =
      tripleMatrix (first, second, inserted) := by
  ext row column
  fin_cases column <;> simp [tripleMatrix]

theorem tripleValue_subdivision (first second third inserted : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    tripleValue (first, second, third) = tripleValue (inserted, second, third) +
      tripleValue (first, inserted, third) + tripleValue (first, second, inserted) := by
  have subdivision := reducedSymbol_subdivision (tripleMatrix (first, second, third))
    (tripleMatrix_normalized _) (lineVector inserted) (lineVector_normalized inserted)
  unfold ReducedSubdivision at subdivision
  rw [Fin.sum_univ_three] at subdivision
  exact subdivision.trans (congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (reducedSymbol_eq_of_matrix_eq _ _ _ _ (tripleMatrix_update_first first second third inserted))
      (reducedSymbol_eq_of_matrix_eq _ _ _ _ (tripleMatrix_update_second first second third inserted)))
    (reducedSymbol_eq_of_matrix_eq _ _ _ _ (tripleMatrix_update_third first second third inserted)))

theorem determinant_zero_of_column_mem_plane (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (plane : Flags .plane)
    (columns : ∀ column, integerVectorMap (matrix.col column) ∈ flagSubspace .plane plane) :
    matrix.det = 0 := by
  by_contra nonzero
  let frame := integralMatrixRationalFrame matrix nonzero
  have ambientLe : (⊤ : Submodule ℚ (Fin 3 → ℚ)) ≤ flagSubspace .plane plane := by
    intro vector _membership
    obtain ⟨coordinates, equality⟩ := (matrixVectorEquiv frame).surjective vector
    rw [← equality]
    change frame.val *ᵥ coordinates ∈ flagSubspace .plane plane
    rw [integralMatrixRationalFrame_val]
    have sumMembership : (∑ column, coordinates column • integerVectorMap (matrix.col column)) ∈
        flagSubspace .plane plane :=
      Submodule.sum_mem _ (fun column _membership => Submodule.smul_mem _ _ (columns column))
    convert sumMembership using 1
    ext row
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      rationalMatrix, Matrix.map_apply, integerVectorMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.col]
    apply Finset.sum_congr rfl
    intro column _membership
    exact mul_comm _ _
  have rank := Submodule.finrank_mono ambientLe
  rw [finrank_top, flagSubspace_finrank, Module.finrank_pi, Fintype.card_fin] at rank
  norm_num at rank

theorem tripleValue_coplanar (vertices : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.Triples)
    (coplanar : vertices ∈ TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.coplanarTriples) : tripleValue vertices = 0 := by
  obtain ⟨plane, firstIncidence, secondIncidence, thirdIncidence⟩ := coplanar
  apply reducedSymbol_zero
  apply determinant_zero_of_column_mem_plane _ plane
  intro column
  fin_cases column
  · apply firstIncidence
    rw [← lineVector_subspace]
    exact Submodule.mem_span_singleton_self _
  · apply secondIncidence
    rw [← lineVector_subspace]
    exact Submodule.mem_span_singleton_self _
  · apply thirdIncidence
    rw [← lineVector_subspace]
    exact Submodule.mem_span_singleton_self _

def triplesEvaluation : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.TripleChains →ₗ[ℂ] SymbolSpace :=
  Finsupp.linearCombination ℂ tripleValue

theorem triplesEvaluation_triple (first second third : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    triplesEvaluation (TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.triple first second third) =
      tripleValue (first, second, third) := by
  simp only [triplesEvaluation, TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.triple,
    Finsupp.linearCombination_single, one_smul]

theorem rationalRelations_evaluation :
    TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations ≤ triplesEvaluation.ker := by
  apply Submodule.span_le.mpr
  intro combination membership
  change triplesEvaluation combination = 0
  rcases membership with ((⟨first, second, third, rfl⟩ | ⟨first, second, third, rfl⟩) |
    ⟨first, second, third, inserted, rfl⟩) | ⟨vertices, coplanar, rfl⟩
  · rw [TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.cycleRelation, map_sub, triplesEvaluation_triple,
      triplesEvaluation_triple, tripleValue_cycle, sub_self]
  · rw [TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.swapRelation, map_add, triplesEvaluation_triple,
      triplesEvaluation_triple, tripleValue_swap first second third, add_neg_cancel]
  · rw [TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.subdivisionRelation, map_sub, map_add, map_add,
      triplesEvaluation_triple, triplesEvaluation_triple, triplesEvaluation_triple,
      triplesEvaluation_triple, tripleValue_subdivision, sub_self]
  · simp only [triplesEvaluation, Finsupp.linearCombination_single, one_smul]
    exact tripleValue_coplanar vertices coplanar

def rationalToIntegralSymbols : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.RationalSymbols →ₗ[ℂ] SymbolSpace :=
  TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.rationalRelations.liftQ triplesEvaluation rationalRelations_evaluation

theorem rationalToIntegralSymbols_symbol (first second third : TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.GoodLines) :
    rationalToIntegralSymbols (TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations.symbol first second third) =
      tripleValue (first, second, third) := triplesEvaluation_triple first second third

theorem tripleValue_normalizedFrame (frame : NormalizedFrames) :
    tripleValue (normalizedFrameTriple frame) = frameSymbol frame := by
  apply (tripleValue_eq_of_column_spans (normalizedFrameTriple frame) frame.val.val frame.property _).trans
    (reducedSymbol_frame frame)
  intro column
  fin_cases column
  all_goals
    change Submodule.span ℚ {integerVectorMap (lineVector _)} =
      Submodule.span ℚ {integerVectorMap (frame.val.val.col _)}
    rw [lineVector_subspace]
    change flagSubspace .line (columnLine (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val) _) = _
    rw [columnLine_subspace]
    rfl

theorem rationalToIntegralSymbols_frameSymbol (frame : NormalizedFrames) :
    rationalToIntegralSymbols (integralToRationalSymbols (frameSymbol frame)) = frameSymbol frame := by
  rw [integralToRationalSymbols_frameSymbol, rationalToIntegralSymbols_symbol]
  exact tripleValue_normalizedFrame frame

theorem rationalToIntegralSymbols_leftInverse :
    Function.LeftInverse rationalToIntegralSymbols integralToRationalSymbols := by
  have equality : (rationalToIntegralSymbols.comp integralToRationalSymbols).comp
      presentationRelations.mkQ = presentationRelations.mkQ := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    rw [show Finsupp.single frame coefficient = coefficient • Finsupp.single frame 1 by simp]
    simp only [LinearMap.comp_apply, map_smul]
    congr 1
    exact rationalToIntegralSymbols_frameSymbol frame
  intro value
  obtain ⟨combination, rfl⟩ := presentationRelations.mkQ_surjective value
  exact LinearMap.congr_fun equality combination

theorem integralToRationalSymbols_injective : Function.Injective integralToRationalSymbols :=
  rationalToIntegralSymbols_leftInverse.injective

theorem apartmentPresentation_kernel : apartmentPresentation.ker = presentationRelations :=
  le_antisymm (completeRelations_iff_rational_injective.mpr integralToRationalSymbols_injective)
    presentationRelations_apartment

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralDescent
