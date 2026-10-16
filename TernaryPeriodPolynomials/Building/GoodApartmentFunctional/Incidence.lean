module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralBases

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence

noncomputable section

def rationalFrameOfBasis (basis : Module.Basis (Fin 3) ℚ (Fin 3 → ℚ)) : RationalGL3 :=
  GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv ((Pi.basisFun ℚ (Fin 3)).equiv basis
      (Equiv.refl (Fin 3))))

theorem rationalFrameOfBasis_column (basis : Module.Basis (Fin 3) ℚ (Fin 3 → ℚ))
    (column : Fin 3) : (rationalFrameOfBasis basis).val.col column = basis column := by
  have evaluation : (GeneralLinearGroup.toLin (rationalFrameOfBasis basis)) •
      (Pi.basisFun ℚ (Fin 3)) column = basis column := by
    simp only [rationalFrameOfBasis, MulEquiv.apply_symm_apply,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_smul]
    exact Module.Basis.equiv_apply _ column basis (Equiv.refl (Fin 3))
  change (GeneralLinearGroup.toLin (rationalFrameOfBasis basis)).toLinearEquiv
    ((Pi.basisFun ℚ (Fin 3)) column) = basis column at evaluation
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv, GeneralLinearGroup.toLin_apply,
    Pi.basisFun_apply] at evaluation
  change (rationalFrameOfBasis basis).val *ᵥ Pi.single column 1 = basis column at evaluation
  rwa [Matrix.mulVec_single_one] at evaluation

theorem plane_frame_subspace (frame : RationalGL3) :
    frameSubspace .plane frame = Submodule.span ℚ {frame.val.col 0, frame.val.col 1} := by
  apply le_antisymm
  · intro vector membership
    obtain ⟨coordinates, allowed, equation⟩ := (mem_frameSubspace .plane frame vector).mp membership
    have decomposition : frame.val *ᵥ coordinates =
        coordinates 0 • frame.val.col 0 + coordinates 1 • frame.val.col 1 := by
      ext row
      change coordinates 2 = 0 at allowed
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, allowed, Matrix.col, mul_comm]
    rw [← equation, decomposition]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro vector membership
    rcases membership with rfl | membership
    · exact ⟨Pi.single 0 1, by simp [standardSubspace], by
        exact Matrix.mulVec_single_one frame.val 0⟩
    · have equality : vector = frame.val.col 1 := Set.mem_singleton_iff.mp membership
      subst vector
      exact ⟨Pi.single 1 1, by simp [standardSubspace], by
        exact Matrix.mulVec_single_one frame.val 1⟩

theorem frame_column_ne_zero (frame : RationalGL3) (column : Fin 3) : frame.val.col column ≠ 0 := by
  intro zero
  have inverseEquation := inverse_mulVec_mulVec frame (Pi.single column 1)
  rw [Matrix.mulVec_single_one, zero, Matrix.mulVec_zero] at inverseEquation
  have contradiction := congrArg (fun vector => vector column) inverseEquation
  simp at contradiction

theorem plane_has_vector_outside_line (line : Flags .line) (plane : Flags .plane) :
    ∃ vector ∈ flagSubspace .plane plane, vector ∉ flagSubspace .line line := by
  by_contra failure
  have inclusion : flagSubspace .plane plane ≤ flagSubspace .line line := by
    intro vector membership
    by_contra nonmembership
    exact failure ⟨vector, membership, nonmembership⟩
  have rank := Submodule.finrank_mono inclusion
  rw [flagSubspace_finrank, flagSubspace_finrank] at rank
  change 2 ≤ 1 at rank
  omega

theorem plane_has_vector_outside (plane : Flags .plane) :
    ∃ vector : Fin 3 → ℚ, vector ∉ flagSubspace .plane plane := by
  by_contra failure
  have equality : flagSubspace .plane plane = ⊤ := by
    apply top_unique
    intro vector _membership
    by_contra nonmembership
    exact failure ⟨vector, nonmembership⟩
  have rank := flagSubspace_finrank .plane plane
  rw [equality] at rank
  norm_num at rank

theorem range_pair (first second : Fin 3 → ℚ) :
    Set.range ![first, second] = {first, second} := by
  ext vector
  constructor
  · rintro ⟨index, rfl⟩
    fin_cases index <;> simp
  · intro membership
    rcases membership with rfl | membership
    · exact ⟨0, rfl⟩
    · exact ⟨1, (Set.mem_singleton_iff.mp membership).symm⟩

theorem edge_exists_of_incident (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) :
    ∃ edge : Edges, endpoint .line edge = line ∧ endpoint .plane edge = plane := by
  induction line using Quotient.inductionOn with
  | h lineFrame =>
    let first : Fin 3 → ℚ := lineFrame.val.col 0
    have lineSpan : flagSubspace .line (QuotientGroup.mk lineFrame) =
        Submodule.span ℚ {first} := line_frame_subspace lineFrame
    have firstNonzero : first ≠ 0 := frame_column_ne_zero lineFrame 0
    have firstInPlane : first ∈ flagSubspace .plane plane := by
      apply incidence
      rw [lineSpan]
      exact Submodule.mem_span_singleton_self first
    obtain ⟨second, secondInPlane, secondOutside⟩ :=
      plane_has_vector_outside_line (QuotientGroup.mk lineFrame) plane
    have pairIndependent : LinearIndependent ℚ ![first, second] := by
      apply (LinearIndependent.pair_iff' firstNonzero).mpr
      intro scalar equality
      apply secondOutside
      rw [lineSpan, ← equality]
      exact Submodule.smul_mem _ scalar (Submodule.mem_span_singleton_self first)
    have planeSpan : Submodule.span ℚ (Set.range ![first, second]) =
        flagSubspace .plane plane := by
      apply Submodule.eq_of_le_of_finrank_eq
      · apply Submodule.span_le.mpr
        rintro vector ⟨index, rfl⟩
        fin_cases index
        · exact firstInPlane
        · exact secondInPlane
      · rw [finrank_span_eq_card pairIndependent, flagSubspace_finrank]
        rfl
    obtain ⟨third, thirdOutside⟩ := plane_has_vector_outside plane
    have tripleIndependent := pairIndependent.finSnoc (by rwa [planeSpan])
    let basis := basisOfLinearIndependentOfCardEqFinrank'
      (Fin.snoc ![first, second] third) tripleIndependent (by simp)
    have basisFirst : basis 0 = first := by
      change (basisOfLinearIndependentOfCardEqFinrank' _ _ _) 0 = _
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']
      rfl
    have basisSecond : basis 1 = second := by
      change (basisOfLinearIndependentOfCardEqFinrank' _ _ _) 1 = _
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']
      rfl
    refine ⟨QuotientGroup.mk (rationalFrameOfBasis basis), ?_, ?_⟩
    · apply flagSubspace_injective
      rw [TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.endpoint_mk, flagSubspace_mk, line_frame_subspace,
        rationalFrameOfBasis_column, basisFirst, lineSpan]
    · apply flagSubspace_injective
      rw [TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.endpoint_mk, flagSubspace_mk, plane_frame_subspace,
        rationalFrameOfBasis_column, rationalFrameOfBasis_column, basisFirst, basisSecond,
        ← range_pair, planeSpan]

theorem pair_extends_rational_frame (first second : Fin 3 → ℚ)
    (independent : LinearIndependent ℚ ![first, second]) :
    ∃ frame : RationalGL3, frame.val.col 0 = first ∧ frame.val.col 1 = second := by
  have spanRank : Module.finrank ℚ (Submodule.span ℚ (Set.range ![first, second])) = 2 := by
    simpa using finrank_span_eq_card independent
  have proper : Submodule.span ℚ (Set.range ![first, second]) ≠ ⊤ := by
    intro equality
    rw [equality] at spanRank
    norm_num at spanRank
  have outside : ∃ third : Fin 3 → ℚ,
      third ∉ Submodule.span ℚ (Set.range ![first, second]) := by
    by_contra failure
    apply proper
    apply top_unique
    intro vector _membership
    by_contra nonmembership
    exact failure ⟨vector, nonmembership⟩
  obtain ⟨third, nonmembership⟩ := outside
  have tripleIndependent := independent.finSnoc nonmembership
  let basis := basisOfLinearIndependentOfCardEqFinrank'
    (Fin.snoc ![first, second] third) tripleIndependent (by simp)
  refine ⟨rationalFrameOfBasis basis, ?_, ?_⟩
  · rw [rationalFrameOfBasis_column]
    change (basisOfLinearIndependentOfCardEqFinrank' _ _ _) 0 = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    rfl
  · rw [rationalFrameOfBasis_column]
    change (basisOfLinearIndependentOfCardEqFinrank' _ _ _) 1 = _
    rw [coe_basisOfLinearIndependentOfCardEqFinrank']
    rfl

theorem line_subspace_le_of_generator_mem (lineFrame : RationalGL3)
    (subspace : Submodule ℚ (Fin 3 → ℚ)) (membership : lineFrame.val.col 0 ∈ subspace) :
    flagSubspace .line (QuotientGroup.mk lineFrame) ≤ subspace := by
  rw [flagSubspace_mk, line_frame_subspace]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr membership

theorem distinct_line_generators_independent (first second : RationalGL3)
    (distinct : (QuotientGroup.mk first : Flags .line) ≠ QuotientGroup.mk second) :
    LinearIndependent ℚ ![first.val.col 0, second.val.col 0] := by
  apply (LinearIndependent.pair_iff' (frame_column_ne_zero first 0)).mpr
  intro scalar equality
  apply distinct
  apply flagSubspace_injective
  apply Submodule.eq_of_le_of_finrank_eq
  · apply line_subspace_le_of_generator_mem
    rw [flagSubspace_mk, line_frame_subspace]
    have nonzero : scalar ≠ 0 := by
      intro zero
      rw [zero, zero_smul] at equality
      exact frame_column_ne_zero second 0 equality.symm
    have membership : scalar • first.val.col 0 ∈ Submodule.span ℚ {second.val.col 0} := by
      rw [equality]
      exact Submodule.mem_span_singleton_self _
    exact ((Submodule.span ℚ {second.val.col 0}).smul_mem_iff nonzero).mp membership
  · rw [flagSubspace_finrank, flagSubspace_finrank]

theorem good_plane_of_containing_good_line (line : Flags .line) (plane : Flags .plane)
    (good : GoodFlag .line line)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) : GoodFlag .plane plane := by
  rw [goodFlag_iff] at good ⊢
  obtain ⟨vector, membership, nonzero⟩ := good
  exact ⟨vector, incidence membership, nonzero⟩

theorem distinct_good_lines_common_plane (first second : Flags .line)
    (distinct : first ≠ second) (firstGood : GoodFlag .line first) :
    ∃ plane : Flags .plane, GoodFlag .plane plane ∧
      flagSubspace .line first ≤ flagSubspace .plane plane ∧
      flagSubspace .line second ≤ flagSubspace .plane plane := by
  induction first using Quotient.inductionOn with
  | h firstFrame =>
    induction second using Quotient.inductionOn with
    | h secondFrame =>
      obtain ⟨frame, firstColumn, secondColumn⟩ := pair_extends_rational_frame
        (firstFrame.val.col 0) (secondFrame.val.col 0)
        (distinct_line_generators_independent firstFrame secondFrame distinct)
      let plane : Flags .plane := QuotientGroup.mk frame
      have firstIncidence : flagSubspace .line (QuotientGroup.mk firstFrame) ≤
          flagSubspace .plane plane := by
        apply line_subspace_le_of_generator_mem
        change firstFrame.val.col 0 ∈ frameSubspace .plane frame
        rw [plane_frame_subspace, firstColumn, secondColumn]
        exact Submodule.subset_span (by simp)
      have secondIncidence : flagSubspace .line (QuotientGroup.mk secondFrame) ≤
          flagSubspace .plane plane := by
        apply line_subspace_le_of_generator_mem
        change secondFrame.val.col 0 ∈ frameSubspace .plane frame
        rw [plane_frame_subspace, firstColumn, secondColumn]
        exact Submodule.subset_span (by simp)
      exact ⟨plane, good_plane_of_containing_good_line _ plane firstGood firstIncidence,
        firstIncidence, secondIncidence⟩

theorem good_lines_chain_connected (first second : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second) :
    ∃ chain : EdgeChains, GoodChain chain ∧
      chainBoundary chain = Finsupp.single (Sum.inr second) 1 -
        Finsupp.single (Sum.inr first) 1 := by
  classical
  by_cases equality : first = second
  · refine ⟨0, ?_, ?_⟩
    · intro edge supported
      simp at supported
    · simp [equality]
  · obtain ⟨plane, _planeGood, firstIncidence, secondIncidence⟩ :=
      distinct_good_lines_common_plane first second equality firstGood
    obtain ⟨firstEdge, firstLine, firstPlane⟩ := edge_exists_of_incident first plane firstIncidence
    obtain ⟨secondEdge, secondLine, secondPlane⟩ := edge_exists_of_incident second plane secondIncidence
    refine ⟨Finsupp.single firstEdge 1 - Finsupp.single secondEdge 1, ?_, ?_⟩
    · rw [← TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.mem_goodChains]
      apply Submodule.sub_mem
      · apply TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.goodChains_single
        exact ⟨TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry.good_plane_of_good_line firstEdge (firstLine ▸ firstGood),
          firstLine ▸ firstGood⟩
      · apply TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.goodChains_single
        exact ⟨TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry.good_plane_of_good_line secondEdge (secondLine ▸ secondGood),
          secondLine ▸ secondGood⟩
    · simp only [map_sub, TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.chainBoundary_single, one_smul,
        firstLine, firstPlane, secondLine, secondPlane]
      abel

theorem good_plane_contains_good_line (plane : Flags .plane) (good : GoodFlag .plane plane) :
    ∃ line : Flags .line, GoodFlag .line line ∧
      flagSubspace .line line ≤ flagSubspace .plane plane := by
  rw [goodFlag_iff] at good
  obtain ⟨integral, membership, lastNonzero⟩ := good
  let first : Fin 3 → ℚ := integerVectorMap integral
  have firstNonzero : first ≠ 0 := by
    intro zero
    have coordinate : (integral 2 : ℚ) = 0 := congrFun zero 2
    have integerZero : integral 2 = 0 := Int.cast_eq_zero.mp coordinate
    apply lastNonzero
    rw [integerZero, Int.cast_zero]
  have secondExists : ∃ second ∈ flagSubspace .plane plane,
      second ∉ Submodule.span ℚ {first} := by
    by_contra failure
    have inclusion : flagSubspace .plane plane ≤ Submodule.span ℚ {first} := by
      intro vector vectorMembership
      by_contra nonmembership
      exact failure ⟨vector, vectorMembership, nonmembership⟩
    have rank := Submodule.finrank_mono inclusion
    rw [flagSubspace_finrank, finrank_span_singleton firstNonzero] at rank
    change 2 ≤ 1 at rank
    omega
  obtain ⟨second, secondMembership, secondOutside⟩ := secondExists
  have independent : LinearIndependent ℚ ![first, second] := by
    apply (LinearIndependent.pair_iff' firstNonzero).mpr
    intro scalar equality
    apply secondOutside
    rw [← equality]
    exact Submodule.smul_mem _ scalar (Submodule.mem_span_singleton_self first)
  obtain ⟨frame, firstColumn, _secondColumn⟩ := pair_extends_rational_frame first second independent
  let line : Flags .line := QuotientGroup.mk frame
  refine ⟨line, ?_, ?_⟩
  · rw [goodFlag_iff]
    refine ⟨integral, ?_, lastNonzero⟩
    change first ∈ frameSubspace .line frame
    rw [line_frame_subspace, firstColumn]
    exact Submodule.mem_span_singleton_self first
  · apply line_subspace_le_of_generator_mem
    rw [firstColumn]
    exact membership

def GoodVertex : BuildingVertices → Prop
  | .inl plane => GoodFlag .plane plane
  | .inr line => GoodFlag .line line

theorem good_vertex_to_line (vertex : BuildingVertices) (good : GoodVertex vertex) :
    ∃ (line : Flags .line) (chain : EdgeChains), GoodFlag .line line ∧ GoodChain chain ∧
      chainBoundary chain = Finsupp.single (Sum.inr line) 1 - Finsupp.single vertex 1 := by
  cases vertex with
  | inl plane =>
    obtain ⟨line, lineGood, incidence⟩ := good_plane_contains_good_line plane good
    obtain ⟨edge, lineEquality, planeEquality⟩ := edge_exists_of_incident line plane incidence
    refine ⟨line, -Finsupp.single edge 1, lineGood, ?_, ?_⟩
    · rw [← TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.mem_goodChains]
      apply Submodule.neg_mem
      apply TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.goodChains_single
      exact ⟨planeEquality ▸ good, lineEquality ▸ lineGood⟩
    · simp only [map_neg, TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.chainBoundary_single, one_smul,
        lineEquality, planeEquality]
      abel
  | inr line =>
    refine ⟨line, 0, good, ?_, ?_⟩
    · intro edge supported
      simp at supported
    · simp

theorem good_vertices_chain_connected (first second : BuildingVertices)
    (firstGood : GoodVertex first) (secondGood : GoodVertex second) :
    ∃ chain : EdgeChains, GoodChain chain ∧
      chainBoundary chain = Finsupp.single second 1 - Finsupp.single first 1 := by
  obtain ⟨firstLine, firstConnector, firstLineGood, firstConnectorGood, firstBoundary⟩ :=
    good_vertex_to_line first firstGood
  obtain ⟨secondLine, secondConnector, secondLineGood, secondConnectorGood, secondBoundary⟩ :=
    good_vertex_to_line second secondGood
  obtain ⟨middle, middleGood, middleBoundary⟩ :=
    good_lines_chain_connected firstLine secondLine firstLineGood secondLineGood
  refine ⟨firstConnector + middle - secondConnector, ?_, ?_⟩
  · rw [← TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers.mem_goodChains] at firstConnectorGood middleGood secondConnectorGood ⊢
    exact Submodule.sub_mem _ (Submodule.add_mem _ firstConnectorGood middleGood) secondConnectorGood
  · rw [map_sub, map_add, firstBoundary, secondBoundary, middleBoundary]
    abel

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
