module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.GenericLine

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.GenericLine

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments

noncomputable section

theorem plane_span_of_distinct_lines (first second : Flags .line) (plane : Flags .plane)
    (distinct : first ≠ second)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane) :
    flagSubspace .line first ⊔ flagSubspace .line second = flagSubspace .plane plane := by
  induction first using Quotient.inductionOn with
  | h firstFrame =>
    induction second using Quotient.inductionOn with
    | h secondFrame =>
      have independent := distinct_line_generators_independent firstFrame secondFrame distinct
      have rank : Module.finrank ℚ
          (Submodule.span ℚ {firstFrame.val.col 0, secondFrame.val.col 0}) = 2 := by
        rw [← range_pair]
        simpa using finrank_span_eq_card independent
      rw [flagSubspace_mk, flagSubspace_mk, line_frame_subspace, line_frame_subspace,
        ← Submodule.span_union]
      change Submodule.span ℚ {firstFrame.val.col 0, secondFrame.val.col 0} = _
      apply Submodule.eq_of_le_of_finrank_eq
      · apply Submodule.span_le.mpr
        intro vector membership
        rcases membership with rfl | membership
        · apply firstIncidence
          rw [flagSubspace_mk, line_frame_subspace]
          exact Submodule.mem_span_singleton_self _
        · rw [Set.mem_singleton_iff.mp membership]
          apply secondIncidence
          rw [flagSubspace_mk, line_frame_subspace]
          exact Submodule.mem_span_singleton_self _
      · rw [rank, flagSubspace_finrank]

theorem plane_unique_of_distinct_lines (first second : Flags .line)
    (firstPlane secondPlane : Flags .plane) (distinct : first ≠ second)
    (firstFirst : flagSubspace .line first ≤ flagSubspace .plane firstPlane)
    (secondFirst : flagSubspace .line second ≤ flagSubspace .plane firstPlane)
    (firstSecond : flagSubspace .line first ≤ flagSubspace .plane secondPlane)
    (secondSecond : flagSubspace .line second ≤ flagSubspace .plane secondPlane) :
    firstPlane = secondPlane := by
  apply flagSubspace_injective
  rw [← plane_span_of_distinct_lines first second firstPlane distinct firstFirst secondFirst,
    ← plane_span_of_distinct_lines first second secondPlane distinct firstSecond secondSecond]

def incidenceEdge (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) : Edges :=
  Classical.choose (edge_exists_of_incident line plane incidence)

theorem incidenceEdge_line (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) :
    endpoint .line (incidenceEdge line plane incidence) = line :=
  (Classical.choose_spec (edge_exists_of_incident line plane incidence)).1

theorem incidenceEdge_plane (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) :
    endpoint .plane (incidenceEdge line plane incidence) = plane :=
  (Classical.choose_spec (edge_exists_of_incident line plane incidence)).2

def incidenceChain (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) : EdgeChains :=
  Finsupp.single (incidenceEdge line plane incidence) 1

theorem incidenceChain_boundary (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane) :
    chainBoundary (incidenceChain line plane incidence) =
      Finsupp.single (Sum.inl plane) 1 - Finsupp.single (Sum.inr line) 1 := by
  simp [incidenceChain, chainBoundary_single, incidenceEdge_line, incidenceEdge_plane]

theorem incidenceChain_good (line : Flags .line) (plane : Flags .plane)
    (incidence : flagSubspace .line line ≤ flagSubspace .plane plane)
    (good : GoodFlag .line line) : incidenceChain line plane incidence ∈ goodChains := by
  apply goodChains_single
  change GoodFlag .plane (endpoint .plane (incidenceEdge line plane incidence)) ∧
    GoodFlag .line (endpoint .line (incidenceEdge line plane incidence))
  rw [incidenceEdge_plane, incidenceEdge_line]
  exact ⟨good_plane_of_containing_good_line line plane good incidence, good⟩

theorem incidenceChain_of_edge (edge : Edges) :
    incidenceChain (endpoint .line edge) (endpoint .plane edge) (edge_subspace_incidence edge) =
      Finsupp.single edge 1 := by
  unfold incidenceChain
  congr 1
  exact edge_eq_of_endpoints_eq _ edge
    (incidenceEdge_plane _ _ _) (incidenceEdge_line _ _ _)

def selectedGoodLine (plane : Flags .plane) (good : GoodFlag .plane plane) : Flags .line :=
  Classical.choose (good_plane_contains_good_line plane good)

theorem selectedGoodLine_good (plane : Flags .plane) (good : GoodFlag .plane plane) :
    GoodFlag .line (selectedGoodLine plane good) :=
  (Classical.choose_spec (good_plane_contains_good_line plane good)).1

theorem selectedGoodLine_incidence (plane : Flags .plane) (good : GoodFlag .plane plane) :
    flagSubspace .line (selectedGoodLine plane good) ≤ flagSubspace .plane plane :=
  (Classical.choose_spec (good_plane_contains_good_line plane good)).2

def pairPlane (first second : Flags .line) (distinct : first ≠ second)
    (good : GoodFlag .line first) : Flags .plane :=
  Classical.choose (distinct_good_lines_common_plane first second distinct good)

theorem pairPlane_first (first second : Flags .line) (distinct : first ≠ second)
    (good : GoodFlag .line first) :
    flagSubspace .line first ≤ flagSubspace .plane (pairPlane first second distinct good) :=
  (Classical.choose_spec (distinct_good_lines_common_plane first second distinct good)).2.1

theorem pairPlane_second (first second : Flags .line) (distinct : first ≠ second)
    (good : GoodFlag .line first) :
    flagSubspace .line second ≤ flagSubspace .plane (pairPlane first second distinct good) :=
  (Classical.choose_spec (distinct_good_lines_common_plane first second distinct good)).2.2

def lineConnector (first second : Flags .line) (firstGood : GoodFlag .line first) : EdgeChains := by
  classical
  exact
  if distinct : first ≠ second then
    incidenceChain first (pairPlane first second distinct firstGood)
      (pairPlane_first first second distinct firstGood) -
    incidenceChain second (pairPlane first second distinct firstGood)
      (pairPlane_second first second distinct firstGood)
  else 0

theorem lineConnector_self (line : Flags .line) (good : GoodFlag .line line) :
    lineConnector line line good = 0 := by
  simp [lineConnector]

theorem lineConnector_boundary (first second : Flags .line) (good : GoodFlag .line first) :
    chainBoundary (lineConnector first second good) =
      Finsupp.single (Sum.inr second) 1 - Finsupp.single (Sum.inr first) 1 := by
  classical
  by_cases distinct : first ≠ second
  · simp only [lineConnector, dite_eq_left distinct, map_sub, incidenceChain_boundary]
    abel
  · simp [lineConnector, not_not.mp distinct]

theorem lineConnector_good (first second : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second) :
    lineConnector first second firstGood ∈ goodChains := by
  classical
  by_cases distinct : first ≠ second
  · simp only [lineConnector, dite_eq_left distinct]
    exact goodChains.sub_mem (incidenceChain_good _ _ _ firstGood)
      (incidenceChain_good _ _ _ secondGood)
  · simp [lineConnector, distinct]

theorem lineConnector_of_common_plane (first second : Flags .line) (plane : Flags .plane)
    (good : GoodFlag .line first) (distinct : first ≠ second)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane) :
    lineConnector first second good = incidenceChain first plane firstIncidence -
      incidenceChain second plane secondIncidence := by
  classical
  have planeEquality := plane_unique_of_distinct_lines first second
    (pairPlane first second distinct good) plane distinct
    (pairPlane_first first second distinct good) (pairPlane_second first second distinct good)
    firstIncidence secondIncidence
  simp only [lineConnector, dite_eq_left distinct]
  subst plane
  rfl

theorem lineConnector_reverse (first second : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second) :
    lineConnector second first secondGood = -lineConnector first second firstGood := by
  classical
  by_cases equality : first = second
  · subst second
    simp [lineConnector_self]
  · rw [lineConnector_of_common_plane second first (pairPlane first second equality firstGood)
      secondGood (Ne.symm equality) (pairPlane_second first second equality firstGood)
      (pairPlane_first first second equality firstGood)]
    simp only [lineConnector, dite_eq_left equality]
    abel

theorem lineConnector_on_edge_plane (first second : Flags .line) (plane : Flags .plane)
    (good : GoodFlag .line first)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane) :
    lineConnector first second good = incidenceChain first plane firstIncidence -
      incidenceChain second plane secondIncidence := by
  by_cases equality : first = second
  · subst second
    simp [lineConnector_self]
  · exact lineConnector_of_common_plane first second plane good equality firstIncidence secondIncidence

theorem rotated_frame_column (frame : RationalGL3) (rotation : Fin 3) (column : Fin 3) :
    (frame * Adelic.weyl ^ rotation.val).val.col column =
      frame.val.col (rotation + column) := by
  ext row
  fin_cases rotation <;> fin_cases column <;>
    simp [Matrix.col, Adelic.weyl, pow_two,
      Matrix.mul_apply, Fin.sum_univ_three]

def columnLine (frame : RationalGL3) (column : Fin 3) : Flags .line :=
  QuotientGroup.mk (frame * Adelic.weyl ^ column.val)

def columnPlane (frame : RationalGL3) (column : Fin 3) : Flags .plane :=
  QuotientGroup.mk (frame * Adelic.weyl ^ column.val)

theorem columnLine_subspace (frame : RationalGL3) (column : Fin 3) :
    flagSubspace .line (columnLine frame column) = Submodule.span ℚ {frame.val.col column} := by
  rw [columnLine, flagSubspace_mk, line_frame_subspace, rotated_frame_column]
  simp

theorem columnPlane_subspace (frame : RationalGL3) (column : Fin 3) :
    flagSubspace .plane (columnPlane frame column) =
      Submodule.span ℚ {frame.val.col column, frame.val.col (column + 1)} := by
  rw [columnPlane, flagSubspace_mk, plane_frame_subspace,
    rotated_frame_column, rotated_frame_column]
  simp

theorem columnLine_first_incidence (frame : RationalGL3) (column : Fin 3) :
    flagSubspace .line (columnLine frame column) ≤ flagSubspace .plane (columnPlane frame column) := by
  rw [columnLine_subspace, columnPlane_subspace]
  apply Submodule.span_mono
  intro vector membership
  simp only [Set.mem_singleton_iff] at membership
  simp [membership]

theorem columnLine_second_incidence (frame : RationalGL3) (column : Fin 3) :
    flagSubspace .line (columnLine frame (column + 1)) ≤
      flagSubspace .plane (columnPlane frame column) := by
  rw [columnLine_subspace, columnPlane_subspace]
  apply Submodule.span_mono
  intro vector membership
  simp only [Set.mem_singleton_iff] at membership
  simp [membership]

theorem incidenceChain_frame_first (frame : RationalGL3) (column : Fin 3) :
    incidenceChain (columnLine frame column) (columnPlane frame column)
      (columnLine_first_incidence frame column) =
      Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val)) 1 := by
  unfold incidenceChain
  congr 1
  apply edge_eq_of_endpoints_eq
  · exact incidenceEdge_plane _ _ _
  · exact incidenceEdge_line _ _ _

theorem incidenceChain_frame_second (frame : RationalGL3) (column : Fin 3) :
    incidenceChain (columnLine frame (column + 1)) (columnPlane frame column)
      (columnLine_second_incidence frame column) =
      Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val * swapFirstTwo)) 1 := by
  unfold incidenceChain
  congr 1
  apply edge_eq_of_endpoints_eq
  · rw [incidenceEdge_plane, endpoint_mk, plane_swapFirstTwo]
    rfl
  · rw [incidenceEdge_line, endpoint_mk, line_swapFirstTwo]
    apply flagSubspace_injective
    rw [columnLine_subspace, flagSubspace_mk, line_frame_subspace]
    have last := rotated_frame_column (frame * Adelic.weyl ^ column.val) 1 0
    simp only [Fin.val_one, pow_one, add_zero] at last
    rw [last, rotated_frame_column]

theorem apartment_as_lineConnectors (frame : RationalGL3)
    (good : ∀ column, GoodFlag .line (columnLine frame column)) :
    apartment frame =
      lineConnector (columnLine frame 0) (columnLine frame 1) (good 0) +
      lineConnector (columnLine frame 1) (columnLine frame 2) (good 1) +
      lineConnector (columnLine frame 2) (columnLine frame 0) (good 2) := by
  have connector (column : Fin 3) :
      lineConnector (columnLine frame column) (columnLine frame (column + 1)) (good column) =
        Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val)) 1 -
          Finsupp.single (QuotientGroup.mk (frame * Adelic.weyl ^ column.val * swapFirstTwo)) 1 := by
    rw [lineConnector_on_edge_plane _ _ (columnPlane frame column) (good column)
      (columnLine_first_incidence frame column) (columnLine_second_incidence frame column),
      incidenceChain_frame_first, incidenceChain_frame_second]
  have first := connector 0
  have second := connector 1
  have third := connector 2
  change lineConnector (columnLine frame 0) (columnLine frame 1) (good 0) = _ at first
  change lineConnector (columnLine frame 1) (columnLine frame 2) (good 1) = _ at second
  change lineConnector (columnLine frame 2) (columnLine frame 0) (good 2) = _ at third
  rw [first, second, third]
  simp only [apartment, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
  abel

def vertexConnector (base : Flags .line) (vertex : BuildingVertices) : EdgeChains := by
  classical
  exact
  if good : GoodVertex vertex then
    match vertex with
    | .inr line => lineConnector line base good
    | .inl plane =>
      -incidenceChain (selectedGoodLine plane good) plane (selectedGoodLine_incidence plane good) +
        lineConnector (selectedGoodLine plane good) base (selectedGoodLine_good plane good)
  else 0

theorem vertexConnector_good (base : Flags .line) (baseGood : GoodFlag .line base)
    (vertex : BuildingVertices) : vertexConnector base vertex ∈ goodChains := by
  classical
  by_cases good : GoodVertex vertex
  · cases vertex with
    | inr line =>
      simp only [vertexConnector, dite_eq_left good]
      exact lineConnector_good _ _ good baseGood
    | inl plane =>
      simp only [vertexConnector, dite_eq_left good]
      exact goodChains.add_mem
        (goodChains.neg_mem (incidenceChain_good _ _ _ (selectedGoodLine_good plane good)))
        (lineConnector_good _ _ (selectedGoodLine_good plane good) baseGood)
  · simp [vertexConnector, good]

theorem vertexConnector_boundary (base : Flags .line) (vertex : BuildingVertices)
    (good : GoodVertex vertex) :
    chainBoundary (vertexConnector base vertex) =
      Finsupp.single (Sum.inr base) 1 - Finsupp.single vertex 1 := by
  classical
  cases vertex with
  | inr line =>
    simp only [vertexConnector, dite_eq_left good]
    exact lineConnector_boundary _ _ good
  | inl plane =>
    simp only [vertexConnector, dite_eq_left good, map_add, map_neg, incidenceChain_boundary,
      lineConnector_boundary]
    abel

def connectorMap (base : Flags .line) : VertexChains →ₗ[ℂ] EdgeChains :=
  Finsupp.linearCombination ℂ (vertexConnector base)

def residualMap (base : Flags .line) : EdgeChains →ₗ[ℂ] EdgeChains :=
  LinearMap.id + (connectorMap base).comp chainBoundary

def edgeResidual (base : Flags .line) (edge : Edges) : EdgeChains :=
  Finsupp.single edge 1 + vertexConnector base (Sum.inl (endpoint .plane edge)) -
    vertexConnector base (Sum.inr (endpoint .line edge))

theorem residualMap_single (base : Flags .line) (edge : Edges) (coefficient : ℂ) :
    residualMap base (Finsupp.single edge coefficient) = coefficient • edgeResidual base edge := by
  simp [residualMap, connectorMap, chainBoundary_single, edgeResidual,
    smul_add, smul_sub, Finsupp.smul_single]
  abel

theorem edgeResidual_goodCycle (base : Flags .line) (baseGood : GoodFlag .line base)
    (edge : Edges) (good : edge ∈ goodEdges) : GoodCycle (edgeResidual base edge) := by
  constructor
  · simp only [edgeResidual, map_sub, map_add, chainBoundary_single, one_smul]
    rw [vertexConnector_boundary base (Sum.inl (endpoint .plane edge)) good.1,
      vertexConnector_boundary base (Sum.inr (endpoint .line edge)) good.2]
    abel
  · rw [← mem_goodChains]
    exact goodChains.sub_mem
      (goodChains.add_mem (goodChains_single edge 1 good) (vertexConnector_good base baseGood _))
      (vertexConnector_good base baseGood _)

theorem goodCycle_in_span_edgeResiduals (base : Flags .line) (chain : EdgeChains)
    (good : GoodCycle chain) :
    chain ∈ Submodule.span ℂ {residual : EdgeChains |
      ∃ edge ∈ goodEdges, residual = edgeResidual base edge} := by
  classical
  have fixed : residualMap base chain = chain := by
    simp [residualMap, good.1]
  rw [← fixed, ← Finsupp.sum_single chain, map_finsuppSum]
  apply Submodule.sum_mem
  intro edge membership
  dsimp only
  rw [residualMap_single]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨edge, good.2 edge membership, rfl⟩

theorem three_lines_rational_frame (first second third : Flags .line)
    (plane : Flags .plane) (distinct : first ≠ second)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane)
    (thirdOutside : ¬flagSubspace .line third ≤ flagSubspace .plane plane) :
    ∃ frame : RationalGL3,
      columnLine frame 0 = first ∧ columnLine frame 1 = second ∧ columnLine frame 2 = third := by
  induction first using Quotient.inductionOn with
  | h firstFrame =>
    induction second using Quotient.inductionOn with
    | h secondFrame =>
      induction third using Quotient.inductionOn with
      | h thirdFrame =>
        have independent := distinct_line_generators_independent firstFrame secondFrame distinct
        have planeSpan : Submodule.span ℚ
            (Set.range ![firstFrame.val.col 0, secondFrame.val.col 0]) =
              flagSubspace .plane plane := by
          rw [range_pair]
          have equality := plane_span_of_distinct_lines _ _ plane distinct
            firstIncidence secondIncidence
          simpa only [flagSubspace_mk, line_frame_subspace,
            ← Submodule.span_union, Set.singleton_union] using equality
        have outside : thirdFrame.val.col 0 ∉ Submodule.span ℚ
            (Set.range ![firstFrame.val.col 0, secondFrame.val.col 0]) := by
          rw [planeSpan]
          intro membership
          exact thirdOutside (line_subspace_le_of_generator_mem thirdFrame _ membership)
        let vectors : Fin 3 → Fin 3 → ℚ := Fin.snoc ![firstFrame.val.col 0, secondFrame.val.col 0]
          (thirdFrame.val.col 0)
        let basis := basisOfLinearIndependentOfCardEqFinrank' vectors
          (independent.finSnoc outside) (by simp)
        let frame := rationalFrameOfBasis basis
        have column (index : Fin 3) : frame.val.col index = vectors index := by
          rw [rationalFrameOfBasis_column]
          exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) index
        refine ⟨frame, ?_, ?_, ?_⟩
        · apply flagSubspace_injective
          rw [columnLine_subspace, column, flagSubspace_mk, line_frame_subspace]
          rfl
        · apply flagSubspace_injective
          rw [columnLine_subspace, column, flagSubspace_mk, line_frame_subspace]
          rfl
        · apply flagSubspace_injective
          rw [columnLine_subspace, column, flagSubspace_mk, line_frame_subspace]
          rfl

def rationalApartmentSpan : Submodule ℂ EdgeChains :=
  Submodule.span ℂ {chain | ∃ frame : RationalGL3,
    (∀ column, GoodFlag .line (columnLine frame column)) ∧ chain = apartment frame}

theorem line_triangle_mem_rationalApartmentSpan (first second third : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second)
    (thirdGood : GoodFlag .line third) (plane : Flags .plane)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane)
    (thirdOutside : ¬flagSubspace .line third ≤ flagSubspace .plane plane) :
    lineConnector first second firstGood + lineConnector second third secondGood +
      lineConnector third first thirdGood ∈ rationalApartmentSpan := by
  by_cases equality : first = second
  · subst second
    rw [lineConnector_self, zero_add, lineConnector_reverse third first thirdGood firstGood]
    simp
  · obtain ⟨frame, firstColumn, secondColumn, thirdColumn⟩ :=
      three_lines_rational_frame first second third plane equality
        firstIncidence secondIncidence thirdOutside
    have good : ∀ column, GoodFlag .line (columnLine frame column) := by
      intro column
      fin_cases column
      · change GoodFlag .line (columnLine frame 0)
        exact firstColumn.symm ▸ firstGood
      · change GoodFlag .line (columnLine frame 1)
        exact secondColumn.symm ▸ secondGood
      · change GoodFlag .line (columnLine frame 2)
        exact thirdColumn.symm ▸ thirdGood
    have apartmentEquality := apartment_as_lineConnectors frame good
    have equality : apartment frame =
        lineConnector first second firstGood + lineConnector second third secondGood +
          lineConnector third first thirdGood := by
      subst first second third
      exact apartmentEquality
    rw [← equality]
    exact Submodule.subset_span ⟨frame, good, rfl⟩

theorem edgeResidual_mem_rationalApartmentSpan (base : Flags .line)
    (baseGood : GoodFlag .line base) (edge : Edges) (good : edge ∈ goodEdges)
    (outside : ¬flagSubspace .line base ≤ flagSubspace .plane (endpoint .plane edge)) :
    edgeResidual base edge ∈ rationalApartmentSpan := by
  classical
  let selected := selectedGoodLine (endpoint .plane edge) good.1
  have selectedGood := selectedGoodLine_good (endpoint .plane edge) good.1
  have selectedIncidence := selectedGoodLine_incidence (endpoint .plane edge) good.1
  have triangle := line_triangle_mem_rationalApartmentSpan
    (endpoint .line edge) selected base good.2 selectedGood baseGood
    (endpoint .plane edge) (edge_subspace_incidence edge) selectedIncidence outside
  rw [lineConnector_on_edge_plane _ _ _ good.2
      (edge_subspace_incidence edge) selectedIncidence,
    incidenceChain_of_edge, lineConnector_reverse (endpoint .line edge) base good.2 baseGood]
      at triangle
  have equality : edgeResidual base edge =
      Finsupp.single edge 1 - incidenceChain selected (endpoint .plane edge) selectedIncidence +
        lineConnector selected base selectedGood - lineConnector (endpoint .line edge) base good.2 := by
    have planeGood : GoodVertex (Sum.inl (endpoint .plane edge)) := good.1
    have lineGood : GoodVertex (Sum.inr (endpoint .line edge)) := good.2
    simp only [edgeResidual, vertexConnector, dite_eq_left planeGood, dite_eq_left lineGood]
    dsimp only [selected] at *
    abel
  rw [equality]
  simpa only [sub_eq_add_neg] using triangle

theorem goodCycle_mem_rationalApartmentSpan (chain : EdgeChains) (good : GoodCycle chain) :
    chain ∈ rationalApartmentSpan := by
  classical
  let planes := chain.support.image (endpoint .plane)
  obtain ⟨base, baseGood, outside⟩ := good_line_avoiding_finite_planes planes
  have fixed : residualMap base chain = chain := by
    simp [residualMap, good.1]
  rw [← fixed, ← Finsupp.sum_single chain, map_finsuppSum]
  apply Submodule.sum_mem
  intro edge membership
  dsimp only
  rw [residualMap_single]
  apply Submodule.smul_mem
  apply edgeResidual_mem_rationalApartmentSpan base baseGood edge (good.2 edge membership)
  exact outside _ (Finset.mem_image.mpr ⟨edge, membership, rfl⟩)

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments
