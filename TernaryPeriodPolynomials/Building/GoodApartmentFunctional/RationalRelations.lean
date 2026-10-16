module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.IntegralReduction

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
open TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments TernaryPeriodPolynomials.GoodApartmentFunctional.ApartmentGeneration

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations

noncomputable section

abbrev GoodLines := {line : Flags .line // GoodFlag .line line}

abbrev Triples := GoodLines × GoodLines × GoodLines

abbrev TripleChains := Triples →₀ ℂ

def triple (first second third : GoodLines) : TripleChains :=
  Finsupp.single (first, second, third) 1

def cycleRelation (first second third : GoodLines) : TripleChains :=
  triple first second third - triple second third first

def swapRelation (first second third : GoodLines) : TripleChains :=
  triple first second third + triple second first third

def subdivisionRelation (first second third inserted : GoodLines) : TripleChains :=
  triple first second third -
    (triple inserted second third + triple first inserted third + triple first second inserted)

def coplanarTriples : Set Triples :=
  {value | ∃ plane : Flags .plane,
    flagSubspace .line value.1.val ≤ flagSubspace .plane plane ∧
    flagSubspace .line value.2.1.val ≤ flagSubspace .plane plane ∧
    flagSubspace .line value.2.2.val ≤ flagSubspace .plane plane}

def rationalRelations : Submodule ℂ TripleChains :=
  Submodule.span ℂ
    ({value | ∃ first second third, value = cycleRelation first second third} ∪
      {value | ∃ first second third, value = swapRelation first second third} ∪
      {value | ∃ first second third inserted,
        value = subdivisionRelation first second third inserted} ∪
      {value | ∃ vertices ∈ coplanarTriples, value = Finsupp.single vertices 1})

abbrev RationalSymbols := TripleChains ⧸ rationalRelations

def symbol (first second third : GoodLines) : RationalSymbols :=
  rationalRelations.mkQ (triple first second third)

theorem symbol_cycle (first second third : GoodLines) :
    symbol first second third = symbol second third first := by
  have membership : cycleRelation first second third ∈ rationalRelations :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨first, second, third, rfl⟩)))
  have zero : rationalRelations.mkQ (cycleRelation first second third) = 0 :=
    (Submodule.Quotient.mk_eq_zero rationalRelations).mpr membership
  simpa only [cycleRelation, map_sub, symbol, sub_eq_zero] using zero

theorem symbol_swap (first second third : GoodLines) :
    symbol second first third = -symbol first second third := by
  have membership : swapRelation first second third ∈ rationalRelations :=
    Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨first, second, third, rfl⟩)))
  have zero : rationalRelations.mkQ (swapRelation first second third) = 0 :=
    (Submodule.Quotient.mk_eq_zero rationalRelations).mpr membership
  have addition : symbol first second third + symbol second first third = 0 := by
    simpa only [swapRelation, map_add, symbol] using zero
  exact eq_neg_of_add_eq_zero_right addition

theorem symbol_subdivision (first second third inserted : GoodLines) :
    symbol first second third = symbol inserted second third +
      symbol first inserted third + symbol first second inserted := by
  have membership : subdivisionRelation first second third inserted ∈ rationalRelations :=
    Submodule.subset_span (Or.inl (Or.inr ⟨first, second, third, inserted, rfl⟩))
  have zero : rationalRelations.mkQ (subdivisionRelation first second third inserted) = 0 :=
    (Submodule.Quotient.mk_eq_zero rationalRelations).mpr membership
  simpa only [subdivisionRelation, map_sub, map_add, symbol, sub_eq_zero] using zero

theorem symbol_coplanar (first second third : GoodLines) (plane : Flags .plane)
    (firstIncidence : flagSubspace .line first.val ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second.val ≤ flagSubspace .plane plane)
    (thirdIncidence : flagSubspace .line third.val ≤ flagSubspace .plane plane) :
    symbol first second third = 0 := by
  apply (Submodule.Quotient.mk_eq_zero rationalRelations).mpr
  exact Submodule.subset_span (Or.inr
    ⟨(first, second, third), ⟨plane, firstIncidence, secondIncidence, thirdIncidence⟩, rfl⟩)

theorem symbol_base_triangle (base first second third : GoodLines) :
    symbol first second third = symbol base first second + symbol base second third +
      symbol base third first := by
  have middle := symbol_cycle first base third
  have last := (symbol_cycle base first second).symm
  rw [symbol_subdivision first second third base, middle, last]
  abel

theorem symbol_base_coplanar (base first second third : GoodLines) (plane : Flags .plane)
    (firstIncidence : flagSubspace .line first.val ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second.val ≤ flagSubspace .plane plane)
    (thirdIncidence : flagSubspace .line third.val ≤ flagSubspace .plane plane) :
    symbol base first second = symbol base first third - symbol base second third := by
  have zero := symbol_coplanar first second third plane firstIncidence secondIncidence thirdIncidence
  have reverse : symbol base third first = -symbol base first third := by
    calc
      symbol base third first = symbol third first base := symbol_cycle base third first
      _ = -symbol first third base := symbol_swap first third base
      _ = -symbol base first third := congrArg Neg.neg (symbol_cycle base first third).symm
  rw [symbol_base_triangle base, reverse] at zero
  rw [← sub_eq_add_neg] at zero
  calc
    symbol base first second = symbol base first second -
        (symbol base first second + symbol base second third - symbol base first third) := by
      rw [zero, sub_zero]
    _ = symbol base first third - symbol base second third := by abel

def tripleApartment (vertices : Triples) : goodCycles :=
  ⟨lineTriangle vertices.1.val vertices.2.1.val vertices.2.2.val
      vertices.1.property vertices.2.1.property vertices.2.2.property,
    (mem_goodCycles _).mpr (lineTriangle_goodCycle _ _ _ _ _ _)⟩

def trianglePresentation : TripleChains →ₗ[ℂ] goodCycles :=
  Finsupp.linearCombination ℂ tripleApartment

theorem trianglePresentation_triple (first second third : GoodLines) :
    (trianglePresentation (triple first second third)).val =
      lineTriangle first.val second.val third.val first.property second.property third.property := by
  simp [trianglePresentation, triple, tripleApartment]

theorem trianglePresentation_cycle (first second third : GoodLines) :
    trianglePresentation (cycleRelation first second third) = 0 := by
  apply Subtype.ext
  simp only [cycleRelation, map_sub, Submodule.coe_sub, trianglePresentation_triple,
    ZeroMemClass.coe_zero, lineTriangle]
  abel

theorem trianglePresentation_swap (first second third : GoodLines) :
    trianglePresentation (swapRelation first second third) = 0 := by
  apply Subtype.ext
  simp only [swapRelation, map_add, Submodule.coe_add, trianglePresentation_triple,
    ZeroMemClass.coe_zero, lineTriangle,
    lineConnector_reverse second.val first.val second.property first.property,
    lineConnector_reverse third.val second.val third.property second.property,
    lineConnector_reverse first.val third.val first.property third.property]
  abel

theorem trianglePresentation_subdivision (first second third inserted : GoodLines) :
    trianglePresentation (subdivisionRelation first second third inserted) = 0 := by
  apply Subtype.ext
  simp only [subdivisionRelation, map_sub, map_add, Submodule.coe_sub, Submodule.coe_add,
    trianglePresentation_triple, ZeroMemClass.coe_zero]
  exact sub_eq_zero.mpr (lineTriangle_subdivision _ _ _ _ _ _ _ _)

theorem rationalRelations_in_kernel : rationalRelations ≤ trianglePresentation.ker := by
  apply Submodule.span_le.mpr
  intro combination membership
  rcases membership with ((⟨first, second, third, rfl⟩ | ⟨first, second, third, rfl⟩) |
      ⟨first, second, third, inserted, rfl⟩) | ⟨vertices, ⟨plane, incidence⟩, rfl⟩
  · exact trianglePresentation_cycle first second third
  · exact trianglePresentation_swap first second third
  · exact trianglePresentation_subdivision first second third inserted
  · apply Subtype.ext
    simp only [trianglePresentation, Finsupp.linearCombination_single, one_smul,
      tripleApartment, ZeroMemClass.coe_zero]
    exact lineTriangle_coplanar _ _ _ _ _ _ plane incidence.1 incidence.2.1 incidence.2.2

def edgeSymbol (base : GoodLines) (edge : Edges) : RationalSymbols := by
  classical
  exact if good : edge ∈ goodEdges then
    symbol base ⟨endpoint .line edge, good.2⟩
      ⟨selectedGoodLine (endpoint .plane edge) good.1,
        selectedGoodLine_good (endpoint .plane edge) good.1⟩
  else 0

def edgeSymbolMap (base : GoodLines) : EdgeChains →ₗ[ℂ] RationalSymbols :=
  Finsupp.linearCombination ℂ (edgeSymbol base)

theorem edgeSymbolMap_incidenceChain (base line : GoodLines) (plane : Flags .plane)
    (incidence : flagSubspace .line line.val ≤ flagSubspace .plane plane) :
    edgeSymbolMap base (incidenceChain line.val plane incidence) =
      symbol base line
        ⟨selectedGoodLine plane (good_plane_of_containing_good_line line.val plane line.property incidence),
          selectedGoodLine_good plane
            (good_plane_of_containing_good_line line.val plane line.property incidence)⟩ := by
  classical
  have planeGood := good_plane_of_containing_good_line line.val plane line.property incidence
  have edgeGood : incidenceEdge line.val plane incidence ∈ goodEdges := by
    change GoodFlag .plane (endpoint .plane _) ∧ GoodFlag .line (endpoint .line _)
    rw [incidenceEdge_plane, incidenceEdge_line]
    exact ⟨planeGood, line.property⟩
  simp only [edgeSymbolMap, incidenceChain, Finsupp.linearCombination_single, one_smul,
    edgeSymbol, dite_eq_left edgeGood, incidenceEdge_line, incidenceEdge_plane]

theorem edgeSymbolMap_lineConnector (base first second : GoodLines) :
    edgeSymbolMap base (lineConnector first.val second.val first.property) =
      symbol base first second := by
  classical
  by_cases distinct : first.val ≠ second.val
  · let plane := pairPlane first.val second.val distinct first.property
    have firstIncidence := pairPlane_first first.val second.val distinct first.property
    have secondIncidence := pairPlane_second first.val second.val distinct first.property
    have planeGood := good_plane_of_containing_good_line first.val plane first.property firstIncidence
    let selected : GoodLines :=
      ⟨selectedGoodLine plane planeGood, selectedGoodLine_good plane planeGood⟩
    rw [lineConnector_of_common_plane first.val second.val plane first.property distinct
      firstIncidence secondIncidence, map_sub, edgeSymbolMap_incidenceChain,
      edgeSymbolMap_incidenceChain]
    exact (symbol_base_coplanar base first second selected plane firstIncidence secondIncidence
      (selectedGoodLine_incidence plane planeGood)).symm
  · have equality : first = second := Subtype.ext (not_not.mp distinct)
    subst second
    rw [lineConnector_self, map_zero]
    have swap := symbol_swap first first base
    have twice : (2 : ℂ) • symbol first first base = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr swap
    have zero := (smul_eq_zero.mp twice).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
    rw [symbol_cycle base first first, zero]

theorem edgeSymbolMap_triangle (base first second third : GoodLines) :
    edgeSymbolMap base
      (lineTriangle first.val second.val third.val first.property second.property third.property) =
        symbol first second third := by
  rw [lineTriangle, map_add, map_add, edgeSymbolMap_lineConnector,
    edgeSymbolMap_lineConnector, edgeSymbolMap_lineConnector]
  exact (symbol_base_triangle base first second third).symm

theorem edgeSymbolMap_trianglePresentation (base : GoodLines) (combination : TripleChains) :
    edgeSymbolMap base (trianglePresentation combination).val =
      rationalRelations.mkQ combination := by
  have equality : (edgeSymbolMap base).comp (goodCycles.subtype.comp trianglePresentation) =
      rationalRelations.mkQ := by
    apply Finsupp.lhom_ext
    intro vertices coefficient
    rw [show Finsupp.single vertices coefficient =
      coefficient • Finsupp.single vertices 1 by simp]
    simp only [LinearMap.comp_apply, map_smul]
    apply congrArg (fun value => coefficient • value)
    simpa only [trianglePresentation, Finsupp.linearCombination_single, one_smul,
      tripleApartment, Submodule.subtype_apply, symbol, triple] using
        edgeSymbolMap_triangle base vertices.1 vertices.2.1 vertices.2.2
  exact LinearMap.congr_fun equality combination

theorem trianglePresentation_kernel : trianglePresentation.ker = rationalRelations := by
  apply le_antisymm
  · intro combination membership
    let frame : NormalizedFrames := TernaryPeriodPolynomials.GoodApartmentFunctional.FrameOrbit.referenceFrame
    let base : GoodLines :=
      ⟨columnLine (GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val) 0,
        by
          simp only [columnLine, Fin.val_zero, pow_zero, mul_one]
          exact goodFlag_column frame.val .line 0 rfl
            (by rw [frame.property 0]; exact one_ne_zero)⟩
    apply (Submodule.Quotient.mk_eq_zero rationalRelations).mp
    change rationalRelations.mkQ combination = 0
    rw [← edgeSymbolMap_trianglePresentation base combination,
      LinearMap.mem_ker.mp membership, ZeroMemClass.coe_zero, map_zero]
  · exact rationalRelations_in_kernel

def rationalFrameTriple (frame : GoodRationalFrames) : Triples :=
  (⟨columnLine frame.val 0, frame.property 0⟩,
    ⟨columnLine frame.val 1, frame.property 1⟩,
    ⟨columnLine frame.val 2, frame.property 2⟩)

def rationalFramesToTriples : (GoodRationalFrames →₀ ℂ) →ₗ[ℂ] TripleChains :=
  Finsupp.linearCombination ℂ (fun frame => Finsupp.single (rationalFrameTriple frame) 1)

theorem trianglePresentation_rationalFramesToTriples (combination : GoodRationalFrames →₀ ℂ) :
    trianglePresentation (rationalFramesToTriples combination) =
      rationalApartmentPresentation combination := by
  have equality : trianglePresentation.comp rationalFramesToTriples =
      rationalApartmentPresentation := by
    apply Finsupp.lhom_ext
    intro frame coefficient
    rw [show Finsupp.single frame coefficient =
      coefficient • Finsupp.single frame 1 by simp]
    simp only [LinearMap.comp_apply, map_smul]
    congr 1
    apply Subtype.ext
    simp only [rationalFramesToTriples, trianglePresentation,
      Finsupp.linearCombination_single, one_smul,
      tripleApartment, rationalFrameTriple, rationalApartmentPresentation,
      rationalApartment]
    exact (apartment_as_lineConnectors frame.val frame.property).symm
  exact LinearMap.congr_fun equality combination

theorem trianglePresentation_surjective : Function.Surjective trianglePresentation := by
  intro chain
  obtain ⟨combination, rfl⟩ := rationalApartmentPresentation_surjective chain
  exact ⟨rationalFramesToTriples combination,
    trianglePresentation_rationalFramesToTriples combination⟩

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.RationalRelations
