module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.RationalApartments

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
open TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.ApartmentGeneration

noncomputable section

def GoodRationalFrames :=
  {frame : RationalGL3 // ∀ column, GoodFlag .line (columnLine frame column)}

def rationalApartment (frame : GoodRationalFrames) : goodCycles :=
  ⟨apartment frame.val, (mem_goodCycles _).mpr ⟨chainBoundary_apartment _, by
    rw [← mem_goodChains, apartment_as_lineConnectors frame.val frame.property]
    exact goodChains.add_mem
      (goodChains.add_mem
        (lineConnector_good _ _ (frame.property 0) (frame.property 1))
        (lineConnector_good _ _ (frame.property 1) (frame.property 2)))
      (lineConnector_good _ _ (frame.property 2) (frame.property 0))⟩⟩

def rationalApartmentPresentation : (GoodRationalFrames →₀ ℂ) →ₗ[ℂ] goodCycles :=
  Finsupp.linearCombination ℂ rationalApartment

theorem rationalApartmentSpan_eq_goodCycles : rationalApartmentSpan = goodCycles := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro chain ⟨frame, good, rfl⟩
    exact (rationalApartment ⟨frame, good⟩).property
  · intro chain membership
    exact goodCycle_mem_rationalApartmentSpan chain ((mem_goodCycles chain).mp membership)

theorem rationalApartmentPresentation_surjective :
    Function.Surjective rationalApartmentPresentation := by
  intro chain
  have membership : chain.val ∈
      Submodule.span ℂ (Set.range (fun frame : GoodRationalFrames => apartment frame.val)) := by
    have generators :
        {value | ∃ frame : RationalGL3,
          (∀ column, GoodFlag .line (columnLine frame column)) ∧ value = apartment frame} =
        Set.range (fun frame : GoodRationalFrames => apartment frame.val) := by
      ext value
      constructor
      · rintro ⟨frame, good, rfl⟩
        exact ⟨⟨frame, good⟩, rfl⟩
      · rintro ⟨frame, rfl⟩
        exact ⟨frame.val, frame.property, rfl⟩
    rw [← generators]
    exact goodCycle_mem_rationalApartmentSpan chain.val ((mem_goodCycles _).mp chain.property)
  rw [← Finsupp.range_linearCombination] at membership
  obtain ⟨combination, equality⟩ := membership
  refine ⟨combination, ?_⟩
  apply Subtype.ext
  change goodCycles.subtype (rationalApartmentPresentation combination) = chain.val
  rw [rationalApartmentPresentation, ← LinearMap.comp_apply,
    ← Finsupp.linearCombination_linear_comp]
  exact equality

def lineTriangle (first second third : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second)
    (thirdGood : GoodFlag .line third) : EdgeChains :=
  lineConnector first second firstGood + lineConnector second third secondGood +
    lineConnector third first thirdGood

theorem lineTriangle_goodCycle (first second third : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second)
    (thirdGood : GoodFlag .line third) : GoodCycle
      (lineTriangle first second third firstGood secondGood thirdGood) := by
  constructor
  · simp only [lineTriangle, map_add, lineConnector_boundary]
    abel
  · rw [← mem_goodChains]
    exact goodChains.add_mem
      (goodChains.add_mem (lineConnector_good _ _ firstGood secondGood)
        (lineConnector_good _ _ secondGood thirdGood))
      (lineConnector_good _ _ thirdGood firstGood)

theorem lineTriangle_coplanar (first second third : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second)
    (thirdGood : GoodFlag .line third) (plane : Flags .plane)
    (firstIncidence : flagSubspace .line first ≤ flagSubspace .plane plane)
    (secondIncidence : flagSubspace .line second ≤ flagSubspace .plane plane)
    (thirdIncidence : flagSubspace .line third ≤ flagSubspace .plane plane) :
    lineTriangle first second third firstGood secondGood thirdGood = 0 := by
  rw [lineTriangle,
    lineConnector_on_edge_plane first second plane firstGood firstIncidence secondIncidence,
    lineConnector_on_edge_plane second third plane secondGood secondIncidence thirdIncidence,
    lineConnector_on_edge_plane third first plane thirdGood thirdIncidence firstIncidence]
  abel

theorem lineTriangle_subdivision (first second third inserted : Flags .line)
    (firstGood : GoodFlag .line first) (secondGood : GoodFlag .line second)
    (thirdGood : GoodFlag .line third) (insertedGood : GoodFlag .line inserted) :
    lineTriangle first second third firstGood secondGood thirdGood =
      lineTriangle inserted second third insertedGood secondGood thirdGood +
      lineTriangle first inserted third firstGood insertedGood thirdGood +
      lineTriangle first second inserted firstGood secondGood insertedGood := by
  simp only [lineTriangle,
    lineConnector_reverse inserted second insertedGood secondGood,
    lineConnector_reverse inserted third insertedGood thirdGood,
    lineConnector_reverse inserted first insertedGood firstGood]
  abel

theorem apartment_subdivision (frame : GoodRationalFrames) (inserted : Flags .line)
    (insertedGood : GoodFlag .line inserted) :
    apartment frame.val =
      lineTriangle inserted (columnLine frame.val 1) (columnLine frame.val 2)
        insertedGood (frame.property 1) (frame.property 2) +
      lineTriangle (columnLine frame.val 0) inserted (columnLine frame.val 2)
        (frame.property 0) insertedGood (frame.property 2) +
      lineTriangle (columnLine frame.val 0) (columnLine frame.val 1) inserted
        (frame.property 0) (frame.property 1) insertedGood := by
  rw [apartment_as_lineConnectors frame.val frame.property]
  exact lineTriangle_subdivision _ _ _ _ _ _ _ _

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.ApartmentGeneration
