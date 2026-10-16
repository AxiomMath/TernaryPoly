module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CountableSlices

@[expose] public section


open scoped Pointwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.DiscreteSlices

variable {ActingGroup Ambient : Type*} [Group ActingGroup] [Group Ambient]

theorem exists_identity_slice [TopologicalSpace Ambient] [IsTopologicalGroup Ambient]
    (hom : ActingGroup →* Ambient) (neighborhood : Set Ambient)
    (openness : IsOpen neighborhood) (identityMem : (1 : Ambient) ∈ neighborhood)
    (isolated : ∀ element, hom element ∈ neighborhood → element = 1) :
    ∃ slice : Set Ambient, IsOpen slice ∧ (1 : Ambient) ∈ slice ∧
      ∀ point ∈ slice, ∀ element, hom element * point ∈ slice → element = 1 := by
  obtain ⟨smaller, smallerOpen, smallerOne, productSubset⟩ :=
    exists_open_nhds_one_mul_subset (openness.mem_nhds identityMem)
  refine ⟨smaller ∩ Inv.inv ⁻¹' smaller, smallerOpen.inter (smallerOpen.preimage continuous_inv),
    ⟨smallerOne, by simpa only [Set.mem_preimage, inv_one] using smallerOne⟩, ?_⟩
  intro point pointMem element elementMem
  apply isolated element
  apply productSubset
  exact Set.mem_mul.mpr ⟨hom element * point, elementMem.1, point⁻¹, pointMem.2, mul_inv_cancel_right _ _⟩

def translate (slice : Set Ambient) (center : Ambient) : Set Ambient :=
  {point | point * center⁻¹ ∈ slice}

theorem translate_open [TopologicalSpace Ambient] [IsTopologicalGroup Ambient]
    (slice : Set Ambient) (openness : IsOpen slice) (center : Ambient) :
    IsOpen (translate slice center) := openness.preimage (continuous_id.mul continuous_const)

theorem mem_translate_self (slice : Set Ambient) (identityMem : (1 : Ambient) ∈ slice) (point : Ambient) :
    point ∈ translate slice point := by
  change point * point⁻¹ ∈ slice
  rwa [mul_inv_cancel]

theorem translate_unique (hom : ActingGroup →* Ambient) (slice : Set Ambient)
    (unique : ∀ point ∈ slice, ∀ element, hom element * point ∈ slice → element = 1)
    (center point : Ambient) (pointMem : point ∈ translate slice center) (element : ActingGroup)
    (translatedMem : hom element * point ∈ translate slice center) : element = 1 := by
  apply unique (point * center⁻¹) pointMem element
  simpa only [translate, Set.mem_ofPred_eq, mul_assoc] using translatedMem

theorem exists_countable_slices [TopologicalSpace Ambient] [IsTopologicalGroup Ambient] [SecondCountableTopology Ambient]
    (hom : ActingGroup →* Ambient) (neighborhood : Set Ambient)
    (openness : IsOpen neighborhood) (identityMem : (1 : Ambient) ∈ neighborhood)
    (isolated : ∀ element, hom element ∈ neighborhood → element = 1) :
    ∃ slices : ℕ → Set Ambient, (∀ index, IsOpen (slices index)) ∧
      (∀ point, ∃ index, point ∈ slices index) ∧
      ∀ index, ∀ point ∈ slices index, ∀ element, hom element * point ∈ slices index → element = 1 := by
  obtain ⟨slice, sliceOpen, sliceOne, unique⟩ := exists_identity_slice hom neighborhood openness identityMem isolated
  obtain ⟨centers, countable, sameUnion⟩ := TopologicalSpace.isOpen_iUnion_countable
    (translate slice) (translate_open slice sliceOpen)
  have cover (point : Ambient) : ∃ center ∈ centers, point ∈ translate slice center := by
    have membership : point ∈ ⋃ center, translate slice center :=
      Set.mem_iUnion.mpr ⟨point, mem_translate_self slice sliceOne point⟩
    rw [← sameUnion] at membership
    simpa only [Set.mem_iUnion, exists_prop] using membership
  have nonempty : centers.Nonempty := by
    obtain ⟨center, membership, _⟩ := cover 1
    exact ⟨center, membership⟩
  obtain ⟨enumeration, rangeEquality⟩ := countable.exists_eq_range nonempty
  refine ⟨fun index => translate slice (enumeration index), fun index => translate_open slice sliceOpen _, ?_, ?_⟩
  · intro point
    obtain ⟨center, membership, pointMem⟩ := cover point
    rw [rangeEquality] at membership
    obtain ⟨index, rfl⟩ := membership
    exact ⟨index, pointMem⟩
  · intro index point pointMem element translatedMem
    exact translate_unique hom slice unique (enumeration index) point pointMem element translatedMem

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.DiscreteSlices
