module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rational.Discreteness

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CountableSlices

variable {ActingGroup Space : Type*} [Group ActingGroup] [MulAction ActingGroup Space]

def piece (slices : ℕ → Set Space) (index : ℕ) : Set Space :=
  slices index \ ⋃ (earlier : ℕ) (_ : earlier < index) (element : ActingGroup),
    (fun point => element • point) ⁻¹' slices earlier

def domain (slices : ℕ → Set Space) : Set Space := ⋃ index, piece (ActingGroup := ActingGroup) slices index

theorem mem_piece (slices : ℕ → Set Space) (index : ℕ) (point : Space) :
    point ∈ piece (ActingGroup := ActingGroup) slices index ↔ point ∈ slices index ∧
      ∀ earlier, earlier < index → ∀ element : ActingGroup, element • point ∉ slices earlier := by
  simp only [piece, Set.mem_sdiff, Set.mem_iUnion, Set.mem_preimage, not_exists]

theorem domain_measurable [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (slices : ℕ → Set Space) (measurable : ∀ index, MeasurableSet (slices index)) :
    MeasurableSet (domain (ActingGroup := ActingGroup) slices) := by
  apply MeasurableSet.iUnion
  intro index
  apply (measurable index).diff
  apply MeasurableSet.iUnion
  intro earlier
  apply MeasurableSet.iUnion
  intro _
  apply MeasurableSet.iUnion
  intro element
  exact (measurable earlier).preimage (measurable_const_smul element)

theorem exists_representative (slices : ℕ → Set Space) (cover : ∀ point, ∃ index, point ∈ slices index)
    (point : Space) : ∃ element : ActingGroup, element • point ∈ domain (ActingGroup := ActingGroup) slices := by
  classical
  have existsIndex : ∃ index, ∃ element : ActingGroup, element • point ∈ slices index := by
    obtain ⟨index, membership⟩ := cover point
    exact ⟨index, 1, by simpa only [one_smul] using membership⟩
  obtain ⟨element, membership⟩ := Nat.find_spec existsIndex
  refine ⟨element, Set.mem_iUnion.mpr ⟨Nat.find existsIndex, (mem_piece _ _ _).mpr ⟨membership, ?_⟩⟩⟩
  intro earlier less other earlierMembership
  exact Nat.find_min existsIndex less ⟨other * element, by simpa only [mul_smul] using earlierMembership⟩

theorem representative_unique (slices : ℕ → Set Space)
    (unique : ∀ index, ∀ point ∈ slices index, ∀ element : ActingGroup, element • point ∈ slices index → element = 1)
    (point : Space) (first second : ActingGroup)
    (firstMem : first • point ∈ domain (ActingGroup := ActingGroup) slices)
    (secondMem : second • point ∈ domain (ActingGroup := ActingGroup) slices) : first = second := by
  obtain ⟨firstIndex, firstMem⟩ := Set.mem_iUnion.mp firstMem
  obtain ⟨secondIndex, secondMem⟩ := Set.mem_iUnion.mp secondMem
  obtain ⟨firstIn, firstEarlier⟩ := (mem_piece _ _ _).mp firstMem
  obtain ⟨secondIn, secondEarlier⟩ := (mem_piece _ _ _).mp secondMem
  have sameIndex : firstIndex = secondIndex := by
    rcases lt_trichotomy firstIndex secondIndex with less | equal | greater
    · exact False.elim (secondEarlier firstIndex less (first * second⁻¹) (by
        simpa only [mul_smul, inv_smul_smul] using firstIn))
    · exact equal
    · exact False.elim (firstEarlier secondIndex greater (second * first⁻¹) (by
        simpa only [mul_smul, inv_smul_smul] using secondIn))
  subst secondIndex
  have identity := unique firstIndex (second • point) secondIn (first * second⁻¹) (by
    simpa only [mul_smul, inv_smul_smul] using firstIn)
  exact mul_inv_eq_one.mp identity

theorem isFundamentalDomain [MeasurableSpace Space] [Countable ActingGroup] [MeasurableConstSMul ActingGroup Space]
    (slices : ℕ → Set Space) (measurable : ∀ index, MeasurableSet (slices index))
    (cover : ∀ point, ∃ index, point ∈ slices index)
    (unique : ∀ index, ∀ point ∈ slices index, ∀ element : ActingGroup, element • point ∈ slices index → element = 1)
    (measure : Measure Space) : IsFundamentalDomain ActingGroup (domain (ActingGroup := ActingGroup) slices) measure := by
  apply IsFundamentalDomain.mk' (domain_measurable (ActingGroup := ActingGroup) slices measurable).nullMeasurableSet
  intro point
  obtain ⟨element, membership⟩ := exists_representative (ActingGroup := ActingGroup) slices cover point
  exact ⟨element, membership, fun other otherMembership =>
    representative_unique slices unique point other element otherMembership membership⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CountableSlices
