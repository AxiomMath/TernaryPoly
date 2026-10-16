module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Exactness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

section Normalization

variable {GroupType Value : Type} [Group GroupType]
  [AddCommGroup Value] [Module ℂ Value]
  (representation : Representation ℂ GroupType Value)

theorem inhomogeneousTwoCycle_one_left (cycle : inhomogeneousTwoCycles representation)
    (element : GroupType) : cycle.val 1 element = cycle.val 1 1 := by
  have identity := cycle.property 1 1 element
  simp only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add] at identity
  exact sub_eq_zero.mp identity

theorem inhomogeneousTwoCycle_one_right (cycle : inhomogeneousTwoCycles representation)
    (element : GroupType) : cycle.val element 1 = representation element (cycle.val 1 1) := by
  have identity := cycle.property element 1 1
  simp only [mul_one] at identity
  apply sub_eq_zero.mp
  convert congrArg Neg.neg identity using 1 <;> abel

def normalizedInhomogeneousCycle (cycle : inhomogeneousTwoCycles representation) :
    inhomogeneousTwoCycles representation :=
  cycle - inhomogeneousBoundaryMap representation (fun _ => cycle.val 1 1)

theorem normalizedInhomogeneousCycle_one_left
    (cycle : inhomogeneousTwoCycles representation) (element : GroupType) :
    (normalizedInhomogeneousCycle representation cycle).val 1 element = 0 := by
  change cycle.val 1 element -
    (representation 1 (cycle.val 1 1) - cycle.val 1 1 + cycle.val 1 1) = 0
  rw [map_one, Module.End.one_apply, inhomogeneousTwoCycle_one_left]
  abel

theorem normalizedInhomogeneousCycle_one_right
    (cycle : inhomogeneousTwoCycles representation) (element : GroupType) :
    (normalizedInhomogeneousCycle representation cycle).val element 1 = 0 := by
  change cycle.val element 1 -
    (representation element (cycle.val 1 1) - cycle.val 1 1 + cycle.val 1 1) = 0
  rw [inhomogeneousTwoCycle_one_right]
  abel

theorem normalizedInhomogeneousCycle_sameClass
    (cycle : inhomogeneousTwoCycles representation) :
    (inhomogeneousBoundaries representation).mkQ
        (normalizedInhomogeneousCycle representation cycle) =
      (inhomogeneousBoundaries representation).mkQ cycle := by
  change (inhomogeneousBoundaries representation).mkQ
    (cycle - inhomogeneousBoundaryMap representation (fun _ => cycle.val 1 1)) = _
  rw [map_sub]
  have boundaryZero : (inhomogeneousBoundaries representation).mkQ
      (inhomogeneousBoundaryMap representation (fun _ => cycle.val 1 1)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [boundaryZero, sub_zero]

end Normalization

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

def normalizedInflationCycle
    (cycle : inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation)) :
    radicalZeroTwoCycles action representation :=
  ⟨semidirectInflationCycles action representation
    (normalizedInhomogeneousCycle (semidirectInvariantRepresentation action representation) cycle), by
    intro first second
    change ((normalizedInhomogeneousCycle
      (semidirectInvariantRepresentation action representation) cycle).val 1 1).val = 0
    rw [normalizedInhomogeneousCycle_one_left]
    rfl⟩

theorem normalizedInflationCycle_sameClass
    (cycle : inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation)) :
    (inhomogeneousBoundaries representation).mkQ
        (normalizedInflationCycle action representation cycle).val =
      semidirectInflationH2 action representation
        ((inhomogeneousBoundaries
          (semidirectInvariantRepresentation action representation)).mkQ cycle) := by
  change semidirectInflationH2 action representation
    ((inhomogeneousBoundaries (semidirectInvariantRepresentation action representation)).mkQ
      (normalizedInhomogeneousCycle (semidirectInvariantRepresentation action representation)
        cycle)) = _
  rw [normalizedInhomogeneousCycle_sameClass]

theorem normalizedInflationCycle_mixed
    (cycle : inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation))
    (element : Levi) :
    mixedCrossedMap action representation element
      (normalizedInflationCycle action representation cycle) = 0 := by
  apply Subtype.ext
  funext radical
  change ((normalizedInhomogeneousCycle
      (semidirectInvariantRepresentation action representation) cycle).val element 1).val -
    ((normalizedInhomogeneousCycle
      (semidirectInvariantRepresentation action representation) cycle).val 1 element).val = 0
  rw [normalizedInhomogeneousCycle_one_right, normalizedInhomogeneousCycle_one_left]
  exact sub_self _

theorem normalizedInflationCycle_mixedClass
    (cycle : inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation)) :
    mixedClassMap action representation (normalizedInflationCycle action representation cycle) = 0 := by
  have mixedZero : mixedH1CocycleMap action representation
      (normalizedInflationCycle action representation cycle) = 0 := by
    apply Subtype.ext
    funext element
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation element
        (normalizedInflationCycle action representation cycle)) = 0
    rw [normalizedInflationCycle_mixed, map_zero]
  change (crossedBoundaries (leviCrossedH1Representation action representation)).mkQ
    (mixedH1CocycleMap action representation (normalizedInflationCycle action representation cycle)) = 0
  rw [mixedZero, map_zero]

theorem semidirectInflationH2_mem_radical_kernel
    (coordinate : InhomogeneousH2 (semidirectInvariantRepresentation action representation)) :
    semidirectInflationH2 action representation coordinate ∈
      (radicalRestrictionH2 action representation).ker := by
  obtain ⟨cycle, rfl⟩ :=
    (inhomogeneousBoundaries (semidirectInvariantRepresentation action representation)).mkQ_surjective
      coordinate
  rw [← normalizedInflationCycle_sameClass]
  exact radicalZeroH2ToFull_mem_ker action representation
    ((radicalZeroBoundaries action representation).mkQ
      (normalizedInflationCycle action representation cycle))

def semidirectInflationToRadicalKernel :
    InhomogeneousH2 (semidirectInvariantRepresentation action representation) →ₗ[ℂ]
      (radicalRestrictionH2 action representation).ker :=
  (semidirectInflationH2 action representation).codRestrict _
    (semidirectInflationH2_mem_radical_kernel action representation)

theorem semidirectInflationToRadicalKernel_mixed
    (coordinate : InhomogeneousH2 (semidirectInvariantRepresentation action representation)) :
    radicalKernelMixedMap action representation
      (semidirectInflationToRadicalKernel action representation coordinate) = 0 := by
  obtain ⟨cycle, rfl⟩ :=
    (inhomogeneousBoundaries (semidirectInvariantRepresentation action representation)).mkQ_surjective
      coordinate
  have representative : semidirectInflationToRadicalKernel action representation
      ((inhomogeneousBoundaries (semidirectInvariantRepresentation action representation)).mkQ cycle) =
    radicalZeroH2ToKernel action representation
      ((radicalZeroBoundaries action representation).mkQ
        (normalizedInflationCycle action representation cycle)) := by
    apply Subtype.ext
    exact (normalizedInflationCycle_sameClass action representation cycle).symm
  rw [representative, radicalKernelMixedMap_representative]
  exact normalizedInflationCycle_mixedClass action representation cycle

theorem radicalKernelMixedMap_zero_iff_mem_inflation
    (coordinate : (radicalRestrictionH2 action representation).ker) :
    radicalKernelMixedMap action representation coordinate = 0 ↔
      coordinate.val ∈ (semidirectInflationH2 action representation).range := by
  constructor
  · exact radicalKernelMixedMap_zero_mem_inflation action representation coordinate
  · rintro ⟨leviCoordinate, equality⟩
    have sameCoordinate : coordinate =
        semidirectInflationToRadicalKernel action representation leviCoordinate :=
      Subtype.ext equality.symm
    rw [sameCoordinate]
    exact semidirectInflationToRadicalKernel_mixed action representation leviCoordinate

theorem semidirectInflationToRadicalKernel_range :
    (semidirectInflationToRadicalKernel action representation).range =
      (radicalKernelMixedMap action representation).ker := by
  apply le_antisymm
  · rintro coordinate ⟨leviCoordinate, rfl⟩
    exact semidirectInflationToRadicalKernel_mixed action representation leviCoordinate
  · intro coordinate zero
    obtain ⟨leviCoordinate, equality⟩ :=
      (radicalKernelMixedMap_zero_iff_mem_inflation action representation coordinate).mp zero
    exact ⟨leviCoordinate, Subtype.ext equality⟩

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
