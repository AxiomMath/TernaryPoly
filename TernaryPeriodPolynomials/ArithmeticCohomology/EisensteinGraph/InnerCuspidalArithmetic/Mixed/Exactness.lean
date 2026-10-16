module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Inflation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

theorem mixedCrossedMap_one (cycle : radicalZeroTwoCycles action representation) :
    mixedCrossedMap action representation 1 cycle = 0 := by
  apply Subtype.ext
  funext radical
  change cycle.val.val (SemidirectProduct.inr 1)
      (SemidirectProduct.inl (action 1⁻¹ radical)) -
    cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr 1) = 0
  simp only [inv_one, map_one, MulAut.one_apply]
  rw [radicalZeroTwoCycle_one_left, radicalZeroTwoCycle_one_right, sub_self]

def radicalCrossedExtension
    (cochain : crossedCocycles (representation.comp SemidirectProduct.inl)) :
    SemidirectProduct Radical Levi action → Value := fun element => cochain.val element.left

theorem radicalCrossedExtension_boundary_zero
    (cochain : crossedCocycles (representation.comp SemidirectProduct.inl)) :
    inhomogeneousBoundaryMap representation (radicalCrossedExtension action representation cochain) ∈
      radicalZeroTwoCycles action representation := by
  apply (inhomogeneousBoundary_radical_zero_iff action representation _).mpr
  exact cochain.property

def radicalCrossedExtensionBoundary
    (cochain : crossedCocycles (representation.comp SemidirectProduct.inl)) :
    radicalZeroTwoCycles action representation :=
  ⟨inhomogeneousBoundaryMap representation (radicalCrossedExtension action representation cochain),
    radicalCrossedExtension_boundary_zero action representation cochain⟩

theorem radicalCrossedExtensionBoundary_mixed
    (cochain : crossedCocycles (representation.comp SemidirectProduct.inl)) (element : Levi) :
    mixedCrossedMap action representation element
        (radicalCrossedExtensionBoundary action representation cochain) =
      leviCrossedAction action representation element cochain - cochain := by
  unfold radicalCrossedExtensionBoundary
  rw [mixedCrossedMap_boundary]
  have restriction : radicalRestrictionOfBoundary action representation
      (radicalCrossedExtension action representation cochain)
      (radicalCrossedExtension_boundary_zero action representation cochain) = cochain := by
    apply Subtype.ext
    rfl
  rw [restriction]
  have oneZero : cochain.val 1 = 0 := by
    have identity := cochain.property 1 1
    change cochain.val (1 * 1) = cochain.val 1 +
      representation (SemidirectProduct.inl 1) (cochain.val 1) at identity
    simp only [one_mul, map_one, Module.End.one_apply] at identity
    exact (add_left_cancel (identity.symm.trans (add_zero (cochain.val 1)).symm))
  change _ - crossedBoundary (representation.comp SemidirectProduct.inl) (cochain.val 1) = _
  rw [oneZero, map_zero, sub_zero]

def leviValueExtension (values : Levi → Value) :
    SemidirectProduct Radical Levi action → Value := fun element => values element.right

theorem leviValueExtension_boundary_zero (values : Levi → Value) (oneZero : values 1 = 0) :
    inhomogeneousBoundaryMap representation (leviValueExtension action values) ∈
      radicalZeroTwoCycles action representation := by
  intro first second
  change representation (SemidirectProduct.inl first) (values 1) -
      values (SemidirectProduct.inl first * SemidirectProduct.inl second).right + values 1 = 0
  rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inl,
    one_mul, oneZero, map_zero]
  abel

def leviValueExtensionBoundary (values : Levi → Value) (oneZero : values 1 = 0) :
    radicalZeroTwoCycles action representation :=
  ⟨inhomogeneousBoundaryMap representation (leviValueExtension action values),
    leviValueExtension_boundary_zero action representation values oneZero⟩

theorem leviValueExtensionBoundary_mixed (values : Levi → Value) (oneZero : values 1 = 0)
    (element : Levi) :
    mixedCrossedMap action representation element
        (leviValueExtensionBoundary action representation values oneZero) =
      -crossedBoundary (representation.comp SemidirectProduct.inl) (values element) := by
  unfold leviValueExtensionBoundary
  rw [mixedCrossedMap_boundary]
  have restriction : radicalRestrictionOfBoundary action representation
      (leviValueExtension action values)
      (leviValueExtension_boundary_zero action representation values oneZero) = 0 := by
    apply Subtype.ext
    funext radical
    exact oneZero
  rw [restriction, map_zero, sub_self, zero_sub]
  rfl

theorem mixedClassMap_zero_iff_pointwise_boundaries
    (cycle : radicalZeroTwoCycles action representation) :
    mixedClassMap action representation cycle = 0 ↔
      ∃ cochain : crossedCocycles (representation.comp SemidirectProduct.inl),
        ∀ element : Levi,
          mixedCrossedMap action representation element cycle -
              (leviCrossedAction action representation element cochain - cochain) ∈
            crossedBoundaries (representation.comp SemidirectProduct.inl) := by
  constructor
  · intro zero
    obtain ⟨primitive, equality⟩ :=
      (Submodule.Quotient.mk_eq_zero
        (crossedBoundaries (leviCrossedH1Representation action representation))).mp zero
    obtain ⟨cochain, cochainClass⟩ :=
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ_surjective primitive
    refine ⟨cochain, ?_⟩
    intro element
    have pointwise := congrArg
      (fun cochain : crossedCocycles (leviCrossedH1Representation action representation) =>
        cochain.val element) equality
    change leviCrossedH1Representation action representation element primitive - primitive =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation element cycle) at pointwise
    rw [← cochainClass, leviCrossedH1Representation_mk] at pointwise
    apply (Submodule.Quotient.mk_eq_zero
      (crossedBoundaries (representation.comp SemidirectProduct.inl))).mp
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation element cycle -
        (leviCrossedAction action representation element cochain - cochain)) = 0
    rw [map_sub, map_sub, ← pointwise, sub_self]
  · rintro ⟨cochain, pointwise⟩
    apply (Submodule.Quotient.mk_eq_zero
      (crossedBoundaries (leviCrossedH1Representation action representation))).mpr
    refine ⟨(crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ cochain, ?_⟩
    apply Subtype.ext
    funext element
    have equality := (Submodule.Quotient.mk_eq_zero
      (crossedBoundaries (representation.comp SemidirectProduct.inl))).mpr (pointwise element)
    change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation element cycle -
        (leviCrossedAction action representation element cochain - cochain)) = 0 at equality
    rw [map_sub, map_sub] at equality
    change leviCrossedH1Representation action representation element
          ((crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ cochain) -
        (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ cochain =
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (mixedCrossedMap action representation element cycle)
    rw [leviCrossedH1Representation_mk]
    exact (sub_eq_zero.mp equality).symm

theorem exists_mixedZero_cycle_of_mixedClass_zero
    (cycle : radicalZeroTwoCycles action representation)
    (zero : mixedClassMap action representation cycle = 0) :
    ∃ corrected : radicalZeroTwoCycles action representation,
      (∀ element, mixedCrossedMap action representation element corrected = 0) ∧
      (inhomogeneousBoundaries representation).mkQ corrected.val =
        (inhomogeneousBoundaries representation).mkQ cycle.val := by
  classical
  obtain ⟨cochain, pointwise⟩ :=
    (mixedClassMap_zero_iff_pointwise_boundaries action representation cycle).mp zero
  let firstCorrection := cycle - radicalCrossedExtensionBoundary action representation cochain
  have firstMixed : ∀ element, mixedCrossedMap action representation element firstCorrection ∈
      crossedBoundaries (representation.comp SemidirectProduct.inl) := by
    intro element
    change mixedCrossedMap action representation element
      (cycle - radicalCrossedExtensionBoundary action representation cochain) ∈ _
    rw [map_sub, radicalCrossedExtensionBoundary_mixed]
    exact pointwise element
  have existsValue : ∀ element : Levi, ∃ value : Value,
      crossedBoundary (representation.comp SemidirectProduct.inl) value =
        mixedCrossedMap action representation element firstCorrection := firstMixed
  choose values values_eq using existsValue
  let normalizedValues : Levi → Value := fun element => if element = 1 then 0 else values element
  have normalizedOne : normalizedValues 1 = 0 := by simp [normalizedValues]
  have normalizedEquality : ∀ element,
      crossedBoundary (representation.comp SemidirectProduct.inl) (normalizedValues element) =
        mixedCrossedMap action representation element firstCorrection := by
    intro element
    by_cases identity : element = 1
    · subst element
      rw [normalizedOne, map_zero, mixedCrossedMap_one]
    · simpa only [normalizedValues, ite_eq_right identity] using values_eq element
  let corrected := firstCorrection +
    leviValueExtensionBoundary action representation normalizedValues normalizedOne
  refine ⟨corrected, ?_, ?_⟩
  · intro element
    change mixedCrossedMap action representation element
      (firstCorrection + leviValueExtensionBoundary action representation normalizedValues normalizedOne) = 0
    rw [map_add, leviValueExtensionBoundary_mixed, normalizedEquality, add_neg_cancel]
  · change (inhomogeneousBoundaries representation).mkQ
      ((cycle.val - inhomogeneousBoundaryMap representation
        (radicalCrossedExtension action representation cochain)) +
        inhomogeneousBoundaryMap representation (leviValueExtension action normalizedValues)) = _
    rw [map_add, map_sub]
    have firstZero : (inhomogeneousBoundaries representation).mkQ
        (inhomogeneousBoundaryMap representation (radicalCrossedExtension action representation cochain)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    have secondZero : (inhomogeneousBoundaries representation).mkQ
        (inhomogeneousBoundaryMap representation (leviValueExtension action normalizedValues)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
    rw [firstZero, secondZero, sub_zero, add_zero]

theorem mixedClass_zero_mem_inflation (cycle : radicalZeroTwoCycles action representation)
    (zero : mixedClassMap action representation cycle = 0) :
    (inhomogeneousBoundaries representation).mkQ cycle.val ∈
      (semidirectInflationH2 action representation).range := by
  obtain ⟨corrected, mixedZero, sameClass⟩ :=
    exists_mixedZero_cycle_of_mixedClass_zero action representation cycle zero
  let normalized := mixedNormalizedCycle action representation corrected
  have normalizedMixed : ∀ element,
      mixedCrossedMap action representation element normalized = 0 := by
    intro element
    rw [mixedNormalizedCycle_mixed]
    exact mixedZero element
  let leviCycle := mixedZeroLeviCycle action representation normalized
    (mixedNormalizedCycle_radical_levi action representation corrected) normalizedMixed
  refine ⟨(inhomogeneousBoundaries
    (semidirectInvariantRepresentation action representation)).mkQ leviCycle, ?_⟩
  change (inhomogeneousBoundaries representation).mkQ
    (semidirectInflationCycles action representation leviCycle) = _
  rw [← mixedZeroCycle_eq_inflation]
  exact (mixedNormalizedCycle_sameClass action representation corrected).trans sameClass

theorem radicalKernelMixedMap_zero_mem_inflation
    (coordinate : (radicalRestrictionH2 action representation).ker)
    (zero : radicalKernelMixedMap action representation coordinate = 0) :
    coordinate.val ∈ (semidirectInflationH2 action representation).range := by
  let representative := (radicalRestrictionKernelEquiv action representation).symm coordinate
  obtain ⟨cycle, cycleClass⟩ := (radicalZeroBoundaries action representation).mkQ_surjective representative
  have fullClass : (inhomogeneousBoundaries representation).mkQ cycle.val = coordinate.val := by
    have equality := congrArg Subtype.val
      ((radicalRestrictionKernelEquiv action representation).apply_symm_apply coordinate)
    change radicalZeroH2ToFull action representation representative = coordinate.val at equality
    rw [← cycleClass] at equality
    exact equality
  have mixedZero : mixedClassMap action representation cycle = 0 := by
    change mixedH2Descent action representation representative = 0 at zero
    rw [← cycleClass, mixedH2Descent_mk] at zero
    exact zero
  rw [← fullClass]
  exact mixedClass_zero_mem_inflation action representation cycle mixedZero

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
