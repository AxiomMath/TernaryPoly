module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InhomogeneousResolution

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

theorem inhomogeneousBoundary_radical_zero_iff
    (cochain : SemidirectProduct Radical Levi action → Value) :
    inhomogeneousBoundaryMap representation cochain ∈
        radicalZeroTwoCycles action representation ↔
      (fun radical => cochain (SemidirectProduct.inl radical)) ∈
        crossedCocycles (representation.comp SemidirectProduct.inl) := by
  constructor
  · intro zero first second
    have identity := zero first second
    change representation (SemidirectProduct.inl first)
        (cochain (SemidirectProduct.inl second)) -
      cochain (SemidirectProduct.inl first * SemidirectProduct.inl second) +
      cochain (SemidirectProduct.inl first) = 0 at identity
    rw [← map_mul] at identity
    change cochain (SemidirectProduct.inl (first * second)) =
      cochain (SemidirectProduct.inl first) +
        representation (SemidirectProduct.inl first) (cochain (SemidirectProduct.inl second))
    apply sub_eq_zero.mp
    convert congrArg Neg.neg identity using 1 <;> abel
  · intro crossed first second
    have identity := crossed first second
    change cochain (SemidirectProduct.inl (first * second)) =
      cochain (SemidirectProduct.inl first) +
        representation (SemidirectProduct.inl first) (cochain (SemidirectProduct.inl second))
      at identity
    change representation (SemidirectProduct.inl first)
        (cochain (SemidirectProduct.inl second)) -
      cochain (SemidirectProduct.inl first * SemidirectProduct.inl second) +
      cochain (SemidirectProduct.inl first) = 0
    rw [← map_mul, identity]
    abel

def radicalRestrictionOfBoundary
    (cochain : SemidirectProduct Radical Levi action → Value)
    (zero : inhomogeneousBoundaryMap representation cochain ∈
      radicalZeroTwoCycles action representation) :
    crossedCocycles (representation.comp SemidirectProduct.inl) :=
  ⟨fun radical => cochain (SemidirectProduct.inl radical),
    (inhomogeneousBoundary_radical_zero_iff action representation cochain).mp zero⟩

theorem mixedCrossedMap_boundary
    (cochain : SemidirectProduct Radical Levi action → Value)
    (zero : inhomogeneousBoundaryMap representation cochain ∈
      radicalZeroTwoCycles action representation) (element : Levi) :
    mixedCrossedMap action representation element
        ⟨inhomogeneousBoundaryMap representation cochain, zero⟩ =
      leviCrossedAction action representation element
          (radicalRestrictionOfBoundary action representation cochain zero) -
        radicalRestrictionOfBoundary action representation cochain zero -
        crossedBoundary (representation.comp SemidirectProduct.inl)
          (cochain (SemidirectProduct.inr element)) := by
  apply Subtype.ext
  funext radical
  change (representation (SemidirectProduct.inr element)
          (cochain (SemidirectProduct.inl (action element⁻¹ radical))) -
        cochain (SemidirectProduct.inr element *
          SemidirectProduct.inl (action element⁻¹ radical)) +
        cochain (SemidirectProduct.inr element)) -
      (representation (SemidirectProduct.inl radical)
          (cochain (SemidirectProduct.inr element)) -
        cochain (SemidirectProduct.inl radical * SemidirectProduct.inr element) +
        cochain (SemidirectProduct.inl radical)) =
    representation (SemidirectProduct.inr element)
        (cochain (SemidirectProduct.inl (action element⁻¹ radical))) -
      cochain (SemidirectProduct.inl radical) -
      (representation (SemidirectProduct.inl radical)
        (cochain (SemidirectProduct.inr element)) - cochain (SemidirectProduct.inr element))
  rw [semidirect_conjugation_intertwines]
  abel

theorem mixedH1CocycleMap_boundary
    (cochain : SemidirectProduct Radical Levi action → Value)
    (zero : inhomogeneousBoundaryMap representation cochain ∈
      radicalZeroTwoCycles action representation) :
    mixedH1CocycleMap action representation
        ⟨inhomogeneousBoundaryMap representation cochain, zero⟩ =
      crossedBoundary (leviCrossedH1Representation action representation)
        ((crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (radicalRestrictionOfBoundary action representation cochain zero)) := by
  apply Subtype.ext
  funext element
  change (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
      (mixedCrossedMap action representation element
        ⟨inhomogeneousBoundaryMap representation cochain, zero⟩) =
    leviCrossedH1Representation action representation element
        ((crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
          (radicalRestrictionOfBoundary action representation cochain zero)) -
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (radicalRestrictionOfBoundary action representation cochain zero)
  rw [mixedCrossedMap_boundary, map_sub, map_sub, ← leviCrossedH1Representation_mk]
  have boundaryZero :
      (crossedBoundaries (representation.comp SemidirectProduct.inl)).mkQ
        (crossedBoundary (representation.comp SemidirectProduct.inl)
          (cochain (SemidirectProduct.inr element))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [boundaryZero, sub_zero]

def radicalZeroBoundaries :
    Submodule ℂ (radicalZeroTwoCycles action representation) :=
  (inhomogeneousBoundaries representation).comap
    (radicalZeroTwoCycles action representation).subtype

instance radicalZeroCyclesAddCommGroup :
    AddCommGroup (radicalZeroTwoCycles action representation) :=
  @Submodule.addCommGroup ℂ (inhomogeneousTwoCycles representation)
    inferInstance inferInstance inferInstance (radicalZeroTwoCycles action representation)

abbrev RadicalZeroH2 :=
  @HasQuotient.Quotient (radicalZeroTwoCycles action representation)
    (Submodule ℂ (radicalZeroTwoCycles action representation))
    (@Submodule.hasQuotient ℂ (radicalZeroTwoCycles action representation)
      inferInstance inferInstance inferInstance)
    (radicalZeroBoundaries action representation)

def mixedClassMap :
    radicalZeroTwoCycles action representation →ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation action representation) :=
  (crossedBoundaries (leviCrossedH1Representation action representation)).mkQ.comp
    (mixedH1CocycleMap action representation)

theorem radicalZeroBoundaries_le_mixedClassMap_ker :
    radicalZeroBoundaries action representation ≤ (mixedClassMap action representation).ker := by
  intro cycle membership
  obtain ⟨cochain, equality⟩ := membership
  have zero : inhomogeneousBoundaryMap representation cochain ∈
      radicalZeroTwoCycles action representation := equality.symm ▸ cycle.property
  have cycle_eq : cycle = ⟨inhomogeneousBoundaryMap representation cochain, zero⟩ :=
    Subtype.ext equality.symm
  change (crossedBoundaries (leviCrossedH1Representation action representation)).mkQ
    (mixedH1CocycleMap action representation cycle) = 0
  rw [cycle_eq, mixedH1CocycleMap_boundary]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

def mixedH2Descent :
    RadicalZeroH2 action representation →ₗ[ℂ]
      CrossedH1 (leviCrossedH1Representation action representation) :=
  @Submodule.liftQ ℂ (radicalZeroTwoCycles action representation)
    inferInstance inferInstance inferInstance (radicalZeroBoundaries action representation)
    ℂ (CrossedH1 (leviCrossedH1Representation action representation))
    inferInstance inferInstance inferInstance (RingHom.id ℂ)
    (mixedClassMap action representation)
    (radicalZeroBoundaries_le_mixedClassMap_ker action representation)

theorem mixedH2Descent_mk (cycle : radicalZeroTwoCycles action representation) :
    mixedH2Descent action representation
        ((radicalZeroBoundaries action representation).mkQ cycle) =
      (crossedBoundaries (leviCrossedH1Representation action representation)).mkQ
        (mixedH1CocycleMap action representation cycle) := by
  rfl

def radicalZeroH2ToFull :
    RadicalZeroH2 action representation →ₗ[ℂ] InhomogeneousH2 representation :=
  @Submodule.liftQ ℂ (radicalZeroTwoCycles action representation)
    inferInstance inferInstance inferInstance (radicalZeroBoundaries action representation)
    ℂ (InhomogeneousH2 representation) inferInstance inferInstance inferInstance (RingHom.id ℂ)
    ((inhomogeneousBoundaries representation).mkQ.comp
      (radicalZeroTwoCycles action representation).subtype) (by
    intro cycle membership
    exact (Submodule.Quotient.mk_eq_zero _).mpr membership)

theorem radicalZeroH2ToFull_injective :
    Function.Injective (radicalZeroH2ToFull action representation) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro coordinate membership
    obtain ⟨cycle, rfl⟩ := (radicalZeroBoundaries action representation).mkQ_surjective coordinate
    change (inhomogeneousBoundaries representation).mkQ cycle.val = 0 at membership
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((Submodule.Quotient.mk_eq_zero (inhomogeneousBoundaries representation)).mp membership)
  · exact bot_le

theorem mixedH2Descent_eq_of_same_full_class
    (first second : RadicalZeroH2 action representation)
    (equality : radicalZeroH2ToFull action representation first =
      radicalZeroH2ToFull action representation second) :
    mixedH2Descent action representation first = mixedH2Descent action representation second := by
  exact congrArg (mixedH2Descent action representation)
    (radicalZeroH2ToFull_injective action representation equality)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
