module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Radical.Restriction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {Radical Levi Value : Type} [Group Radical] [Group Levi]
  [AddCommGroup Value] [Module ℂ Value]
  (action : Levi →* MulAut Radical)
  (representation : Representation ℂ (SemidirectProduct Radical Levi action) Value)

def semidirectRadicalInvariants : Submodule ℂ Value where
  carrier := {value | ∀ radical : Radical, representation (SemidirectProduct.inl radical) value = value}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstFixed secondFixed radical
    rw [map_add, firstFixed, secondFixed]
  smul_mem' := by
    intro scalar value fixed radical
    rw [map_smul, fixed]

theorem semidirectRadicalInvariants_levi_stable (element : Levi) (value : Value)
    (fixed : value ∈ semidirectRadicalInvariants action representation) :
    representation (SemidirectProduct.inr element) value ∈
      semidirectRadicalInvariants action representation := by
  intro radical
  rw [← Module.End.mul_apply, ← map_mul,
    ← semidirect_conjugation_intertwines action element radical,
    map_mul, Module.End.mul_apply, fixed]

def semidirectInvariantRepresentation :
    Representation ℂ Levi (semidirectRadicalInvariants action representation) :=
  Representation.subrepresentation (representation.comp SemidirectProduct.inr)
    (semidirectRadicalInvariants action representation)
    (fun element _ fixed => semidirectRadicalInvariants_levi_stable
      action representation element _ fixed)

theorem semidirect_representation_invariant
    (element : SemidirectProduct Radical Levi action)
    (value : semidirectRadicalInvariants action representation) :
    representation element value.val = representation (SemidirectProduct.inr element.right) value.val := by
  have factorization : element = SemidirectProduct.inl element.left *
      SemidirectProduct.inr element.right := by
    apply SemidirectProduct.ext <;> simp
  rw [factorization, map_mul, Module.End.mul_apply]
  simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
    SemidirectProduct.right_inr, one_mul]
  exact semidirectRadicalInvariants_levi_stable action representation element.right value.val
    value.property element.left

def semidirectInflationCycles :
    inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation) →ₗ[ℂ]
      inhomogeneousTwoCycles representation where
  toFun cycle := ⟨fun first second => (cycle.val first.right second.right).val, by
    intro first second third
    have identity := congrArg Subtype.val (cycle.property first.right second.right third.right)
    change representation (SemidirectProduct.inr first.right)
          (cycle.val second.right third.right).val -
        (cycle.val (first.right * second.right) third.right).val +
        (cycle.val first.right (second.right * third.right)).val -
        (cycle.val first.right second.right).val = 0 at identity
    rw [semidirect_representation_invariant action representation first]
    simpa only [SemidirectProduct.mul_right] using identity⟩
  map_add' first second := rfl
  map_smul' scalar cycle := rfl

theorem semidirectInflationCycles_boundary
    (cochain : Levi → semidirectRadicalInvariants action representation) :
    semidirectInflationCycles action representation
        (inhomogeneousBoundaryMap (semidirectInvariantRepresentation action representation) cochain) =
      inhomogeneousBoundaryMap representation (fun element => (cochain element.right).val) := by
  apply Subtype.ext
  funext first second
  change representation (SemidirectProduct.inr first.right) (cochain second.right).val -
        (cochain (first.right * second.right)).val + (cochain first.right).val =
      representation first (cochain second.right).val -
        (cochain (first * second).right).val + (cochain first.right).val
  rw [semidirect_representation_invariant action representation first,
    SemidirectProduct.mul_right]

def semidirectInflationH2 :
    InhomogeneousH2 (semidirectInvariantRepresentation action representation) →ₗ[ℂ]
      InhomogeneousH2 representation :=
  (inhomogeneousBoundaries (semidirectInvariantRepresentation action representation)).mapQ
    (inhomogeneousBoundaries representation) (semidirectInflationCycles action representation) (by
    rintro cycle ⟨cochain, rfl⟩
    exact ⟨fun element => (cochain element.right).val,
      (semidirectInflationCycles_boundary action representation cochain).symm⟩)

theorem radicalZeroTwoCycle_one_left (cycle : radicalZeroTwoCycles action representation)
    (element : SemidirectProduct Radical Levi action) : cycle.val.val 1 element = 0 := by
  have identity := cycle.val.property 1 1 element
  have zero : cycle.val.val 1 1 = 0 := by simpa only [map_one] using cycle.property 1 1
  simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add, zero, sub_zero]
    using identity

theorem radicalZeroTwoCycle_one_right (cycle : radicalZeroTwoCycles action representation)
    (element : SemidirectProduct Radical Levi action) : cycle.val.val element 1 = 0 := by
  have identity := cycle.val.property element 1 1
  have zero := radicalZeroTwoCycle_one_left action representation cycle 1
  have negZero : -cycle.val.val element 1 = 0 := by
    simp only [zero, map_zero, mul_one, zero_sub] at identity
    convert identity using 1
    abel
  exact neg_eq_zero.mp negZero

def mixedNormalizationPrimitive (cycle : radicalZeroTwoCycles action representation) :
    SemidirectProduct Radical Levi action → Value :=
  fun element => cycle.val.val (SemidirectProduct.inl element.left)
    (SemidirectProduct.inr element.right)

theorem mixedNormalizationPrimitive_inl (cycle : radicalZeroTwoCycles action representation)
    (radical : Radical) : mixedNormalizationPrimitive action representation cycle
      (SemidirectProduct.inl radical) = 0 := by
  change cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr 1) = 0
  rw [map_one, radicalZeroTwoCycle_one_right]

theorem mixedNormalizationPrimitive_inr (cycle : radicalZeroTwoCycles action representation)
    (element : Levi) : mixedNormalizationPrimitive action representation cycle
      (SemidirectProduct.inr element) = 0 := by
  change cycle.val.val (SemidirectProduct.inl 1) (SemidirectProduct.inr element) = 0
  rw [map_one, radicalZeroTwoCycle_one_left]

def mixedNormalizedCycle (cycle : radicalZeroTwoCycles action representation) :
    radicalZeroTwoCycles action representation :=
  ⟨cycle.val + inhomogeneousBoundaryMap representation
    (mixedNormalizationPrimitive action representation cycle), by
    intro first second
    change cycle.val.val (SemidirectProduct.inl first) (SemidirectProduct.inl second) +
      (representation (SemidirectProduct.inl first)
          (mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inl second)) -
        mixedNormalizationPrimitive action representation cycle
          (SemidirectProduct.inl first * SemidirectProduct.inl second) +
        mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inl first)) = 0
    rw [cycle.property, ← map_mul, mixedNormalizationPrimitive_inl,
      mixedNormalizationPrimitive_inl, mixedNormalizationPrimitive_inl, map_zero]
    abel⟩

theorem mixedNormalizedCycle_radical_levi (cycle : radicalZeroTwoCycles action representation)
    (radical : Radical) (element : Levi) :
    (mixedNormalizedCycle action representation cycle).val.val
      (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0 := by
  change cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) +
    (representation (SemidirectProduct.inl radical)
        (mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inr element)) -
      mixedNormalizationPrimitive action representation cycle
        (SemidirectProduct.inl radical * SemidirectProduct.inr element) +
      mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inl radical)) = 0
  rw [mixedNormalizationPrimitive_inr, mixedNormalizationPrimitive_inl, map_zero]
  simp only [mixedNormalizationPrimitive, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
    SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one,
    mul_one, one_mul]
  abel

theorem mixedNormalizedCycle_sameClass (cycle : radicalZeroTwoCycles action representation) :
    (inhomogeneousBoundaries representation).mkQ
        (mixedNormalizedCycle action representation cycle).val =
      (inhomogeneousBoundaries representation).mkQ cycle.val := by
  change (inhomogeneousBoundaries representation).mkQ
      (cycle.val + inhomogeneousBoundaryMap representation
        (mixedNormalizationPrimitive action representation cycle)) = _
  rw [map_add]
  have boundaryZero : (inhomogeneousBoundaries representation).mkQ
      (inhomogeneousBoundaryMap representation
        (mixedNormalizationPrimitive action representation cycle)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [boundaryZero, add_zero]

theorem mixedNormalizedCycle_mixed (cycle : radicalZeroTwoCycles action representation)
    (element : Levi) :
    mixedCrossedMap action representation element
        (mixedNormalizedCycle action representation cycle) =
      mixedCrossedMap action representation element cycle := by
  apply Subtype.ext
  funext radical
  change ((cycle.val.val (SemidirectProduct.inr element)
        (SemidirectProduct.inl (action element⁻¹ radical)) +
      (representation (SemidirectProduct.inr element)
          (mixedNormalizationPrimitive action representation cycle
            (SemidirectProduct.inl (action element⁻¹ radical))) -
        mixedNormalizationPrimitive action representation cycle
          (SemidirectProduct.inr element * SemidirectProduct.inl (action element⁻¹ radical)) +
        mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inr element))) -
    (cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) +
      (representation (SemidirectProduct.inl radical)
          (mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inr element)) -
        mixedNormalizationPrimitive action representation cycle
          (SemidirectProduct.inl radical * SemidirectProduct.inr element) +
        mixedNormalizationPrimitive action representation cycle (SemidirectProduct.inl radical)))) =
    cycle.val.val (SemidirectProduct.inr element)
        (SemidirectProduct.inl (action element⁻¹ radical)) -
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element)
  rw [semidirect_conjugation_intertwines, mixedNormalizationPrimitive_inl,
    mixedNormalizationPrimitive_inr, mixedNormalizationPrimitive_inl, map_zero, map_zero]
  abel

theorem semidirect_factorization (element : SemidirectProduct Radical Levi action) :
    element = SemidirectProduct.inl element.left * SemidirectProduct.inr element.right := by
  apply SemidirectProduct.ext <;> simp

theorem mixedZeroCycle_radical_first (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (radical : Radical) (element : SemidirectProduct Radical Levi action) :
    cycle.val.val (SemidirectProduct.inl radical) element = 0 := by
  have identity := cycle.val.property (SemidirectProduct.inl radical)
    (SemidirectProduct.inl element.left) (SemidirectProduct.inr element.right)
  rw [radicalLevi, map_zero, ← map_mul, radicalLevi, cycle.property] at identity
  simpa only [zero_sub, sub_zero, zero_add, ← semidirect_factorization] using identity

theorem mixedZeroCycle_levi_radical (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (element : Levi) (radical : Radical) :
    cycle.val.val (SemidirectProduct.inr element) (SemidirectProduct.inl radical) = 0 := by
  have identity := congrArg (fun cochain : crossedCocycles
    (representation.comp SemidirectProduct.inl) => cochain.val (action element radical))
    (mixedZero element)
  change cycle.val.val (SemidirectProduct.inr element)
      (SemidirectProduct.inl (action element⁻¹ (action element radical))) -
    cycle.val.val (SemidirectProduct.inl (action element radical))
      (SemidirectProduct.inr element) = 0 at identity
  have inverse : action element⁻¹ (action element radical) = radical := by
    simp
  rw [inverse, radicalLevi, sub_zero] at identity
  exact identity

theorem mixedZeroCycle_radical_second (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (element : SemidirectProduct Radical Levi action) (radical : Radical) :
    cycle.val.val element (SemidirectProduct.inl radical) = 0 := by
  have identity := cycle.val.property (SemidirectProduct.inl element.left)
    (SemidirectProduct.inr element.right) (SemidirectProduct.inl radical)
  rw [mixedZeroCycle_levi_radical action representation cycle radicalLevi mixedZero,
    map_zero, mixedZeroCycle_radical_first action representation cycle radicalLevi,
    radicalLevi] at identity
  have negZero : -cycle.val.val element (SemidirectProduct.inl radical) = 0 := by
    simpa only [← semidirect_factorization, zero_sub, add_zero, sub_zero] using identity
  exact neg_eq_zero.mp negZero

theorem mixedZeroCycle_radical_shift_right (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (first second : SemidirectProduct Radical Levi action) (radical : Radical) :
    cycle.val.val first (second * SemidirectProduct.inl radical) = cycle.val.val first second := by
  have identity := cycle.val.property first second (SemidirectProduct.inl radical)
  rw [mixedZeroCycle_radical_second action representation cycle radicalLevi mixedZero,
    mixedZeroCycle_radical_second action representation cycle radicalLevi mixedZero,
    map_zero] at identity
  apply sub_eq_zero.mp
  simpa only [sub_zero, zero_add] using identity

theorem semidirect_radical_commutation (element : SemidirectProduct Radical Levi action)
    (radical : Radical) :
    SemidirectProduct.inl radical * element = element *
      SemidirectProduct.inl (action element.right⁻¹ (element.left⁻¹ * radical * element.left)) := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, mul_assoc]
  · simp [SemidirectProduct.mul_right]

theorem mixedZeroCycle_radical_shift_second (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (first second : SemidirectProduct Radical Levi action) (radical : Radical) :
    cycle.val.val first (SemidirectProduct.inl radical * second) = cycle.val.val first second := by
  rw [semidirect_radical_commutation]
  exact mixedZeroCycle_radical_shift_right action representation cycle radicalLevi mixedZero _ _ _

theorem mixedZeroCycle_radical_shift_first (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (first second : SemidirectProduct Radical Levi action) (radical : Radical) :
    cycle.val.val (first * SemidirectProduct.inl radical) second = cycle.val.val first second := by
  have identity := cycle.val.property first (SemidirectProduct.inl radical) second
  rw [mixedZeroCycle_radical_first action representation cycle radicalLevi, map_zero,
    mixedZeroCycle_radical_second action representation cycle radicalLevi mixedZero,
    mixedZeroCycle_radical_shift_second action representation cycle radicalLevi mixedZero] at identity
  apply sub_eq_zero.mp
  convert congrArg Neg.neg identity using 1 <;> abel

theorem mixedZeroCycle_values_invariant (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (first second : SemidirectProduct Radical Levi action) :
    cycle.val.val first second ∈ semidirectRadicalInvariants action representation := by
  intro radical
  have identity := cycle.val.property (SemidirectProduct.inl radical) first second
  rw [mixedZeroCycle_radical_first action representation cycle radicalLevi,
    mixedZeroCycle_radical_first action representation cycle radicalLevi,
    semidirect_radical_commutation,
    mixedZeroCycle_radical_shift_first action representation cycle radicalLevi mixedZero] at identity
  apply sub_eq_zero.mp
  simpa only [add_zero, sub_zero] using identity

theorem mixedZeroCycle_levi_coordinates (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0)
    (first second : SemidirectProduct Radical Levi action) :
    cycle.val.val first second =
      cycle.val.val (SemidirectProduct.inr first.right) (SemidirectProduct.inr second.right) := by
  conv_lhs => rw [semidirect_factorization action first, semidirect_factorization action second]
  rw [mixedZeroCycle_radical_shift_second action representation cycle radicalLevi mixedZero,
    semidirect_radical_commutation,
    mixedZeroCycle_radical_shift_first action representation cycle radicalLevi mixedZero]

def mixedZeroLeviCycle (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0) :
    inhomogeneousTwoCycles (semidirectInvariantRepresentation action representation) :=
  ⟨fun first second =>
    ⟨cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second),
      mixedZeroCycle_values_invariant action representation cycle radicalLevi mixedZero _ _⟩, by
    intro first second third
    apply Subtype.ext
    change representation (SemidirectProduct.inr first)
          (cycle.val.val (SemidirectProduct.inr second) (SemidirectProduct.inr third)) -
        cycle.val.val (SemidirectProduct.inr (first * second)) (SemidirectProduct.inr third) +
        cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr (second * third)) -
        cycle.val.val (SemidirectProduct.inr first) (SemidirectProduct.inr second) = 0
    simpa only [map_mul] using
      cycle.val.property (SemidirectProduct.inr first) (SemidirectProduct.inr second)
        (SemidirectProduct.inr third)⟩

theorem mixedZeroCycle_eq_inflation (cycle : radicalZeroTwoCycles action representation)
    (radicalLevi : ∀ radical element,
      cycle.val.val (SemidirectProduct.inl radical) (SemidirectProduct.inr element) = 0)
    (mixedZero : ∀ element, mixedCrossedMap action representation element cycle = 0) :
    cycle.val = semidirectInflationCycles action representation
      (mixedZeroLeviCycle action representation cycle radicalLevi mixedZero) := by
  apply Subtype.ext
  funext first second
  exact mixedZeroCycle_levi_coordinates action representation cycle radicalLevi mixedZero first second

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
