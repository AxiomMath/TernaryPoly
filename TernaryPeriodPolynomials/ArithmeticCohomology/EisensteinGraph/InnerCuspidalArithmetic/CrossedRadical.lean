module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.DiscreteRadical

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Value : Type} [Group GroupType] [AddCommGroup Value] [Module ℂ Value]

def crossedCocycles (representation : Representation ℂ GroupType Value) :
    Submodule ℂ (GroupType → Value) where
  carrier := {cochain | ∀ first second,
    cochain (first * second) = cochain first + representation first (cochain second)}
  zero_mem' := by simp
  add_mem' := by
    intro first second firstCocycle secondCocycle elementOne elementTwo
    change first (elementOne * elementTwo) + second (elementOne * elementTwo) = _
    rw [firstCocycle elementOne elementTwo, secondCocycle elementOne elementTwo]
    simp only [Pi.add_apply, map_add]
    abel
  smul_mem' := by
    intro scalar cochain cocycle first second
    change scalar • cochain (first * second) = _
    rw [cocycle first second]
    simp only [Pi.smul_apply, map_smul, smul_add]

def crossedBoundary (representation : Representation ℂ GroupType Value) :
    Value →ₗ[ℂ] crossedCocycles representation where
  toFun value := ⟨fun element => representation element value - value, by
    intro first second
    change representation (first * second) value - value =
      (representation first value - value) + representation first (representation second value - value)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' first second := by
    apply Subtype.ext
    funext element
    change representation element (first + second) - (first + second) =
      (representation element first - first) + (representation element second - second)
    rw [map_add]
    abel
  map_smul' scalar value := by
    apply Subtype.ext
    funext element
    change representation element (scalar • value) - scalar • value =
      scalar • (representation element value - value)
    rw [map_smul, smul_sub]

theorem crossedCocycle_one (representation : Representation ℂ GroupType Value)
    (cochain : crossedCocycles representation) : cochain.val 1 = 0 := by
  have identity := cochain.property 1 1
  simp only [one_mul, map_one, Module.End.one_apply] at identity
  exact add_eq_left.mp identity.symm

def crossedCocycleZeroSubgroup (representation : Representation ℂ GroupType Value)
    (cochain : crossedCocycles representation) : Subgroup GroupType where
  carrier := {element | cochain.val element = 0}
  one_mem' := crossedCocycle_one representation cochain
  mul_mem' := by
    intro first second firstZero secondZero
    change cochain.val (first * second) = 0
    rw [cochain.property, firstZero, secondZero, map_zero, add_zero]
  inv_mem' := by
    intro element zero
    change cochain.val element⁻¹ = 0
    have identity := cochain.property element element⁻¹
    rw [mul_inv_cancel, crossedCocycle_one, zero, zero_add] at identity
    have acted := congrArg (representation element⁻¹) identity.symm
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using acted

def integralRadicalRationalHom : Multiplicative (ℤ × ℤ) →* RationalGL3 :=
  integralRational.comp (integralBadLineStabilizer.subtype.comp integralBadLineRadicalEmbedding)

def radicalRepresentation (degree : ℕ) :
    Representation ℂ (Multiplicative (ℤ × ℤ)) (HomogeneousPoly degree) :=
  (rationalCoefficientComponent degree trivialCharacter).comp integralRadicalRationalHom

def integralRadicalGenerator (index : Fin 2) : Multiplicative (ℤ × ℤ) :=
  Multiplicative.ofAdd (if index = 0 then 1 else 0, if index = 1 then 1 else 0)

theorem integralRadicalRationalHom_generator (index : Fin 2) :
    integralRadicalRationalHom (integralRadicalGenerator index) = radicalGenerator index := by
  change GeneralLinearGroup.map (Int.castRingHom ℚ)
    (lineUnipotent (if index = 0 then 1 else 0) (if index = 1 then 1 else 0)) = _
  rw [map_lineUnipotent]
  fin_cases index <;> rfl

theorem radicalRepresentation_generator (degree : ℕ) (index : Fin 2) :
    radicalRepresentation degree (integralRadicalGenerator index) =
      rationalCoefficientComponent degree trivialCharacter (radicalGenerator index) := by
  change rationalCoefficientComponent degree trivialCharacter
    (integralRadicalRationalHom (integralRadicalGenerator index)) = _
  rw [integralRadicalRationalHom_generator]

theorem integralRadicalGenerator_factor (coordinates : Multiplicative (ℤ × ℤ)) :
    integralRadicalGenerator 0 ^ coordinates.toAdd.1 *
      integralRadicalGenerator 1 ^ coordinates.toAdd.2 = coordinates := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_zpow]
  change coordinates.toAdd.1 • ((1, 0) : ℤ × ℤ) +
    coordinates.toAdd.2 • ((0, 1) : ℤ × ℤ) = coordinates.toAdd
  ext <;> simp

theorem radicalCrossedCocycle_zero_of_generators (degree : ℕ)
    (cochain : crossedCocycles (radicalRepresentation degree))
    (firstZero : cochain.val (integralRadicalGenerator 0) = 0)
    (secondZero : cochain.val (integralRadicalGenerator 1) = 0) : cochain = 0 := by
  apply Subtype.ext
  funext coordinates
  change coordinates ∈ crossedCocycleZeroSubgroup (radicalRepresentation degree) cochain
  rw [← integralRadicalGenerator_factor coordinates]
  exact (crossedCocycleZeroSubgroup _ cochain).mul_mem
    ((crossedCocycleZeroSubgroup _ cochain).zpow_mem firstZero _)
    ((crossedCocycleZeroSubgroup _ cochain).zpow_mem secondZero _)

def radicalCrossedEvaluation (degree : ℕ) :
    crossedCocycles (radicalRepresentation degree) →ₗ[ℂ] discreteRadicalCycles degree where
  toFun cochain := ⟨(cochain.val (integralRadicalGenerator 0),
    cochain.val (integralRadicalGenerator 1)), by
    change radicalDifference degree 0 (cochain.val (integralRadicalGenerator 1)) -
      radicalDifference degree 1 (cochain.val (integralRadicalGenerator 0)) = 0
    have first := cochain.property (integralRadicalGenerator 0) (integralRadicalGenerator 1)
    have second := cochain.property (integralRadicalGenerator 1) (integralRadicalGenerator 0)
    rw [mul_comm] at first
    rw [radicalRepresentation_generator] at first second
    have equality := first.symm.trans second
    simp only [radicalDifference, LinearMap.sub_apply, Module.End.one_apply]
    apply sub_eq_zero.mpr
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using equality⟩
  map_add' first second := by
    apply Subtype.ext
    rfl
  map_smul' scalar cochain := by
    apply Subtype.ext
    rfl

theorem radicalCrossedEvaluation_injective (degree : ℕ) :
    Function.Injective (radicalCrossedEvaluation degree) := by
  intro first second equality
  have firstEquality := congrArg (fun cycle : discreteRadicalCycles degree => cycle.val.1) equality
  have secondEquality := congrArg (fun cycle : discreteRadicalCycles degree => cycle.val.2) equality
  have zero := radicalCrossedCocycle_zero_of_generators degree (first - second)
    (sub_eq_zero.mpr firstEquality) (sub_eq_zero.mpr secondEquality)
  exact sub_eq_zero.mp zero

theorem radicalCrossedEvaluation_boundary (degree : ℕ) (positive : 0 < degree)
    (polynomial : HomogeneousPoly degree) :
    radicalCrossedEvaluation degree (crossedBoundary (radicalRepresentation degree) polynomial) =
      discreteRadicalBoundaryMap degree positive polynomial := by
  apply Subtype.ext
  apply Prod.ext
  · change radicalRepresentation degree (integralRadicalGenerator 0) polynomial - polynomial =
      radicalDifference degree 0 polynomial
    rw [radicalRepresentation_generator]
    rfl
  · change radicalRepresentation degree (integralRadicalGenerator 1) polynomial - polynomial =
      radicalDifference degree 1 polynomial
    rw [radicalRepresentation_generator]
    rfl

theorem radicalCrossed_coboundary_iff_evaluation (degree : ℕ) (positive : 0 < degree)
    (cochain : crossedCocycles (radicalRepresentation degree)) :
    cochain ∈ (crossedBoundary (radicalRepresentation degree)).range ↔
      radicalCrossedEvaluation degree cochain ∈ discreteRadicalBoundaries degree positive := by
  constructor
  · rintro ⟨polynomial, rfl⟩
    exact ⟨polynomial, (radicalCrossedEvaluation_boundary degree positive polynomial).symm⟩
  · rintro ⟨polynomial, equality⟩
    refine ⟨polynomial, radicalCrossedEvaluation_injective degree ?_⟩
    exact (radicalCrossedEvaluation_boundary degree positive polynomial).trans equality

def radicalCrossedBinaryCoordinate (degree : ℕ) (positive : 0 < degree) :
    crossedCocycles (radicalRepresentation degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (discreteRadicalBinaryEquiv degree positive).toLinearMap.comp
    ((discreteRadicalBoundaries degree positive).mkQ.comp (radicalCrossedEvaluation degree))

theorem radicalCrossedBinaryCoordinate_zero_iff (degree : ℕ) (positive : 0 < degree)
    (cochain : crossedCocycles (radicalRepresentation degree)) :
    radicalCrossedBinaryCoordinate degree positive cochain = 0 ↔
      cochain ∈ (crossedBoundary (radicalRepresentation degree)).range := by
  change discreteRadicalBinaryEquiv degree positive
    ((discreteRadicalBoundaries degree positive).mkQ (radicalCrossedEvaluation degree cochain)) =
      0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    radicalCrossed_coboundary_iff_evaluation degree positive cochain]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
