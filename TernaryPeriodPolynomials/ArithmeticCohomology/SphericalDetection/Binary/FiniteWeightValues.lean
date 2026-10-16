module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ExtremalSpherical

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspFiniteWeightValues (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    Submodule ℂ (cuspAffineSmoothValues cusp) where
  carrier := {vector |
    (∀ element : level, cusp.π (atFinite element.val) vector.val = vector.val) ∧
    ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val = (angle : ℂ) ^ weight • vector.val}
  zero_mem' := by constructor <;> intro element <;> simp
  add_mem' {first second} first_mem second_mem := by
    constructor
    · intro element
      change cusp.π _ (first.val + second.val) = first.val + second.val
      rw [map_add, first_mem.1, second_mem.1]
    · intro angle
      change cusp.π _ (first.val + second.val) = (angle : ℂ) ^ weight • (first.val + second.val)
      rw [map_add, first_mem.2, second_mem.2, smul_add]
  smul_mem' scalar vector member := by
    constructor
    · intro element
      change cusp.π _ (scalar • vector.val) = scalar • vector.val
      rw [map_smul, member.1]
    · intro angle
      change cusp.π _ (scalar • vector.val) = (angle : ℂ) ^ weight • (scalar • vector.val)
      rw [map_smul, member.2, smul_comm]

theorem cuspFiniteOperator_real (cusp : CuspidalRepresentation) (finite : BinaryFiniteGL)
    (matrix : BinaryRealGL) (vector : cusp.H) :
    cuspUnitaryOperator cusp (atFinite finite) (cusp.π (atInfinity matrix) vector) =
      cusp.π (atInfinity matrix) (cuspUnitaryOperator cusp (atFinite finite) vector) := by
  change (cusp.π (atFinite finite) * cusp.π (atInfinity matrix)) vector =
    (cusp.π (atInfinity matrix) * cusp.π (atFinite finite)) vector
  rw [← map_mul, ← map_mul, (atInfinity_commute_atFinite matrix finite).symm.eq]

theorem cuspFiniteWeightValues_lowering (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cuspAffineSmoothValues cusp) (member : vector ∈ cuspFiniteWeightValues cusp level weight) :
    cuspLoweringOperator cusp weight vector ∈ cuspFiniteWeightValues cusp level (weight - 2) := by
  constructor
  · intro element
    have identity := cuspLoweringVector_intertwiner cusp (cuspUnitaryOperator cusp (atFinite element.val))
      (cuspFiniteOperator_real cusp element.val) weight vector.val (cuspAffineSmoothValues_differentiable cusp vector)
    change cuspLoweringVector cusp weight (cusp.π (atFinite element.val) vector.val) =
      cusp.π (atFinite element.val) (cuspLoweringVector cusp weight vector.val) at identity
    rw [member.1 element] at identity
    exact identity.symm
  · exact cuspLoweringVector_rotation cusp vector.val weight vector.property member.2

theorem cuspFiniteWeightValues_raising (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (vector : cuspAffineSmoothValues cusp) (member : vector ∈ cuspFiniteWeightValues cusp level weight) :
    cuspRaisingOperator cusp weight vector ∈ cuspFiniteWeightValues cusp level (weight + 2) := by
  constructor
  · intro element
    have identity := cuspRaisingVector_intertwiner cusp (cuspUnitaryOperator cusp (atFinite element.val))
      (cuspFiniteOperator_real cusp element.val) weight vector.val (cuspAffineSmoothValues_differentiable cusp vector)
    change cuspRaisingVector cusp weight (cusp.π (atFinite element.val) vector.val) =
      cusp.π (atFinite element.val) (cuspRaisingVector cusp weight vector.val) at identity
    rw [member.1 element] at identity
    exact identity.symm
  · exact cuspRaisingVector_rotation cusp vector.val weight vector.property member.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
