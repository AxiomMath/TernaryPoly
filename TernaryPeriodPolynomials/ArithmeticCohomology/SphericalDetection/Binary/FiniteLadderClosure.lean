module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderClosures
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ClosedLadderRange

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspHilbertWeightValues (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    Submodule ℂ cusp.H where
  carrier := {vector |
    (∀ element : level, cusp.π (atFinite element.val) vector = vector) ∧
    ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector}
  zero_mem' := by constructor <;> intro element <;> simp
  add_mem' {first second} first_mem second_mem := by
    constructor
    · intro element
      rw [map_add, first_mem.1, second_mem.1]
    · intro angle
      rw [map_add, first_mem.2, second_mem.2, smul_add]
  smul_mem' scalar vector member := by
    constructor
    · intro element
      rw [map_smul, member.1]
    · intro angle
      rw [map_smul, member.2, smul_comm]

theorem cuspHilbertWeightValues_isClosed (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    IsClosed (cuspHilbertWeightValues cusp level weight : Set cusp.H) := by
  change IsClosed {vector : cusp.H |
    (∀ element : level, cusp.π (atFinite element.val) vector = vector) ∧
    ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector}
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun element : level =>
      isClosed_eq (cuspUnitaryOperator cusp (atFinite element.val)).continuous continuous_id)
  · exact isClosed_iInter (fun angle : Circle =>
      isClosed_eq (cuspUnitaryOperator cusp (atInfinity (binaryRotations angle))).continuous
        (continuous_const.smul continuous_id))

def cuspFiniteRaisingPMap (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    cusp.H →ₗ.[ℂ] cusp.H :=
  (cuspRaisingPMap cusp weight).domRestrict (cuspHilbertWeightValues cusp level weight)

theorem cuspFiniteRaisingPMap_isClosable (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) :
    (cuspFiniteRaisingPMap cusp level weight).IsClosable :=
  (cuspRaisingPMap_isClosable cusp spherical weight).leIsClosable LinearPMap.domRestrict_le

theorem cuspFiniteRaisingPMap_bound (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (weight : ℤ) (positive : 0 < weight) (vector : (cuspFiniteRaisingPMap cusp level weight).domain) :
    ‖vector.val‖ ≤ ‖(cuspFiniteRaisingPMap cusp level weight vector : cusp.H)‖ := by
  let smooth : cuspAffineSmoothValues cusp := ⟨vector.val, vector.property.2⟩
  have rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) smooth.val =
      (angle : ℂ) ^ weight • smooth.val := vector.property.1.2
  have identity := cuspLadder_norm_identity cusp weight smooth rotation
  change ‖smooth.val‖ ≤ ‖(cuspRaisingOperator cusp weight smooth).val‖
  have positive_weight : (1 : ℝ) ≤ (weight : ℝ) := by exact_mod_cast positive
  have lower_bound : ‖smooth.val‖ ^ 2 ≤ (weight : ℝ) * ‖smooth.val‖ ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right positive_weight (sq_nonneg ‖smooth.val‖)
  nlinarith [sq_nonneg ‖(cuspLoweringOperator cusp weight smooth).val‖, norm_nonneg smooth.val,
    norm_nonneg (cuspRaisingOperator cusp weight smooth).val]

theorem cuspFiniteRaisingPMap_closure_bound (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    ‖vector.val‖ ≤ ‖((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H)‖ := by
  simpa only [NNReal.coe_one, one_mul] using
    closableLinearPMap_closure_bound (cuspFiniteRaisingPMap cusp level weight)
      (cuspFiniteRaisingPMap_isClosable cusp spherical level weight) 1
      (fun vector => by simpa using cuspFiniteRaisingPMap_bound cusp level weight positive vector) vector

theorem cuspFiniteRaisingPMap_closure_range_isClosed (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ) (positive : 0 < weight) :
    IsClosed ((cuspFiniteRaisingPMap cusp level weight).closure.toFun.range : Set cusp.H) :=
  closableLinearPMap_closure_range_isClosed (cuspFiniteRaisingPMap cusp level weight)
    (cuspFiniteRaisingPMap_isClosable cusp spherical level weight) 1
    (fun vector => by simpa using cuspFiniteRaisingPMap_bound cusp level weight positive vector)

theorem cuspFiniteRaisingPMap_closure_weights (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (level : Subgroup BinaryFiniteGL) (weight : ℤ)
    (vector : (cuspFiniteRaisingPMap cusp level weight).closure.domain) :
    vector.val ∈ cuspHilbertWeightValues cusp level weight ∧
      ((cuspFiniteRaisingPMap cusp level weight).closure vector : cusp.H) ∈ cuspHilbertWeightValues cusp level (weight + 2) := by
  apply closableLinearPMap_closure_constraints (cuspFiniteRaisingPMap cusp level weight)
    (cuspFiniteRaisingPMap_isClosable cusp spherical level weight)
    (cuspHilbertWeightValues cusp level weight) (cuspHilbertWeightValues cusp level (weight + 2))
    (cuspHilbertWeightValues_isClosed cusp level weight) (cuspHilbertWeightValues_isClosed cusp level (weight + 2))
    (fun _ member => member.1) _ vector
  intro value
  exact cuspFiniteWeightValues_raising cusp level weight ⟨value.val, value.property.2⟩ value.property.1

end TernaryPeriodPolynomials.SphericalDetection.Helpers
