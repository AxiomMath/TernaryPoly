module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Kernel

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Value : Type} [Group GroupType]
  [AddCommGroup Value] [Module ℂ Value]
  (representation : Representation ℂ GroupType Value)

def centralCyclePrimitive (central : GroupType)
    (cycle : inhomogeneousTwoCycles representation) : GroupType → Value :=
  fun element => cycle.val central element - cycle.val element central

theorem centralCyclePrimitive_boundary (central : GroupType)
    (commutes : ∀ element, central * element = element * central)
    (cycle : inhomogeneousTwoCycles representation) (first second : GroupType) :
    (inhomogeneousBoundaryMap representation
      (centralCyclePrimitive representation central cycle)).val first second =
      representation central (cycle.val first second) - cycle.val first second := by
  have firstIdentity := cycle.property central first second
  have secondIdentity := cycle.property first central second
  have thirdIdentity := cycle.property first second central
  rw [commutes first] at firstIdentity
  rw [commutes second] at secondIdentity
  change representation first (cycle.val central second - cycle.val second central) -
    (cycle.val central (first * second) - cycle.val (first * second) central) +
    (cycle.val central first - cycle.val first central) = _
  rw [map_sub]
  have combined := congrArg₂ (fun first second : Value => first - second)
    firstIdentity secondIdentity
  have combined := congrArg₂ (fun first second : Value => first + second) combined thirdIdentity
  apply sub_eq_zero.mp
  convert congrArg Neg.neg combined using 1 <;> abel

theorem inhomogeneousH2_zero_of_central_neg (central : GroupType)
    (commutes : ∀ element, central * element = element * central)
    (actsNeg : ∀ value, representation central value = -value)
    (coordinate : InhomogeneousH2 representation) : coordinate = 0 := by
  obtain ⟨cycle, rfl⟩ := (inhomogeneousBoundaries representation).mkQ_surjective coordinate
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨(- (1 / 2 : ℂ)) • centralCyclePrimitive representation central cycle, ?_⟩
  rw [map_smul]
  apply Subtype.ext
  funext first second
  change (- (1 / 2 : ℂ)) •
    (inhomogeneousBoundaryMap representation
      (centralCyclePrimitive representation central cycle)).val first second = cycle.val first second
  rw [centralCyclePrimitive_boundary representation central commutes, actsNeg]
  have scalar : (- (1 / 2 : ℂ)) * (-1 - 1) = 1 := by norm_num
  calc
    _ = ((- (1 / 2 : ℂ)) * (-1 - 1)) • cycle.val first second := by
      rw [mul_smul, sub_smul, neg_one_smul, one_smul]
    _ = cycle.val first second := by rw [scalar, one_smul]

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
