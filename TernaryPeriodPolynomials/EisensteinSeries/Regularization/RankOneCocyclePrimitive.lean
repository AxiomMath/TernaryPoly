module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.TupleOperatorAlgebra

@[expose] public section


namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem operator_commutator_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (first second bracket : Module.End ℂ V) (identity : first * second - second * first = bracket)
    (vector : V) : first (second vector) = second (first vector) + bracket vector := by
  have applied := congrArg (fun operator : Module.End ℂ V => operator vector) identity
  change first (second vector) - second (first vector) = bracket vector at applied
  exact (sub_eq_iff_eq_add.mp applied).trans (add_comm _ _)

noncomputable def rankOneCocyclePrimitive {V : Type*} [AddCommGroup V] [Module ℂ V]
    (split symmetric rotation : Module.End ℂ V) (splitValue symmetricValue rotationValue : V) : V :=
  split splitValue + symmetric symmetricValue - rotation rotationValue

theorem rankOneCocyclePrimitive_rotation {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rotation split symmetric rotationDifference splitDifference symmetricDifference : Module.End ℂ V)
    (rotationValue splitValue symmetricValue : V)
    (mixed_rotation : rotation * rotationDifference - rotationDifference * rotation = 0)
    (mixed_split : rotation * splitDifference - splitDifference * rotation = -(2 • symmetricDifference))
    (mixed_symmetric : rotation * symmetricDifference - symmetricDifference * rotation = 2 • splitDifference)
    (cocycle_split : rotation splitValue - split rotationValue = -(2 • symmetricValue))
    (cocycle_symmetric : rotation symmetricValue - symmetric rotationValue = 2 • splitValue) :
    rotation (rankOneCocyclePrimitive splitDifference symmetricDifference rotationDifference
      splitValue symmetricValue rotationValue) =
      (splitDifference * split + symmetricDifference * symmetric - rotationDifference * rotation) rotationValue := by
  simp only [rankOneCocyclePrimitive, map_sub, map_add]
  rw [operator_commutator_apply _ _ _ mixed_split, operator_commutator_apply _ _ _ mixed_symmetric,
    operator_commutator_apply _ _ _ mixed_rotation,
    sub_eq_iff_eq_add.mp cocycle_split, sub_eq_iff_eq_add.mp cocycle_symmetric]
  simp only [two_smul, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply, map_add, map_neg]
  abel

theorem rankOneCocyclePrimitive_split {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rotation split symmetric rotationDifference splitDifference symmetricDifference : Module.End ℂ V)
    (rotationValue splitValue symmetricValue : V)
    (mixed_rotation : split * rotationDifference - rotationDifference * split = 2 • symmetricDifference)
    (mixed_split : split * splitDifference - splitDifference * split = 0)
    (mixed_symmetric : split * symmetricDifference - symmetricDifference * split = 2 • rotationDifference)
    (cocycle_rotation : split rotationValue - rotation splitValue = 2 • symmetricValue)
    (cocycle_symmetric : split symmetricValue - symmetric splitValue = 2 • rotationValue) :
    split (rankOneCocyclePrimitive splitDifference symmetricDifference rotationDifference
      splitValue symmetricValue rotationValue) =
      (splitDifference * split + symmetricDifference * symmetric - rotationDifference * rotation) splitValue := by
  simp only [rankOneCocyclePrimitive, map_sub, map_add]
  rw [operator_commutator_apply _ _ _ mixed_split, operator_commutator_apply _ _ _ mixed_symmetric,
    operator_commutator_apply _ _ _ mixed_rotation,
    sub_eq_iff_eq_add.mp cocycle_rotation, sub_eq_iff_eq_add.mp cocycle_symmetric]
  simp only [two_smul, LinearMap.add_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.End.mul_apply, map_add]
  abel

theorem rankOneCocyclePrimitive_symmetric {V : Type*} [AddCommGroup V] [Module ℂ V]
    (rotation split symmetric rotationDifference splitDifference symmetricDifference : Module.End ℂ V)
    (rotationValue splitValue symmetricValue : V)
    (mixed_rotation : symmetric * rotationDifference - rotationDifference * symmetric = -(2 • splitDifference))
    (mixed_split : symmetric * splitDifference - splitDifference * symmetric = -(2 • rotationDifference))
    (mixed_symmetric : symmetric * symmetricDifference - symmetricDifference * symmetric = 0)
    (cocycle_rotation : symmetric rotationValue - rotation symmetricValue = -(2 • splitValue))
    (cocycle_split : symmetric splitValue - split symmetricValue = -(2 • rotationValue)) :
    symmetric (rankOneCocyclePrimitive splitDifference symmetricDifference rotationDifference
      splitValue symmetricValue rotationValue) =
      (splitDifference * split + symmetricDifference * symmetric - rotationDifference * rotation) symmetricValue := by
  simp only [rankOneCocyclePrimitive, map_sub, map_add]
  rw [operator_commutator_apply _ _ _ mixed_split, operator_commutator_apply _ _ _ mixed_symmetric,
    operator_commutator_apply _ _ _ mixed_rotation,
    sub_eq_iff_eq_add.mp cocycle_rotation, sub_eq_iff_eq_add.mp cocycle_split]
  simp only [two_smul, LinearMap.neg_apply, LinearMap.add_apply, LinearMap.zero_apply,
    LinearMap.sub_apply, Module.End.mul_apply, map_add, map_neg]
  abel

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
