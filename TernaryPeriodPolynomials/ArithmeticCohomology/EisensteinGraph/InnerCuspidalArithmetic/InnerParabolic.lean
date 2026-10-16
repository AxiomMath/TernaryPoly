module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerEdgePrimitives
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.Cusps
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.CohomologyRestrictionTransport

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binaryParabolicH1 (degree : ℕ) : Submodule ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
  ⨅ frame : GeneralLinearGroup (Fin 2) ℚ,
    (crossedPullbackH1 (binaryCuspLevel frame).subtype (binaryArithmeticRepresentation degree)).ker

theorem innerBadLineArithmeticBinaryMap_parabolic (degree : ℕ) (positive : 0 < degree)
    (coordinate : innerBadLineClasses degree) :
    innerBadLineArithmeticBinaryMap degree positive coordinate ∈ binaryParabolicH1 degree := by
  apply (Submodule.mem_iInf (M := CrossedH1 (binaryArithmeticRepresentation degree)) _).mpr
  intro frame
  change crossedPullbackH1 (binaryCuspLevel frame).subtype (binaryArithmeticRepresentation degree)
    (binaryLeviH1Equiv degree (explicitBinaryMixedH1Equiv degree positive
      (standardBadLineInnerMixedMap degree (innerBadLineLocalEquiv degree coordinate)))) = 0
  apply binaryLeviH1Equiv_restriction_zero
  apply explicitBinaryMixedH1Equiv_restriction_zero
  apply locallyInner_mixed_restriction_zero degree (binaryEdge frame) (binaryEdge_endpoint frame)
    ((1 : binaryCuspLevel frame →* ℤˣ).prod (binaryCuspLevel frame).subtype)
  · intro radical
    change (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val ∈
      fixedPointLevel rationalLevel (binaryEdge frame)
    exact binaryEdge_radical_mem frame radical
  · intro element
    change (standardBadLineSemidirectEquiv (SemidirectProduct.inr (1, element.val))).val ∈
      fixedPointLevel rationalLevel (binaryEdge frame)
    rw [standardBadLine_inr_binary]
    exact binaryCusp_mem_edge frame element

def innerBadLineParabolicMap (degree : ℕ) (positive : 0 < degree) :
    innerBadLineClasses degree →ₗ[ℂ] binaryParabolicH1 degree :=
  (innerBadLineArithmeticBinaryMap degree positive).codRestrict _
    (innerBadLineArithmeticBinaryMap_parabolic degree positive)

theorem innerBadLineParabolicMap_injective (degree : ℕ) (positive : 0 < degree) :
    Function.Injective (innerBadLineParabolicMap degree positive) := by
  intro first second equality
  apply innerBadLineArithmeticBinaryMap_injective degree positive
  exact congrArg Subtype.val equality

theorem innerBadLineParabolicMap_zero_iff (degree : ℕ) (positive : 0 < degree)
    (coordinate : innerBadLineClasses degree) :
    innerBadLineParabolicMap degree positive coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro zero
    apply innerBadLineParabolicMap_injective degree positive
    exact zero.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
