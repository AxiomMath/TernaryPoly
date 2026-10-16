module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.ExplicitRadicalBinaryEquivZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerParabolic

@[expose] public section


/-!
# The degree-`0` inner bad-line arithmetic binary map lands in the parabolic submodule

Degree-`0` analogue of the positive-degree chain `innerBadLineExplicitBinaryMap` →
`innerBadLineArithmeticBinaryMap` → `innerBadLineArithmeticBinaryMap_parabolic`
(`ExplicitBinaryAction.lean`, `BinaryLeviReduction.lean`, `InnerParabolic.lean`), using
`explicitRadicalBinaryEquivZero` in place of the positive-degree `explicitRadicalBinaryEquiv`.
Every other piece of the chain (`binaryArithmeticRepresentation`, `binaryLeviRepresentation`,
`binaryLeviH1Equiv`, `binaryLeviH1Equiv_restriction_zero`, `standardBadLineInnerMixedMap`,
`innerBadLineLocalEquiv`, `locallyInner_mixed_restriction_zero`, `innerBadLineMixedMap`,
`binaryParabolicH1`) is already degree-generic in the library, with no `0 < degree` hypothesis.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairing


theorem explicitRadicalBinaryEquivZero_equivariant
    (element : ℤˣ × binaryArithmeticLevel)
    (coordinate : CrossedH1 ((standardBadLineRepresentation 0).comp SemidirectProduct.inl)) :
    explicitRadicalBinaryEquivZero
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation 0) element coordinate) =
      binaryLeviRepresentation 0 element (explicitRadicalBinaryEquivZero coordinate) := by
  obtain ⟨pair, rfl⟩ := standardRadicalH1_binaryPair_representative_zero coordinate
  rw [leviCrossedH1Representation_mk, leviCrossedAction_binaryPair,
    explicitBinaryPairCocycle_coordinate_zero, explicitBinaryPairCocycle_coordinate_zero]
  exact binaryPairWedge_matrixAction 0 (binaryIntegralComplex element.2.val) pair

theorem explicitRadicalBinaryZero_transport_eq :
    coefficientTransportRepresentation
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation 0)) explicitRadicalBinaryEquivZero =
      binaryLeviRepresentation 0 := by
  apply MonoidHom.ext
  intro element
  apply LinearMap.ext
  intro polynomial
  rw [coefficientTransportRepresentation_apply, explicitRadicalBinaryEquivZero_equivariant,
    LinearEquiv.apply_symm_apply]

/-- **Degree-`0` analogue of `explicitBinaryMixedH1Equiv`.** -/
def explicitBinaryMixedH1EquivZero :
    CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation 0)) ≃ₗ[ℂ] CrossedH1 (binaryLeviRepresentation 0) :=
  (crossedH1CoefficientEquiv
    (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation 0)) explicitRadicalBinaryEquivZero).trans
    (crossedH1RepresentationEqEquiv _ _ explicitRadicalBinaryZero_transport_eq)

def innerBadLineExplicitBinaryMapZero :
    innerBadLineClasses 0 →ₗ[ℂ] CrossedH1 (binaryLeviRepresentation 0) :=
  explicitBinaryMixedH1EquivZero.toLinearMap.comp (innerBadLineMixedMap 0)

theorem innerBadLineExplicitBinaryMapZero_injective :
    Function.Injective innerBadLineExplicitBinaryMapZero :=
  explicitBinaryMixedH1EquivZero.injective.comp (innerBadLineMixedMap_injective 0)

theorem explicitBinaryMixedH1EquivZero_restriction_zero {Source : Type} [Group Source]
    (homomorphism : Source →* (ℤˣ × binaryArithmeticLevel))
    (coordinate : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation 0)))
    (zero : crossedPullbackH1 homomorphism
      (leviCrossedH1Representation integralBadLineSplitting.conjAct (standardBadLineRepresentation 0))
      coordinate = 0) :
    crossedPullbackH1 homomorphism (binaryLeviRepresentation 0)
      (explicitBinaryMixedH1EquivZero coordinate) = 0 := by
  apply crossedH1RepresentationEqEquiv_restriction_zero homomorphism _ _
    explicitRadicalBinaryZero_transport_eq
  exact crossedH1CoefficientEquiv_restriction_zero homomorphism _
    explicitRadicalBinaryEquivZero coordinate zero

/-- **Degree-`0` analogue of `innerBadLineArithmeticBinaryMap`.** -/
def innerBadLineArithmeticBinaryMapZero :
    innerBadLineClasses 0 →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation 0) :=
  (binaryLeviH1Equiv 0).toLinearMap.comp innerBadLineExplicitBinaryMapZero

theorem innerBadLineArithmeticBinaryMapZero_injective :
    Function.Injective innerBadLineArithmeticBinaryMapZero :=
  (binaryLeviH1Equiv 0).injective.comp innerBadLineExplicitBinaryMapZero_injective

/-- **Degree-`0` analogue of `innerBadLineArithmeticBinaryMap_parabolic`.** -/
theorem innerBadLineArithmeticBinaryMapZero_parabolic
    (coordinate : innerBadLineClasses 0) :
    innerBadLineArithmeticBinaryMapZero coordinate ∈ binaryParabolicH1 0 := by
  apply (Submodule.mem_iInf (M := CrossedH1 (binaryArithmeticRepresentation 0)) _).mpr
  intro frame
  change crossedPullbackH1 (binaryCuspLevel frame).subtype (binaryArithmeticRepresentation 0)
    (binaryLeviH1Equiv 0 (explicitBinaryMixedH1EquivZero
      (standardBadLineInnerMixedMap 0 (innerBadLineLocalEquiv 0 coordinate)))) = 0
  apply binaryLeviH1Equiv_restriction_zero
  apply explicitBinaryMixedH1EquivZero_restriction_zero
  apply locallyInner_mixed_restriction_zero 0 (binaryEdge frame) (binaryEdge_endpoint frame)
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

end TernaryPeriodPolynomials.Argument.FacePairing
