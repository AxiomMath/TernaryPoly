module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LeviCocycleAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binaryArithmeticRepresentation (degree : ℕ) :
    Representation ℂ binaryArithmeticLevel (Binary.HomogeneousPoly (degree + 1)) :=
  (Binary.homogeneousAction (degree + 1) 0).comp
    (binaryIntegralComplex.comp binaryArithmeticLevel.subtype)

def binaryLeviRepresentation (degree : ℕ) :
    Representation ℂ (ℤˣ × binaryArithmeticLevel) (Binary.HomogeneousPoly (degree + 1)) :=
  (binaryArithmeticRepresentation degree).comp (MonoidHom.snd ℤˣ binaryArithmeticLevel)

theorem explicitRadicalBinaryEquiv_equivariant (degree : ℕ) (positive : 0 < degree)
    (element : ℤˣ × binaryArithmeticLevel)
    (coordinate : CrossedH1 ((standardBadLineRepresentation degree).comp SemidirectProduct.inl)) :
    explicitRadicalBinaryEquiv degree positive
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree) element coordinate) =
      binaryLeviRepresentation degree element (explicitRadicalBinaryEquiv degree positive coordinate) := by
  obtain ⟨pair, rfl⟩ := standardRadicalH1_binaryPair_representative degree positive coordinate
  rw [leviCrossedH1Representation_mk, leviCrossedAction_binaryPair,
    explicitBinaryPairCocycle_coordinate, explicitBinaryPairCocycle_coordinate]
  exact binaryPairWedge_matrixAction degree (binaryIntegralComplex element.2.val) pair

theorem explicitRadicalBinary_transport_eq (degree : ℕ) (positive : 0 < degree) :
    coefficientTransportRepresentation
      (leviCrossedH1Representation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree)) (explicitRadicalBinaryEquiv degree positive) =
      binaryLeviRepresentation degree := by
  apply MonoidHom.ext
  intro element
  apply LinearMap.ext
  intro polynomial
  rw [coefficientTransportRepresentation_apply, explicitRadicalBinaryEquiv_equivariant,
    LinearEquiv.apply_symm_apply]

def explicitBinaryMixedH1Equiv (degree : ℕ) (positive : 0 < degree) :
    CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) ≃ₗ[ℂ] CrossedH1 (binaryLeviRepresentation degree) :=
  (crossedH1CoefficientEquiv
    (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) (explicitRadicalBinaryEquiv degree positive)).trans
    (crossedH1RepresentationEqEquiv _ _ (explicitRadicalBinary_transport_eq degree positive))

def innerBadLineExplicitBinaryMap (degree : ℕ) (positive : 0 < degree) :
    innerBadLineClasses degree →ₗ[ℂ] CrossedH1 (binaryLeviRepresentation degree) :=
  (explicitBinaryMixedH1Equiv degree positive).toLinearMap.comp (innerBadLineMixedMap degree)

theorem innerBadLineExplicitBinaryMap_injective (degree : ℕ) (positive : 0 < degree) :
    Function.Injective (innerBadLineExplicitBinaryMap degree positive) :=
  (explicitBinaryMixedH1Equiv degree positive).injective.comp (innerBadLineMixedMap_injective degree)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
