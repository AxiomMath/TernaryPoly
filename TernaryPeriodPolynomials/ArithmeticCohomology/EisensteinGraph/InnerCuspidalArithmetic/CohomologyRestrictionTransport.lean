module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Mixed.Restriction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem crossedH1CoefficientEquiv_restriction_zero
    {Source GroupType Value Target : Type} [Group Source] [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value] [AddCommGroup Target] [Module ℂ Target]
    (homomorphism : Source →* GroupType) (representation : Representation ℂ GroupType Value)
    (equivalence : Value ≃ₗ[ℂ] Target) (coordinate : CrossedH1 representation)
    (zero : crossedPullbackH1 homomorphism representation coordinate = 0) :
    crossedPullbackH1 homomorphism (coefficientTransportRepresentation representation equivalence)
      (crossedH1CoefficientEquiv representation equivalence coordinate) = 0 := by
  obtain ⟨cochain, rfl⟩ := (crossedBoundaries representation).mkQ_surjective coordinate
  change (crossedBoundaries (representation.comp homomorphism)).mkQ
    (crossedPullbackCocycles homomorphism representation cochain) = 0 at zero
  obtain ⟨primitive, boundary⟩ := (Submodule.Quotient.mk_eq_zero _).mp zero
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨equivalence primitive, ?_⟩
  apply Subtype.ext
  funext element
  have pointwise := congrArg
    (fun cochain : crossedCocycles (representation.comp homomorphism) => cochain.val element) boundary
  change representation (homomorphism element) primitive - primitive = cochain.val (homomorphism element)
    at pointwise
  change coefficientTransportRepresentation representation equivalence (homomorphism element)
      (equivalence primitive) - equivalence primitive = equivalence (cochain.val (homomorphism element))
  rw [coefficientTransportRepresentation_apply, LinearEquiv.symm_apply_apply, ← map_sub, pointwise]

theorem crossedH1RepresentationEqEquiv_restriction_zero
    {Source GroupType Value : Type} [Group Source] [Group GroupType]
    [AddCommGroup Value] [Module ℂ Value]
    (homomorphism : Source →* GroupType) (first second : Representation ℂ GroupType Value)
    (same : first = second) (coordinate : CrossedH1 first)
    (zero : crossedPullbackH1 homomorphism first coordinate = 0) :
    crossedPullbackH1 homomorphism second (crossedH1RepresentationEqEquiv first second same coordinate) = 0 := by
  cases same
  have identity : crossedH1RepresentationEqEquiv first first rfl coordinate = coordinate := by
    obtain ⟨cochain, rfl⟩ := (crossedBoundaries first).mkQ_surjective coordinate
    rfl
  rw [identity]
  exact zero

theorem explicitBinaryMixedH1Equiv_restriction_zero {Source : Type} [Group Source]
    (degree : ℕ) (positive : 0 < degree) (homomorphism : Source →* (ℤˣ × binaryArithmeticLevel))
    (coordinate : CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)))
    (zero : crossedPullbackH1 homomorphism
      (leviCrossedH1Representation integralBadLineSplitting.conjAct (standardBadLineRepresentation degree))
      coordinate = 0) :
    crossedPullbackH1 homomorphism (binaryLeviRepresentation degree)
      (explicitBinaryMixedH1Equiv degree positive coordinate) = 0 := by
  apply crossedH1RepresentationEqEquiv_restriction_zero homomorphism _ _
    (explicitRadicalBinary_transport_eq degree positive)
  exact crossedH1CoefficientEquiv_restriction_zero homomorphism _
    (explicitRadicalBinaryEquiv degree positive) coordinate zero

theorem binaryLeviH1Equiv_restriction_zero {Source : Type} [Group Source]
    (degree : ℕ) (homomorphism : Source →* binaryArithmeticLevel)
    (coordinate : CrossedH1 (binaryLeviRepresentation degree))
    (zero : crossedPullbackH1 ((1 : Source →* ℤˣ).prod homomorphism)
      (binaryLeviRepresentation degree) coordinate = 0) :
    crossedPullbackH1 homomorphism (binaryArithmeticRepresentation degree)
      (binaryLeviH1Equiv degree coordinate) = 0 := by
  revert zero
  refine Quotient.inductionOn' coordinate ?_
  intro cochain zero
  change (crossedBoundaries ((binaryLeviRepresentation degree).comp
    ((1 : Source →* ℤˣ).prod homomorphism))).mkQ
    (crossedPullbackCocycles ((1 : Source →* ℤˣ).prod homomorphism)
      (binaryLeviRepresentation degree) cochain) = 0 at zero
  obtain ⟨primitive, boundary⟩ := (Submodule.Quotient.mk_eq_zero _).mp zero
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨primitive, ?_⟩
  apply Subtype.ext
  funext element
  have pointwise := congrArg
    (fun cochain : crossedCocycles ((binaryLeviRepresentation degree).comp
      ((1 : Source →* ℤˣ).prod homomorphism)) => cochain.val element) boundary
  change binaryArithmeticRepresentation degree (homomorphism element) primitive - primitive =
    cochain.val (1, homomorphism element) at pointwise ⊢
  exact pointwise

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
