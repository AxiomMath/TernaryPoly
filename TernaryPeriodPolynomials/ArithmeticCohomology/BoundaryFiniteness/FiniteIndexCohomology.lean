module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.ArithmeticStabilizers

@[expose] public section


namespace TernaryPeriodPolynomials.BoundaryFiniteness.FiniteIndexCohomology

noncomputable section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def cosetEvaluation (level : Subgroup G) (action : Representation ℂ level V) :
    Representation.coindV level.subtype action →ₗ[ℂ] (G ⧸ level → V) where
  toFun function coset := function.val coset.out⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cosetEvaluation_injective (level : Subgroup G) (action : Representation ℂ level V) :
    Function.Injective (cosetEvaluation level action) := by
  intro left right equality
  apply Subtype.ext
  funext element
  let coset : G ⧸ level := QuotientGroup.mk element⁻¹
  have membership : element * coset.out ∈ level := by
    have coset_equality : QuotientGroup.mk element⁻¹ = coset := rfl
    rw [← Quotient.out_eq coset] at coset_equality
    simpa only [inv_inv] using QuotientGroup.eq.mp coset_equality
  let correction : level := ⟨element * coset.out, membership⟩
  have left_equation := left.property correction coset.out⁻¹
  have right_equation := right.property correction coset.out⁻¹
  change left.val ((element * coset.out) * coset.out⁻¹) = action correction (left.val coset.out⁻¹) at left_equation
  change right.val ((element * coset.out) * coset.out⁻¹) = action correction (right.val coset.out⁻¹) at right_equation
  rw [mul_inv_cancel_right] at left_equation right_equation
  rw [left_equation, right_equation]
  exact congrArg (action correction) (congrFun equality coset)

theorem coinduced_finiteDimensional (level : Subgroup G) [level.FiniteIndex]
    (action : Representation ℂ level V) [FiniteDimensional ℂ V] :
    FiniteDimensional ℂ (Representation.coindV level.subtype action) :=
  FiniteDimensional.of_injective (cosetEvaluation level action) (cosetEvaluation_injective level action)

def parabolicRepresentation (degree : ℕ) (character : GeneralEisenstein.RankOneCharacter)
    (side : GeneralEisenstein.Side) (orbit : ArithmeticCohomology.flagOrbits side) :
    Rep ℂ (ArithmeticStabilizers.integralParabolic side) :=
  Rep.coind (ArithmeticStabilizers.localLevel side (ArithmeticStabilizers.orbitRepresentative side orbit)).subtype
    (ArithmeticStabilizers.localRepresentation degree character side orbit)

instance parabolicRepresentation_finiteDimensional (degree : ℕ) (character : GeneralEisenstein.RankOneCharacter)
    (side : GeneralEisenstein.Side) (orbit : ArithmeticCohomology.flagOrbits side) :
    FiniteDimensional ℂ (parabolicRepresentation degree character side orbit) :=
  coinduced_finiteDimensional _ (ArithmeticStabilizers.localRepresentation degree character side orbit).ρ

def parabolicCohomologyEquiv (degree : ℕ) (character : GeneralEisenstein.RankOneCharacter)
    (side : GeneralEisenstein.Side) (orbit : ArithmeticCohomology.flagOrbits side) :
    groupCohomology.H2 (parabolicRepresentation degree character side orbit) ≃ₗ[ℂ]
      groupCohomology.H2 (ArithmeticCohomology.stabilizerRepresentation degree character side orbit) :=
  (groupCohomology.coindIso (ArithmeticStabilizers.localRepresentation degree character side orbit) 2).toLinearEquiv.trans
    (ArithmeticStabilizers.localCohomologyEquiv degree character side orbit)

end

end TernaryPeriodPolynomials.BoundaryFiniteness.FiniteIndexCohomology
