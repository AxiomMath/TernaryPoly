module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.FiniteIndexCohomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.PresentationCohomology

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryFiniteness.ParabolicFiniteness

theorem stabilizer_H2_finiteDimensional (degree : ℕ) (character : RankOneCharacter) (side : Side)
    [Group.IsFinitelyPresented (ArithmeticStabilizers.integralParabolic side)]
    (orbit : ArithmeticCohomology.flagOrbits side) :
    FiniteDimensional ℂ (groupCohomology.H2
      (ArithmeticCohomology.stabilizerRepresentation degree character side orbit)) := by
  let := PresentationCohomology.H2_finiteDimensional
    (FiniteIndexCohomology.parabolicRepresentation degree character side orbit).ρ
  exact (FiniteIndexCohomology.parabolicCohomologyEquiv degree character side orbit).finiteDimensional

theorem boundary_finiteDimensional (degree : ℕ) (character : RankOneCharacter)
    [∀ side : Side, Group.IsFinitelyPresented (ArithmeticStabilizers.integralParabolic side)] :
    FiniteDimensional ℂ (BoundaryCoordinates degree character) := by
  let (side : Side) (orbit : ArithmeticCohomology.flagOrbits side) :=
    stabilizer_H2_finiteDimensional degree character side orbit
  exact FiniteFlagOrbits.boundary_finiteDimensional_of_stabilizers degree character

end TernaryPeriodPolynomials.BoundaryFiniteness.ParabolicFiniteness
