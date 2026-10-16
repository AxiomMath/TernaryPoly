module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryFiniteness.OrbitCohomology
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.BoundaryFiniteness.ArithmeticCohomology

noncomputable section

theorem homogeneous_finiteDimensional (arity degree : ℕ) :
    FiniteDimensional ℂ (MvPolynomial.homogeneousSubmodule (Fin arity) ℂ degree) := by
  have bounded : MvPolynomial.homogeneousSubmodule (Fin arity) ℂ degree ≤
      MvPolynomial.restrictTotalDegree (Fin arity) ℂ degree := by
    intro polynomial homogeneous
    exact (MvPolynomial.mem_restrictTotalDegree (Fin arity) degree polynomial).mpr homogeneous.totalDegree_le
  exact FiniteDimensional.of_injective (Submodule.inclusion bounded) (Submodule.inclusion_injective bounded)

def flagOrbits (side : Side) := OrbitCohomology.Orbits (G := rationalLevel) (Flags side)

def flagStabilizer (side : Side) (orbit : flagOrbits side) : Subgroup rationalLevel :=
  OrbitCohomology.stabilizer (Flags side) orbit

def stabilizerRepresentation (degree : ℕ) (character : RankOneCharacter) (side : Side)
    (orbit : flagOrbits side) : Rep ℂ (flagStabilizer side orbit) :=
  Rep.of (((rationalCoefficientComponent degree character).comp rationalLevel.subtype).comp
    (flagStabilizer side orbit).subtype)

instance stabilizerRepresentation_finiteDimensional (degree : ℕ) (character : RankOneCharacter)
    (side : Side) (orbit : flagOrbits side) :
    FiniteDimensional ℂ (stabilizerRepresentation degree character side orbit) :=
  homogeneous_finiteDimensional 3 degree

def stratumEquiv (degree : ℕ) (character : RankOneCharacter) (side : Side) :
    StratumH2 degree character side ≃ₗ[ℂ]
      ∀ orbit : flagOrbits side, groupCohomology.H2 (stabilizerRepresentation degree character side orbit) :=
  (AmbientResolution.cohomologyEquiv rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree character) side)).trans
      (OrbitCohomology.cohomologyEquiv (Flags side)
        ((rationalCoefficientComponent degree character).comp rationalLevel.subtype))

theorem stratum_finiteDimensional (degree : ℕ) (character : RankOneCharacter) (side : Side)
    [Finite (flagOrbits side)]
    [∀ orbit : flagOrbits side,
      FiniteDimensional ℂ (groupCohomology.H2 (stabilizerRepresentation degree character side orbit))] :
    FiniteDimensional ℂ (StratumH2 degree character side) :=
  FiniteDimensional.of_injective (stratumEquiv degree character side).toLinearMap
    (stratumEquiv degree character side).injective

theorem boundary_finiteDimensional (degree : ℕ) (character : RankOneCharacter)
    [∀ side : Side, Finite (flagOrbits side)]
    [∀ (side : Side) (orbit : flagOrbits side),
      FiniteDimensional ℂ (groupCohomology.H2 (stabilizerRepresentation degree character side orbit))] :
    FiniteDimensional ℂ (BoundaryCoordinates degree character) := by
  let := stratum_finiteDimensional degree character .plane
  let := stratum_finiteDimensional degree character .line
  infer_instance

end

end TernaryPeriodPolynomials.BoundaryFiniteness.ArithmeticCohomology
