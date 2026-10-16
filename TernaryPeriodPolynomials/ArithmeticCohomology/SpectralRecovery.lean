module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.SmallDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalPlaneSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalLineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.TrivialCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinite
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.FiniteRecovery
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Boundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Dichotomy
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.SingleCharacter

@[expose] public section


/-! Proof of the finite spectral recovery child.

Proved here (AxiomDeep):
* `Proofs/SpectralSeparation`: when the associate pair is eigencharacter separated,
  there is a spectral projector inside the away-three algebra. By uniqueness it is
  `p D`, so `p D` lies in the algebra.
* `Proofs/SpectralSeparation/Dichotomy`: two associate pairs that are separated and
  have a single eigencharacter are equal or independent.
* `Proofs/HeckeCommutativity/FiniteRecovery`: the finite recovery then follows by
  elementary linear algebra.

* `Proofs/HeckeEigen/Satake`: `SingleCharacter`. The plane and line eigenvalues of every
  away-from-three Hecke operator agree, by a finite Satake-type comparison over `ℚ`.

Eigencharacter separation, `EigenSeparated` (every vector that shares all simultaneous generalized
away-three eigenvalues with a nonzero vector of the associate pair lies in the pair;
Harder–Raghuram constituent separation), is proved below from the AxiomCode reductions and their
discharged inputs. -/

open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials

theorem cuspidal_finite_spectral_recovery : ∀ n : ℕ, 0 < n →
    ∀ hecke : BoundaryHecke n trivialCharacter, ActualBoundaryHecke n trivialCharacter hecke →
    ∀ p : CohomologicalCuspData n → Module.End ℂ (BoundaryCoordinates n trivialCharacter),
    (∀ D : CohomologicalCuspData n, IsIsotypicalProjection D.inducingData hecke (p D)) →
    ∀ b : BoundaryCoordinates n trivialCharacter, b.2 ∈ automorphicLineSpan n →
    ∃ (m : ℕ) (D : Fin m → CohomologicalCuspData n), ∑ i, (p (D i) b).2 = b.2 := by
  intro n _ hecke hhecke p hp b hb
  -- Single eigencharacter on each associate pair (proved: Satake comparison).
  have single : ∀ D : CohomologicalCuspData n,
      TernaryPeriodPolynomials.SpectralSeparation.SingleCharacter
        (awayThreeHeckeAlgebra D.inducingData hecke) (associatePair D.inducingData) := fun D =>
    TernaryPeriodPolynomials.HeckeEigen.Satake.singleCharacter D.inducingData hecke hhecke
  -- Constituent separation: the associate pair is a union of generalized eigenspaces.
  have separated : ∀ D : CohomologicalCuspData n,
      TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
        (awayThreeHeckeAlgebra D.inducingData hecke) (associatePair D.inducingData) := by
    -- Degrees `n < 3` are closed (both cuspidal summands vanish; AxiomCode
    -- `Spectral.eigenSeparated_of_small_degree`).
    intro D
    rcases Nat.lt_or_ge n 3 with small | _large
    · exact TernaryPeriodPolynomials.Spectral.eigenSeparated_of_small_degree small
        D.inducingData hecke
    -- Reduced (AxiomCode, `Separation.eigenSeparated_of_openInputs_trivial`, Claude Sonnet 5.5) to its named inputs: source construction and strong multiplicity
    -- one at the level-one cusps (strong multiplicity one now proved: `AxiomCodeMultiplicityOne.
    -- sphericalForcedByLocal(Line)`, Claude Opus 5.5 Claude Sonnet 5.5), local
    -- finiteness and the coordinate rank lower bound at the level-three cusps; the identity-plane
    -- source construction is `SourceConstruction.sphericalSourceConstruction_of_trivial`
    --  (Claude Opus 5.5 Claude Sonnet 5.5); the level-three inputs are
    -- `AxiomCodeLevelThreeSource.*_unconditional` (Opus 5.5, with BL, OLD, PI, R3, EV).
    refine TernaryPeriodPolynomials.Separation.eigenSeparated_of_openInputs_trivial
      _large D.inducingData rfl hecke hhecke
        (fun _ _ => TernaryPeriodPolynomials.SourceConstruction.sphericalSourceConstruction_of_trivial D.inducingData rfl)
          (fun _ _ => TernaryPeriodPolynomials.SourceConstruction.sphericalSourceConstructionLine_of_trivial D.inducingData rfl)
        (fun _ hne => TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocal _large D.inducingData hecke hhecke hne)
        (fun _ hne => TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocalLine _large D.inducingData hecke hhecke hne)
        (TernaryPeriodPolynomials.LevelThree.GoodPlaneFinite.localJointFinite_plane_true_of_trivial (by omega) D.inducingData hecke hhecke rfl)
        (TernaryPeriodPolynomials.LevelThree.BadLineFinite.localJointFinite_badLine_of_trivial _large D.inducingData hecke hhecke rfl)
        (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_goodPlane_unconditional _large D.inducingData rfl hecke hhecke)
        (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_badLine_unconditional _large D.inducingData rfl hecke hhecke)
  have spectral : ∀ D : CohomologicalCuspData n,
      TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
        (awayThreeHeckeAlgebra D.inducingData hecke) (associatePair D.inducingData) ∧
      TernaryPeriodPolynomials.SpectralSeparation.SingleCharacter
        (awayThreeHeckeAlgebra D.inducingData hecke) (associatePair D.inducingData) :=
    fun D => ⟨separated D, single D⟩
  have hmem : ∀ D : CohomologicalCuspData n, p D ∈ awayThreeHeckeAlgebra D.inducingData hecke :=
    fun D => TernaryPeriodPolynomials.SpectralSeparation.mem_awayThree_of_eigenSeparated
      D.inducingData hecke hhecke (spectral D).1 (p D) (hp D)
  have hsep : ∀ D D' : CohomologicalCuspData n,
      associatePair D.inducingData ⊓ associatePair D'.inducingData = ⊥ ∨
        associatePair D.inducingData = associatePair D'.inducingData := fun D D' =>
    TernaryPeriodPolynomials.SpectralSeparation.dichotomy_of_separated
      (awayThreeHeckeAlgebra D.inducingData hecke) (spectral D).1 (spectral D').1
      (spectral D).2 (spectral D').2
  exact TernaryPeriodPolynomials.HeckeCommutativity.finite_recovery
    hecke hhecke p hp hmem hsep b hb

end TernaryPeriodPolynomials
