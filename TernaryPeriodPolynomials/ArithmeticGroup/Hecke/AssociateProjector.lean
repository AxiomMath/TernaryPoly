module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.SmallDegree
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.NontrivialChi
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalPlaneSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalLineSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.TrivialCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Good.PlaneFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.LineTwIdentity
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AlgebraProjector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Boundary

@[expose] public section


/-! Proof of the away-three algebra child.

Proved here (AxiomDeep, `Proofs/HeckeCommutativity`): every element of
`awayThreeHeckeAlgebra D hecke` commutes with every pair Hecke operator, so a
spectral projector onto `associatePair D` inside that algebra is the unique
isotypical projection.  Such a spectral projector exists as soon as `associatePair D`
is eigencharacter separated (`Proofs/SpectralSeparation`, AxiomDeep): every vector
sharing all simultaneous generalized away-three eigenvalues with a nonzero vector
of the associate pair lies in the pair.  That separation property (Harder–Raghuram
constituent separation) is proved below from the AxiomCode reductions and their discharged
inputs (LO1, M1, SC, TW, TS, D-GP, BL, CRL, OLD, PI, PL, R3, EV). -/

open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials

theorem associate_projector_away_three_algebra : ∀ n : ℕ, 0 < n → ∀ D : InducingData n,
    ∀ hecke : BoundaryHecke n D.chi, ActualBoundaryHecke n D.chi hecke →
    ∀ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D hecke p →
    p ∈ awayThreeHeckeAlgebra D hecke := by
  intro n _ D hecke hhecke p hp
  -- Constituent separation: the associate pair is a union of generalized eigenspaces.
  have separated : TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
      (awayThreeHeckeAlgebra D hecke) (associatePair D) := by
    -- Degrees `n < 3` are closed (both cuspidal summands vanish; AxiomCode
    -- `Spectral.eigenSeparated_of_small_degree`).
    rcases Nat.lt_or_ge n 3 with small | _large
    · exact TernaryPeriodPolynomials.Spectral.eigenSeparated_of_small_degree small D hecke
    -- Reduced (AxiomCode, Claude Sonnet 5.5) to named inputs:
    -- trivial character via `Separation.eigenSeparated_of_openInputs_trivial`; nontrivial
    -- character via `LevelOneNontrivial.eigenSeparated_of_openInputs_nontrivial` (the pair vanishes
    -- unless the conductor divides three, strong multiplicity one is automatic for `χ ≠ 1`, `MultiplicityOne.sphericalForcedByLocal(Line)_of_nontrivial`, Opus 5.5); the conductor-three plane source construction is
    -- `TwistedSource.sphericalSourceConstruction_of_conductorThree` (Sonnet 5.5).
    -- Level-one local multiplicity one for conductor three: `Twisted.levelOneLocalMultiplicityOne_
    -- of_conductorThree` (Sonnet 5.5); the conductor-three line source construction is
    -- `TwistedSource.sphericalSourceConstructionLine_of_conductorThree`; the level-three
    -- inputs are vacuous for `χ ≠ 1` (`AxiomCodeLevelThreeSource.*_final`, Opus 5.5).
    -- The nontrivial-character branch is therefore closed; the trivial branch uses
    -- `AxiomCodeLevelThreeSource.*_unconditional` (Opus 5.5, with BL, OLD, PI, R3, EV).
    rcases em (D.chi = trivialCharacter) with hχ | hχ
    on_goal 2 =>
      refine TernaryPeriodPolynomials.Spectral.LevelOneNontrivial.eigenSeparated_of_openInputs_nontrivial
        _large D hecke hhecke hχ
        (fun h3 =>
          TernaryPeriodPolynomials.Twisted.levelOneLocalMultiplicityOne_of_conductorThree
            _large D hecke hhecke hχ h3)
        (fun h3 hne =>
          TernaryPeriodPolynomials.TwistedSource.sphericalSourceConstruction_of_conductorThree
            D hχ h3 hne)
        (fun h3 hne =>
          TernaryPeriodPolynomials.TwistedSource.sphericalSourceConstructionLine_of_conductorThree
            D hχ h3 hne)
        (fun _ hne =>
          TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocal_of_nontrivial
            D hχ hecke hhecke hne)
        (fun _ hne =>
          TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocalLine_of_nontrivial
            D hχ hecke hhecke hne)
        (TernaryPeriodPolynomials.LevelThreeSource.localJointFinite_goodPlane_final D hecke hhecke (fun h => absurd h hχ))
        (TernaryPeriodPolynomials.LevelThreeSource.localJointFinite_badLine_final D hecke hhecke (fun h => absurd h hχ))
        (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_goodPlane_final D hecke hhecke
          (fun h => absurd h hχ) (fun h => absurd h hχ) (fun h => absurd h hχ) (fun h => absurd h hχ))
        (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_badLine_final D hecke hhecke
          (fun h => absurd h hχ) (fun h => absurd h hχ) (fun h => absurd h hχ) (fun h => absurd h hχ))
    on_goal 1 =>
      refine TernaryPeriodPolynomials.Separation.eigenSeparated_of_openInputs_trivial
        _large D hχ hecke hhecke
          (fun _ _ => TernaryPeriodPolynomials.SourceConstruction.sphericalSourceConstruction_of_trivial D hχ)
          (fun _ _ => TernaryPeriodPolynomials.SourceConstruction.sphericalSourceConstructionLine_of_trivial D hχ)
          (fun _ hne => TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocal _large D hecke hhecke hne)
          (fun _ hne => TernaryPeriodPolynomials.MultiplicityOne.sphericalForcedByLocalLine _large D hecke hhecke hne)
          (TernaryPeriodPolynomials.LevelThree.GoodPlaneFinite.localJointFinite_plane_true_of_trivial (by omega) D hecke hhecke hχ)
          (TernaryPeriodPolynomials.LevelThree.BadLineFinite.localJointFinite_badLine_of_trivial _large D hecke hhecke hχ)
          (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_goodPlane_unconditional _large D hχ hecke hhecke)
          (TernaryPeriodPolynomials.LevelThreeSource.coordinateRankLowerBound_badLine_unconditional _large D hχ hecke hhecke)
  exact TernaryPeriodPolynomials.SpectralSeparation.mem_awayThree_of_eigenSeparated D hecke
    hhecke separated p hp

end TernaryPeriodPolynomials
