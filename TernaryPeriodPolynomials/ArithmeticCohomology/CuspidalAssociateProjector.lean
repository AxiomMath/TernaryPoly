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
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.AlgebraProjector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Boundary

@[expose] public section


/-! Proof of the cuspidal associate projector child.

`existsUnique_isotypical_of_mem_awayThree` (AxiomDeep, `Proofs/HeckeCommutativity`)
turns a spectral projector inside `awayThreeHeckeAlgebra` into the unique
isotypical projection.  Such a projector exists when the associate pair is
eigencharacter separated (`Proofs/SpectralSeparation`, AxiomDeep).  That separation
property (Harder–Raghuram constituent separation), the same statement as in
`associate_projector_away_three_algebra`, is proved below from the AxiomCode reductions and
their discharged inputs. -/

open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials

theorem cuspidal_associate_projector : ∀ n : ℕ, 0 < n → ∀ D : CohomologicalCuspData n,
    ∀ hecke : BoundaryHecke n trivialCharacter, ActualBoundaryHecke n trivialCharacter hecke →
    ∃ p : Module.End ℂ (BoundaryCoordinates n trivialCharacter),
      IsIsotypicalProjection D.inducingData hecke p ∧
      ∀ p', IsIsotypicalProjection D.inducingData hecke p' → p' = p := by
  intro n _ D hecke hhecke
  -- Constituent separation: the associate pair is a union of generalized eigenspaces.
  have separated : TernaryPeriodPolynomials.SpectralSeparation.EigenSeparated
      (awayThreeHeckeAlgebra D.inducingData hecke) (associatePair D.inducingData) := by
    -- Degrees `n < 3` are closed (both cuspidal summands vanish; AxiomCode
    -- `Spectral.eigenSeparated_of_small_degree`).
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
  exact TernaryPeriodPolynomials.SpectralSeparation.existsUnique_isotypical_of_eigenSeparated
    D.inducingData hecke hhecke separated

end TernaryPeriodPolynomials
