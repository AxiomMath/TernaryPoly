module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GeneratorsBounds
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqBasic
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.GenEqLine
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalPlaneSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial

@[expose] public section


/-!
# The prime eigenspace equals the local joint eigenspace at the identity plane

At the identity plane (the dual plane of the good line `L₁`) the joint generalized eigenspace `J`
of the prime operators `T_p` has dimension at most one (`HeckeGeneratorsBounds`). A line summand
class with nonzero coordinate at `L₁` makes `D.cusp` spherical, hence (spherical source
construction at the identity plane, trivial or odd conductor-three character) some plane summand
class has nonzero coordinate there. A nonzero coordinate image in a space of dimension at most one
is all of it, so `J = L = coordinate image`.

* `localJointGen_eq_localJoint_identityPlane_trivial` (`χ = 1`);
* `localJointGen_eq_localJoint_identityPlane_odd` (odd character of conductor three).

Each has a version from the line coordinate image (`…_of_line`) and one from a line summand class
`b` as in `LocalNondegenerate` at `v = 1` (`…_of_lineRep`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq

open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
open TernaryPeriodPolynomials.BoundaryDuality.HeckeGenerators
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-! ### The identity plane, trivial character -/

/-- **Identity plane, trivial character: the prime eigenspace is the local joint eigenspace**, given
a nonzero line coordinate image at the good line (the dual line cusp). -/
theorem localJointGen_eq_localJoint_identityPlane_trivial_of_line (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hline : coordinateImage D .line true ≠ ⊥) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false =
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false := by
  have hsph : SphericalCusp D.cusp := sphericalCusp_of_coordinateImage_line_ne_bot D hline
  have hcoord : coordinateImage D .plane false ≠ ⊥ :=
    SourceConstruction.sphericalSourceConstruction_of_trivial D hχ hsph
  exact localJointGen_eq_localJoint_of_coordinate
    (localJointGen_eq_coordinateImage_of_ne_bot D hecke hhecke .plane false
      (localUpperBoundGen_identityPlane_pair hn D hχ hecke hhecke hne) hcoord)

/-- **Identity plane, trivial character** (`3 ≤ n`, nonzero pair), from a line summand class `b`
with nonzero coordinate at the representative good line `L₁`, as in `LocalNondegenerate` at
`v = 1`. -/
theorem localJointGen_eq_localJoint_identityPlane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    (hbne : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b ≠ 0) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false =
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false :=
  localJointGen_eq_localJoint_identityPlane_trivial_of_line hn D hχ hecke hhecke hne
    (coordinateImage_line_true_ne_bot_of_lineRep_one hb hbne)

/-! ### The identity plane, odd character of conductor three -/

/-- **Twisted identity plane: the prime eigenspace is the local joint eigenspace**, given a nonzero
line coordinate image at the good line (the dual line cusp). The character is nontrivial; a nonzero
pair forces it to be the odd character of conductor three. -/
theorem localJointGen_eq_localJoint_identityPlane_odd_of_line (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    (hline : coordinateImage D .line true ≠ ⊥) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false =
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false := by
  have h3 := LevelOneNontrivial.conductorThree_of_associatePair_ne_bot D hne
  have hneg := LevelOneNontrivial.chi_realNegOne_eq_neg_one hχ h3
  have hsph : SphericalCusp D.cusp := sphericalCusp_of_coordinateImage_line_ne_bot D hline
  have hcoord : coordinateImage D .plane false ≠ ⊥ :=
    TwistedSource.sphericalSourceConstruction_of_conductorThree D hχ h3 hne hsph
  exact localJointGen_eq_localJoint_of_coordinate
    (localJointGen_eq_coordinateImage_of_ne_bot D hecke hhecke .plane false
      (localUpperBoundGen_identityPlane_pair_twisted hn D h3 hneg hecke hhecke hne) hcoord)

/-- **Twisted identity plane** (`3 ≤ n`, nonzero pair, nontrivial character), from a line summand
class `b` with nonzero coordinate at the representative good line `L₁`, as in `LocalNondegenerate`
at `v = 1`. -/
theorem localJointGen_eq_localJoint_identityPlane_odd (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥)
    {b : StratumH2 n D.chi .line} (hb : b ∈ boundarySummand D .line)
    (hbne : fixedPointH2 rationalLevel (rationalCoefficientComponent n D.chi)
      (traceDataL2.lineRep 1) b ≠ 0) :
    localJointGen n D.chi (pairCharacter D hecke hhecke) .plane false =
      localJoint n D.chi (pairCharacter D hecke hhecke) .plane false :=
  localJointGen_eq_localJoint_identityPlane_odd_of_line hn D hχ hecke hhecke hne
    (coordinateImage_line_true_ne_bot_of_lineRep_one hb hbne)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeGenEq
