module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspFullness
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.Assembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.TrivialCharacter
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.SphericalPlaneSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Odd.Vanish
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwIdentity

@[expose] public section


/-!
# The plane coordinate statements for the trivial character

For the trivial character and `3 ≤ n`, every local joint generalized eigenclass of the pair
character at either plane cusp is the Shapiro coordinate of a plane summand class:
* at the good plane by the finiteness of the local joint eigenspace and the rank lower bound of
  the level-three source construction,
* at the identity plane by the spherical source construction, strong multiplicity one at the
  prime three and local multiplicity one at level one.

So boundary duality on the associate pair for the trivial character only needs local
nondegeneracy at the two line cusps (`associatePairDuality_of_localNondegenerate_trivial`). If
the associate pair is zero the line summand is zero and there is nothing to prove; this happens
whenever the conductor of the character does not divide three. A nontrivial character of
conductor dividing three is odd: then the local cohomology at the bad line vanishes, and only the
good line with its dual identity plane remains, where the coordinate statement holds by the
twisted level-one multiplicity one and the twisted source construction
(`associatePairDuality_of_localNondegenerate`, all characters).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.BoundaryDuality.CoordinateInputs

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace
open TernaryPeriodPolynomials.BoundaryDuality.CuspFullness
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2
open TernaryPeriodPolynomials.Separation

variable {n : ℕ}

/-- **The plane coordinate statements for the trivial character.** -/
theorem coordinateStatement_plane_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) (g : Bool) :
    CoordinateStatement D hecke hhecke .plane g := by
  cases g
  · exact coordinateStatement_plane_false D hecke hhecke hn hne (fun h => absurd hχ h)
      (fun _ _ => SourceConstruction.sphericalSourceConstruction_of_trivial D hχ)
      (fun _ h => MultiplicityOne.sphericalForcedByLocal hn D hecke hhecke h)
  · exact coordinateStatement_of_finite_rank D hecke hhecke .plane true hne
      (LevelThreeSource.localJointFinite_goodPlane hn D hχ hecke hhecke)
      (LevelThreeSource.coordinateRankLowerBound_goodPlane_unconditional hn D hχ hecke
        hhecke)

/-- If the associate pair is zero, boundary duality holds vacuously. -/
theorem associatePairDuality_of_eq_bot (D : InducingData n) (h : associatePair D = ⊥) :
    AssociatePairDuality D := by
  intro b hb hne
  exfalso
  apply hne
  have hmem : ((0 : StratumH2 n D.chi .plane), b) ∈ associatePair D :=
    Submodule.mem_prod.mpr ⟨(boundarySummand D .plane).zero_mem, hb⟩
  rw [h, Submodule.mem_bot] at hmem
  exact congrArg Prod.snd hmem

/-- **Boundary duality on the associate pair for the trivial character from local nondegeneracy
at the two line cusps.** -/
theorem associatePairDuality_of_localNondegenerate_trivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke)
    (nondeg : associatePair D ≠ ⊥ → ∀ v : Fin 2,
      LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke v (good v)) :
    AssociatePairDuality D := by
  by_cases hne : associatePair D = ⊥
  · exact associatePairDuality_of_eq_bot D hne
  · exact associateDuality_of_localNondegenerate traceDataL2 (dualityData n D.chi) hecke hhecke
      good (hdual_L2 n D.chi) hgood_L2 hlines_L2
      (fun v => coordinateStatement_plane_trivial hn D hχ hecke hhecke hne (good v))
      (nondeg hne)

/-- For an odd character there is nothing to prove at the bad line: its local cohomology is zero. -/
theorem cuspDuality_badLine_of_odd (D : InducingData n)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) :
    CuspSeparation.CuspDuality traceDataL2 D (dualityData n D.chi) 0 := by
  intro b _ hb
  exfalso
  apply hb
  have := SourceConstruction.cuspH2_line_false_subsingleton n D.chi hodd
  exact Subsingleton.elim (α := Spectral.CuspReduction.CuspH2 n D.chi .line false) _ _

/-- The identity-plane coordinate statement for a nontrivial character of conductor dividing
three. -/
theorem coordinateStatement_plane_false_nontrivial (hn : 3 ≤ n) (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hne : associatePair D ≠ ⊥) :
    CoordinateStatement D hecke hhecke .plane false := by
  have h3 := Spectral.LevelOneNontrivial.conductorThree_of_associatePair_ne_bot D hne
  exact coordinateStatement_plane_false D hecke hhecke hn hne
    (fun _ => Twisted.levelOneLocalMultiplicityOne_of_conductorThree hn D hecke hhecke hχ
      h3)
    (fun _ h => TwistedSource.sphericalSourceConstruction_of_conductorThree D hχ h3 h)
    (fun _ h => MultiplicityOne.sphericalForcedByLocal hn D hecke hhecke h)

/-- **Boundary duality on the associate pair for every character from local nondegeneracy**: at
both line cusps for the trivial character, and only at the good line `v = 1` for a nontrivial
character. -/
theorem associatePairDuality_of_localNondegenerate (hn : 3 ≤ n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (nondeg : associatePair D ≠ ⊥ → ∀ v : Fin 2, (D.chi = trivialCharacter ∨ v = 1) →
      LocalNondegenerate traceDataL2 D (dualityData n D.chi) hecke hhecke v (good v)) :
    AssociatePairDuality D := by
  by_cases hχ : D.chi = trivialCharacter
  · exact associatePairDuality_of_localNondegenerate_trivial hn D hχ hecke hhecke
      fun hne v => nondeg hne v (Or.inl hχ)
  by_cases hne : associatePair D = ⊥
  · exact associatePairDuality_of_eq_bot D hne
  have h3 := Spectral.LevelOneNontrivial.conductorThree_of_associatePair_ne_bot D hne
  have hodd := Spectral.LevelOneNontrivial.chi_realNegOne_eq_neg_one hχ h3
  refine CuspSeparation.associateDuality_of_cuspDuality traceDataL2 (dualityData n D.chi) good
    (hdual_L2 n D.chi) hgood_L2 hlines_L2 fun v => ?_
  fin_cases v
  · exact cuspDuality_badLine_of_odd D hodd
  · exact cuspDuality_of_localNondegenerate traceDataL2 (dualityData n D.chi) hecke hhecke 1 false
      (coordinateStatement_plane_false_nontrivial hn D hχ hecke hhecke hne)
      (nondeg hne 1 (Or.inr rfl))

end TernaryPeriodPolynomials.BoundaryDuality.CoordinateInputs
