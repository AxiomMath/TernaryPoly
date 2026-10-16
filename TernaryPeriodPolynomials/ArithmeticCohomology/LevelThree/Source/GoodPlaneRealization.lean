module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneDetect
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.LevelThreeEichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelVector

@[expose] public section


/-!
# Source realization at the good plane from the level-three period

For the trivial character, odd degree and a nonzero pair, `D.cusp` has a nonzero level-three vector
(`spherical_or_levelThree`; a spherical vector is one), hence a nonzero holomorphic level-three
vector of weight `n + 3` (`cohomological_exists_levelThree_classical`), hence the
level-three Eichler datum `E` with `E.α = lteAlpha …` (`exists_levelLeviCocycleData`, CRL-LCD).
The good-plane cell source of `E` has nonzero good-plane coordinate as soon as the level-three
period class of `E` is nonzero (`GoodPlaneDetect`).  The only input is therefore

  `LevelThreePeriodNonvanishing n`: the Eichler cocycle `lteAlpha σ n halfWeight v` of a nonzero
  holomorphic level-three vector `v` of weight `n + 3` has nonzero class on `Γ₁'(3)`
  (injectivity of the level-three period map at the twist `det⁻¹`).

This gives source realization at the good plane for every such `D`, spherical or not
(`sourceRealization_goodPlane_of_periodNonvanishing`), and the summand nonvanishing input of
`Cases.lean` (`levelThreeSummandNonvanishing_goodPlane_of_periodNonvanishing`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.SourceConstruction (gpMu)
open TernaryPeriodPolynomials.MultiplicityOne
open TernaryPeriodPolynomials.Separation

namespace TernaryPeriodPolynomials.LevelThreeSource

variable {n : ℕ}

/-- **Level-three period nonvanishing in degree `n`.**  The Eichler cocycle of a nonzero
holomorphic level-three vector of weight `n + 3` is not a crossed coboundary on `Γ₁'(3)`. -/
def LevelThreePeriodNonvanishing (n : ℕ) : Prop :=
  ∀ (σ : CuspidalRepresentation), Cohomological σ n → ∀ (halfWeight : ℤ),
    2 * halfWeight = -((n : ℤ) + 3) → ∀ v ∈ levelThreeClassicalVectors σ halfWeight, v ≠ 0 →
      ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
        lteAlpha σ n halfWeight v.val (gpMu m) 1 = levelRep (n + 1) (-1) m w - w

/-- A nonzero pair of odd degree gives a level-three datum with nonzero period class. -/
theorem exists_periodClass (hodd : Odd n) (hper : LevelThreePeriodNonvanishing n)
    (D : InducingData n) (hne : associatePair D ≠ ⊥) :
    ∃ E : LevelLeviCocycleData D.cusp n, LevelThreePeriodClass E := by
  have hlev : ∃ v : D.cusp.smooth, v ≠ 0 ∧ v.val ∈ levelThreeValues D.cusp := by
    rcases spherical_or_levelThree D hne with hsph | h
    · obtain ⟨v, hv, hfix⟩ := hsph
      exact ⟨v, hv, fun k _ => hfix k⟩
    · exact h
  obtain ⟨halfWeight, hw, v, hv, hv0⟩ :=
    cohomological_exists_levelThree_classical D.cusp hlev hodd D.cohomological
  obtain ⟨E, hE⟩ := exists_levelLeviCocycleData D.cohomological halfWeight hw v hv hv0
  refine ⟨E, ?_⟩
  unfold LevelThreePeriodClass
  rw [hE]
  exact hper D.cusp D.cohomological halfWeight hw v hv hv0

/-- **Source realization at the good plane** for the trivial character and odd degree, from the
level-three period nonvanishing. -/
theorem sourceRealization_goodPlane_of_periodNonvanishing (hodd : Odd n)
    (hper : LevelThreePeriodNonvanishing n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) (hne : associatePair D ≠ ⊥) :
    SourceRealization D hecke hhecke .plane true :=
  sourceRealization_goodPlane_of_period D hecke hhecke hχ hodd.pos
    fun _ => exists_periodClass hodd hper D hne

/-- **Summand nonvanishing at the good plane** for the trivial character and odd degree, from the
level-three period nonvanishing. -/
theorem levelThreeSummandNonvanishing_goodPlane_of_periodNonvanishing (hodd : Odd n)
    (hper : LevelThreePeriodNonvanishing n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true :=
  levelThreeSummandNonvanishing_goodPlane_of_period D hecke hhecke hχ hodd.pos
    fun hne _ => exists_periodClass hodd hper D hne

/-- **The rank lower bound at the good plane** for the trivial character and odd degree, from
D's local bound, the level-three period nonvanishing and the oldform classes. -/
theorem coordinateRankLowerBound_goodPlane_of_period (hodd : Odd n)
    (hper : LevelThreePeriodNonvanishing n) (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hχ : D.chi = trivialCharacter)
    (hbound : associatePair D ≠ ⊥ →
      LocalUpperBound n D.chi (pairCharacter D hecke hhecke) .plane true 2)
    (hpair : LevelThreeOldformClasses D hecke hhecke .plane true) :
    CoordinateRankLowerBound D hecke hhecke .plane true := fun hne =>
  coordinateRankLowerBound_of_cases D hecke hhecke .plane true hbound
    (sourceRealization_goodPlane_of_periodNonvanishing hodd hper D hecke hhecke hχ hne) hpair hne

end TernaryPeriodPolynomials.LevelThreeSource
