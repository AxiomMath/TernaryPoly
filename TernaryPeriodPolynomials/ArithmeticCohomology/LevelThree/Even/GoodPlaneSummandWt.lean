module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.BadLineSummandWt
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneDetect
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3PlaneMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPlanePeriodVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceInduced
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases

@[expose] public section


/-!
# The good-plane summand of a nonzero pair is nonzero (trivial character, every degree)

Formalized by Claude Sonnet 5.5 (AxiomCode).

Good-plane twin of `BadLineSummandWt`.  With the integer rotation weight `wt = -(n + 3)` the
explicit Eichler family `l3PlaneFamilyDataWt` of level-three Levi cocycle data exists for every
degree.  For the trivial character, assume the parity-projected level-three period map
`levelPeriodMap (n + 1) (-1)` is injective (an input).  A nonzero level-three weight vector `w` of
`D.cusp` has a Levi datum `E w` whose period cocycle `m ↦ (E w).α m 1` is not a crossed coboundary
(`l3PlanePeriod_vector_eq_zeroWt`), so the good-plane source `goodPlaneSource D (E w)` has nonzero
good-plane Shapiro coordinate (CRL's `goodPlaneSource_sourceCoordinate_ne_zero`).  A nonzero pair has a
nonzero level-three weight vector, hence a nonzero good-plane summand
(`levelThreeSummandNonvanishing_goodPlane_of_periodWt`); for even `n` this is
`levelThreeSummandNonvanishing_goodPlane_of_even`.
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight LevelThreeSummandNonvanishing goodPlaneSource
    goodPlaneSource_isSourceCocycle_of_trivial LevelLeviCocycleData)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel)
open TernaryPeriodPolynomials.SourceConstruction (levelThreeCusp_of_weightVector)

namespace TernaryPeriodPolynomials.EvenLevelThree

variable {n : ℕ}

/-- **A Levi datum whose period cocycle is not a crossed coboundary gives a good-plane source
cocycle with nonzero good-plane coordinate.** -/
theorem goodPlane_sourceCoordinate_ne_zero_of_levelLevi (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hn : 0 < n) (E : LevelLeviCocycleData D.cusp n)
    (hnc : ¬ ∃ w : Binary.HomogeneousPoly (n + 1), ∀ m : binaryArithmeticLevel,
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m.val) 1 =
        levelRep (n + 1) (-1) m w - w) :
    ∃ c : sourceCocycles D .plane, sourceCoordinate D .plane true c ≠ 0 := by
  exact ⟨_, LevelThreeSource.goodPlaneSource_sourceCoordinate_ne_zero D hchi hn E hnc⟩

/-- **A nonzero level-three weight vector has a good-plane source with nonzero good-plane
coordinate**, given the injectivity of the parity-projected level-three period map; no parity of
`n` is assumed. -/
theorem goodPlane_sourceCoordinate_ne_zero_of_weightVectorWt (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hn : 0 < n)
    (hper : Function.Injective (levelPeriodMap (n + 1) (-1)))
    (w : levelThreeWeightVectors D.cusp (sourceWeight n)) (hw : w ≠ 0) :
    ∃ c : sourceCocycles D .plane, sourceCoordinate D .plane true c ≠ 0 := by
  have hσ : MultiplicityOne.LevelThreeCusp D.cusp := levelThreeCusp_of_weightVector w hw
  exact goodPlane_sourceCoordinate_ne_zero_of_levelLevi D hchi hn
    (l3PlaneFamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D) w)
    (fun hcob => hw (Subtype.ext (l3PlanePeriod_vector_eq_zeroWt
      (l3FamilyInputWt D hσ (-((n : ℤ) + 3)) rfl w) (AnalyticClasses.continuousStages D) hper
      hcob)))

/-- **The plane summand of a nonzero pair is nonzero** (trivial character, any positive degree,
injective level-three period map). -/
theorem levelThreeSummandNonvanishing_goodPlane_of_periodWt (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hchi : D.chi = trivialCharacter) (hn : 0 < n)
    (hper : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true := by
  intro hne _
  have hW : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)) ≠ ⊥ := by
    rcases MultiplicityOne.spherical_or_levelThree D hne with ⟨v, hv, hfix⟩ | h
    · exact levelThreeWeightVectors_ne_bot_of_levelVectorWt D ⟨v, hv, fun k _ => hfix k⟩
    · exact levelThreeWeightVectors_ne_bot_of_levelVectorWt D h
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : (⟨x, hx⟩ : levelThreeWeightVectors D.cusp (sourceWeight n)) ≠ 0 :=
    fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := goodPlane_sourceCoordinate_ne_zero_of_weightVectorWt D hchi hn hper
    ⟨x, hx⟩ hw
  exact boundarySummand_ne_bot_of_sourceCoordinate_ne_zeroWt D .plane true c hc

/-- **Summand nonvanishing at the good plane for even degree** (trivial character, injective
level-three period map). -/
theorem levelThreeSummandNonvanishing_goodPlane_of_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (_heven : Even n) (hchi : D.chi = trivialCharacter)
    (hper : Function.Injective (levelPeriodMap (n + 1) (-1))) :
    LevelThreeSummandNonvanishing D hecke hhecke .plane true :=
  levelThreeSummandNonvanishing_goodPlane_of_periodWt D hecke hhecke hchi (by omega) hper

end TernaryPeriodPolynomials.EvenLevelThree

end
