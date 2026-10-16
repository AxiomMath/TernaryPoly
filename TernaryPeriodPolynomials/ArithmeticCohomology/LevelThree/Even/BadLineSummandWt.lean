module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPeriodVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineLevel3
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs

@[expose] public section


/-!
# The bad-line summand of a nonzero pair is nonzero (trivial character, every degree)

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twin of `BadLineSummand` without the parity hypothesis on `n`: with the integer rotation weight
`wt = -(n + 3)`, the explicit Eichler family `l3FamilyDataWt` exists for every degree.  For the trivial
character, assume the parity-projected level-three period map `levelPeriodMap (n + 1) 0` is injective
(an input).  Then a nonzero level-three weight vector `w` of `D.cusp` gives a line source
`lineSource3 D (E w)` with nonzero bad-line Shapiro coordinate
(`badLine_sourceCoordinate_ne_zero_of_weightVectorWt`), and a nonzero pair has a nonzero line summand
(`levelThreeSummandNonvanishing_badLine_of_periodWt`).  For even `n` this is
`levelThreeSummandNonvanishing_badLine_of_even`.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SpectralSeparation
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight LevelThreeSummandNonvanishing)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity (levelPeriodMap)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (binaryArithmeticLevel binaryArithmeticRepresentation)
open TernaryPeriodPolynomials.SourceConstruction
  (lineSource3 lineSource3_isSourceCocycle lineSource3_badLine_coordinate_eq_zero_imp
    levelThreeCusp_of_weightVector)

namespace TernaryPeriodPolynomials.EvenLevelThree

variable {n : ℕ}

/-- A source cocycle with nonzero Shapiro coordinate at a cusp of a side shows that the summand of
the side is nonzero. -/
theorem boundarySummand_ne_bot_of_sourceCoordinate_ne_zeroWt (D : InducingData n) (side : Side)
    (good : Bool) (c : sourceCocycles D side) (hc : sourceCoordinate D side good c ≠ 0) :
    boundarySummand D side ≠ ⊥ := by
  intro hbot
  apply hc
  have hmem : sourceClass D side c ∈ boundarySummand D side := by
    rw [← sourceClass_range D side]
    exact LinearMap.mem_range_self _ c
  rw [hbot, Submodule.mem_bot] at hmem
  rw [sourceCoordinate_apply, hmem, map_zero]

/-- **The vanishing of the Levi period class of a level-three weight vector** (explicit Eichler
family) forces the vector to vanish, given the injectivity of the parity-projected level-three
period map. -/
theorem l3Family_coboundary_imp_zeroWt (D : InducingData n)
    (hσ : MultiplicityOne.LevelThreeCusp D.cusp) (wt : ℤ)
    (hw : wt = -((n : ℤ) + 3))
    (hper : Function.Injective (levelPeriodMap (n + 1) 0))
    (v : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)))
    (hv : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) •
          (l3FamilyDataWt D hσ wt hw (AnalyticClasses.continuousStages D) v).α
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) :
    v = 0 := by
  apply Subtype.ext
  exact l3Period_vector_eq_zeroWt (l3FamilyInputWt D hσ wt hw v)
    (AnalyticClasses.continuousStages D) hper hv

/-- **A nonzero level-three weight vector has a line source with nonzero bad-line coordinate**,
given the injectivity of the parity-projected level-three period map; no parity of `n` is
assumed. -/
theorem badLine_sourceCoordinate_ne_zero_of_weightVectorWt (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hn : 0 < n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0))
    (w : levelThreeWeightVectors D.cusp (sourceWeight n)) (hw : w ≠ 0) :
    ∃ c : sourceCocycles D .line, sourceCoordinate D .line false c ≠ 0 := by
  have hσ : MultiplicityOne.LevelThreeCusp D.cusp := levelThreeCusp_of_weightVector w hw
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  have hsrc : ∀ v : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)),
      IsSourceCocycle D .line (lineSource3 D
        (l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D) v)) :=
    fun v => lineSource3_isSourceCocycle D _ hχ
  refine ⟨⟨lineSource3 D
    (l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D) w),
      hsrc w⟩, ?_⟩
  intro h0
  apply hw
  exact lineSource3_badLine_coordinate_eq_zero_imp D hchi hn
    (l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D))
    (fun v hv => l3Family_coboundary_imp_zeroWt D hσ (-((n : ℤ) + 3)) rfl hper v hv) hsrc w h0

/-- **The line summand of a nonzero pair is nonzero** (trivial character, any positive degree,
injective level-three period map). -/
theorem levelThreeSummandNonvanishing_badLine_of_periodWt (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hchi : D.chi = trivialCharacter) (hn : 0 < n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeSummandNonvanishing D hecke hhecke .line false := by
  intro hne _
  obtain ⟨side, good, c, hc⟩ := exists_sourceCoordinate_ne_zero D hne
  have hsum : boundarySummand D side ≠ ⊥ :=
    boundarySummand_ne_bot_of_sourceCoordinate_ne_zeroWt D side good c hc
  cases side with
  | line => exact hsum
  | plane =>
    have hlev : PlaneLevelVector D.cusp true := planeLevelVector_true_of_summand_ne_bot D hsum
    have hW := levelThreeWeightVectors_ne_bot_of_levelVectorWt D
      ((MultiplicityOne.planeLevelVector_true_iff D.cusp).mp hlev)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hw : (⟨x, hx⟩ : levelThreeWeightVectors D.cusp (sourceWeight n)) ≠ 0 :=
      fun h => hx0 (congrArg Subtype.val h)
    obtain ⟨c', hc'⟩ := badLine_sourceCoordinate_ne_zero_of_weightVectorWt D hchi hn hper
      ⟨x, hx⟩ hw
    exact boundarySummand_ne_bot_of_sourceCoordinate_ne_zeroWt D .line false c' hc'

/-- **Summand nonvanishing at the bad line for even degree** (trivial character, injective
level-three period map). -/
theorem levelThreeSummandNonvanishing_badLine_of_even (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hn : 3 ≤ n) (_heven : Even n) (hchi : D.chi = trivialCharacter)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeSummandNonvanishing D hecke hhecke .line false :=
  levelThreeSummandNonvanishing_badLine_of_periodWt D hecke hhecke hchi (by omega) hper

end TernaryPeriodPolynomials.EvenLevelThree

end
