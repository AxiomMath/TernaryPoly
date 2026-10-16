module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodVector
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3EichlerMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3Weight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineLevel3
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Cases

@[expose] public section


/-!
# The bad-line summand of a nonzero pair is nonzero (trivial character, odd degree)

For the trivial character and odd `n`, assume the parity-projected level-three period map
`levelPeriodMap (n + 1) 0 : S_{n+3}(Γ₁(3)) → H¹(Γ₁'(3), Sym^{n+1})` is injective (the Eichler–Shimura
injectivity, an input).  Then a nonzero level-three weight vector `w` of `D.cusp` gives a line source
`lineSource3 D (E w)` with nonzero bad-line Shapiro coordinate
(`badLine_sourceCoordinate_ne_zero_of_weightVector`): if the coordinate vanished, the Levi values
`(n + 1) E_w.α(A) 1` would be a coboundary on `Γ₁'(3)` (`lineSource3_badLine_levi_coboundary`), and
`l3Period_vector_eq_zero` identifies this cocycle with the classical period cocycle of the cusp form of
`w`, which forces `w = 0`.

A nonzero associate pair has a nonzero summand at one of the two sides.  A nonzero line summand is
what is wanted; a nonzero plane summand gives a good-plane level vector
(`planeLevelVector_true_of_summand_ne_bot`), hence a nonzero level-three weight vector and so, by the
above, a nonzero line summand.  This is `LevelThreeSummandNonvanishing D hecke hhecke .line false`
(`levelThreeSummandNonvanishing_badLine_of_trivial`).

Original work by Claude Opus 5.5 (AxiomCode).
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

namespace TernaryPeriodPolynomials.SourceConstruction

variable {n : ℕ}

/-- A source cocycle with nonzero Shapiro coordinate at a cusp of a side shows that the summand of
the side is nonzero. -/
theorem boundarySummand_ne_bot_of_sourceCoordinate_ne_zero (D : InducingData n) (side : Side)
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
theorem l3Family_coboundary_imp_zero (D : InducingData n)
    (hσ : MultiplicityOne.LevelThreeCusp D.cusp) (halfWeight : ℤ)
    (hw : 2 * halfWeight = -((n : ℤ) + 3))
    (hper : Function.Injective (levelPeriodMap (n + 1) 0))
    (v : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)))
    (hv : ∃ w₀ : Binary.HomogeneousPoly (n + 1), ∀ A : binaryArithmeticLevel,
      ((n + 1 : ℕ) : ℂ) •
          (l3FamilyData D hσ halfWeight hw (AnalyticClasses.continuousStages D) v).α
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 =
        binaryArithmeticRepresentation n A w₀ - w₀) :
    v = 0 := by
  apply Subtype.ext
  exact l3Period_vector_eq_zero (l3FamilyInput D hσ halfWeight hw v)
    (AnalyticClasses.continuousStages D) hper hv

/-- **A nonzero level-three weight vector has a line source with nonzero bad-line coordinate**,
given the injectivity of the parity-projected level-three period map. -/
theorem badLine_sourceCoordinate_ne_zero_of_weightVector (D : InducingData n)
    (hchi : D.chi = trivialCharacter) (hodd : Odd n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0))
    (w : levelThreeWeightVectors D.cusp (sourceWeight n)) (hw : w ≠ 0) :
    ∃ c : sourceCocycles D .line, sourceCoordinate D .line false c ≠ 0 := by
  obtain ⟨k, hk⟩ := hodd
  have hn : (n : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  have hhalf : 2 * (-((k : ℤ) + 2)) = -((n : ℤ) + 3) := by omega
  have hσ : MultiplicityOne.LevelThreeCusp D.cusp := levelThreeCusp_of_weightVector w hw
  have pos : 0 < n := by omega
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  have hsrc : ∀ v : levelThreeWeightVectors D.cusp (-((n : ℤ) + 3)),
      IsSourceCocycle D .line (lineSource3 D
        (l3FamilyData D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D) v)) :=
    fun v => lineSource3_isSourceCocycle D _ hχ
  refine ⟨⟨lineSource3 D
    (l3FamilyData D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D) w),
      hsrc w⟩, ?_⟩
  intro h0
  apply hw
  exact lineSource3_badLine_coordinate_eq_zero_imp D hchi pos
    (l3FamilyData D hσ (-((k : ℤ) + 2)) hhalf (AnalyticClasses.continuousStages D))
    (fun v hv => l3Family_coboundary_imp_zero D hσ (-((k : ℤ) + 2)) hhalf hper v hv) hsrc w h0

/-- **The line summand of a nonzero pair is nonzero** (trivial character, odd degree, injective
level-three period map). -/
theorem levelThreeSummandNonvanishing_badLine_of_period (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hchi : D.chi = trivialCharacter) (hodd : Odd n)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeSummandNonvanishing D hecke hhecke .line false := by
  intro hne _
  obtain ⟨side, good, c, hc⟩ := exists_sourceCoordinate_ne_zero D hne
  have hsum : boundarySummand D side ≠ ⊥ :=
    boundarySummand_ne_bot_of_sourceCoordinate_ne_zero D side good c hc
  cases side with
  | line => exact hsum
  | plane =>
    have hlev : PlaneLevelVector D.cusp true := planeLevelVector_true_of_summand_ne_bot D hsum
    have hW := levelThreeWeightVectors_ne_bot_of_planeLevelVector hodd D hlev
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hw : (⟨x, hx⟩ : levelThreeWeightVectors D.cusp (sourceWeight n)) ≠ 0 :=
      fun h => hx0 (congrArg Subtype.val h)
    obtain ⟨c', hc'⟩ := badLine_sourceCoordinate_ne_zero_of_weightVector D hchi hodd hper
      ⟨x, hx⟩ hw
    exact boundarySummand_ne_bot_of_sourceCoordinate_ne_zero D .line false c' hc'

/-- **Summand nonvanishing at the bad line** (trivial character, odd degree).  The hypothesis
`¬ SphericalCusp D.cusp` of the non-spherical case is not needed: the argument covers every `D`. -/
theorem levelThreeSummandNonvanishing_badLine_of_trivial (D : InducingData n)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hchi : D.chi = trivialCharacter) (hodd : Odd n) (_hns : ¬ SphericalCusp D.cusp)
    (hper : Function.Injective (levelPeriodMap (n + 1) 0)) :
    LevelThreeSummandNonvanishing D hecke hhecke .line false :=
  levelThreeSummandNonvanishing_badLine_of_period D hecke hhecke hchi hodd hper

end TernaryPeriodPolynomials.SourceConstruction

end
