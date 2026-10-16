module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Interfaces
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Period.EdgeIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtPeriodAlpha
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtL3TwMain
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.L3PeriodCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.CutoffLine

@[expose] public section


/-!
# Every classical level-three weight vector has its period class realized

For a cohomological cuspidal datum `D` and a classical level-three vector `w` of rotation weight
`-(n + 3)`, the explicit Eichler family gives a level-three Levi cocycle `E` of `w`.  Its line
source `lineSource3 D E` is a source cocycle whose bad-line coordinate has edge class equal to the
class of `A ↦ (n + 1) • E.α(A) 1` (`EdgeIdentity.lineSource3_badLine_edge`), and `E.α(A) 1` is the
parity-projected period cocycle of the cusp form `g` of `w`.  Hence the edge class is `(n + 1)` times
the parity-projected period class of `g`.  The bad-line cutoff replaces the source class by an
element of the line summand with the same bad-line coordinate and zero good-line coordinate.

* `exists_period_form`: the cusp form `g` of `w` and its period cocycle formula;
* `mkQ_eq_smul_levelPeriodMap`: the class of the scaled period cocycle;
* `memberRealized`: the contract `Contracts.MemberRealized n hn D`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open GeneralEisenstein
open Homogeneous Adelic

noncomputable section

namespace TernaryPeriodPolynomials.Automorphic.Period.MemberRealized

open TernaryPeriodPolynomials.Automorphic.Contracts (wtOf)
open TernaryPeriodPolynomials.Automorphic.DirectRoute
open TernaryPeriodPolynomials.Automorphic.Period.EdgeIdentity
  (lineSource3_badLine_edge)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Separation
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodCocycle
  (S periodCocycle form_holo)
open TernaryPeriodPolynomials.LevelThree.LevelThreePeriodParity
  (levelPeriodMap levelPeriodMap_apply levelPlus)
open TernaryPeriodPolynomials.EvenLevelThree
open TernaryPeriodPolynomials.SourceConstruction
  (L3PeriodFormula LineLeviCocycleData3 l3p_exists_S_cast l3p_levelPlus_eq_alpha
    levelThreeCusp_of_weightVector lineSource3 lineSource3_isSourceCocycle)
open TernaryPeriodPolynomials.LevelThreeSource (levelThreeWeightVectors)
open TernaryPeriodPolynomials.MultiplicityOne (LevelThreeCusp)

/-- The level-three weight vector underlying a classical level-three vector. -/
def classicalToWeight (σ : CuspidalRepresentation) (n : ℕ)
    (w : levelThreeClassicalVectorsWt σ (wtOf n)) :
    levelThreeWeightVectors σ (-((n : ℤ) + 3)) :=
  ⟨w.1, w.2.1, w.2.2.1⟩

/-- Membership in `periodRealized`, unfolded. -/
theorem mem_periodRealized_iff {n : ℕ} {hn : 0 < n} {f : S (n + 1)} :
    f ∈ periodRealized n hn ↔ ∃ b ∈ automorphicLineSpan n,
      cuspRes n trivialCharacter .line true b = 0 ∧
        ∃ y : badLineLocalRadicalKernel n,
          (y.1 : CuspH2 n trivialCharacter .line false) =
              cuspRes n trivialCharacter .line false b ∧
            badLineEdge n hn y = ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 f :=
  Iff.rfl

/-- **The cusp form of a classical vector and its period cocycle.**  The classical form `g` of `w`,
as an element of `S (n + 1)`, has parity-projected period cocycle equal to the values of the Eichler
cocycle of `w` at the identity adele. -/
theorem exists_period_form {n : ℕ} (D : InducingData n) (hσ : LevelThreeCusp D.cusp)
    (w : levelThreeClassicalVectorsWt D.cusp (wtOf n)) :
    ∃ g : S (n + 1),
      (⇑g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt D.cusp (wtOf n) 1 w.1 ∧
        ∀ A : binaryArithmeticLevel,
          (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 g)).val A =
            (l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl (AnalyticClasses.continuousStages D)
              (classicalToWeight D.cusp n w)).α
              (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1 := by
  have negative : wtOf n < 0 := by
    show -((n : ℤ) + 3) < 0
    omega
  have weight : -(wtOf n) = ((n + 1 : ℕ) : ℤ) + 2 := by
    show -(-((n : ℤ) + 3)) = ((n + 1 : ℕ) : ℤ) + 2
    push_cast
    omega
  obtain ⟨g, hg⟩ := l3p_exists_S_cast (n + 1) weight
    (levelThreeFormWt D.cusp (wtOf n) negative w.1 w.2)
  have hf : (g : UpperHalfPlane → ℂ) = cuspScalarWeightedLinearWt D.cusp (wtOf n) 1 w.1 :=
    hg.trans (levelThreeForm_coeWt D.cusp (wtOf n) negative w.1 w.2)
  have hα : L3PeriodFormula (l3FamilyDataWt D hσ (-((n : ℤ) + 3)) rfl
      (AnalyticClasses.continuousStages D) (classicalToWeight D.cusp n w)) ⇑g := fun K =>
    l3p_alpha_one_eq_formulaWt (l3FamilyInputWt D hσ (-((n : ℤ) + 3)) rfl
      (classicalToWeight D.cusp n w)) (AnalyticClasses.continuousStages D) hf
      (form_holo g) K
  exact ⟨g, hf, fun A => l3p_levelPlus_eq_alpha _ g hα A⟩

/-- The class of a crossed cocycle equal to `(n + 1)` times the parity-projected period cocycle of
`g` is `(n + 1)` times the parity-projected period class of `g`. -/
theorem mkQ_eq_smul_levelPeriodMap {n : ℕ} (g : S (n + 1))
    (z : crossedCocycles (levelRep (n + 1) 0))
    (hz : ∀ A : binaryArithmeticLevel,
      z.val A = ((n + 1 : ℕ) : ℂ) • (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 g)).val A) :
    (crossedBoundaries (levelRep (n + 1) 0)).mkQ z =
      ((n + 1 : ℕ) : ℂ) • levelPeriodMap (n + 1) 0 g := by
  have h : z = ((n + 1 : ℕ) : ℂ) • levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 g) := by
    apply Subtype.ext
    funext A
    exact hz A
  rw [levelPeriodMap_apply, h, map_smul]

/-- **Realization from the Levi cocycle.**  If the parity-projected period cocycle of `g` is given by
the values `E.α(A) 1` of a level-three Levi cocycle datum `E` of `D`, then `g` lies in
`periodRealized n hn`: the bad-line coordinate of the line source of `E`, cut off at the good line,
is an element of the automorphic line span with edge class `(n + 1)` times the period class of
`g`. -/
theorem mem_periodRealized_of_link {n : ℕ} (hn : 0 < n) (D : CohomologicalCuspData n) (g : S (n + 1))
    (E : LineLeviCocycleData3 D.cusp n)
    (hlink : ∀ A : binaryArithmeticLevel,
      (levelPlus (n + 1) 0 (periodCocycle (n + 1) 0 g)).val A =
        E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1) :
    g ∈ periodRealized n hn := by
  have hsrc : IsSourceCocycle D.inducingData .line (lineSource3 D.inducingData E) :=
    lineSource3_isSourceCocycle D.inducingData E (fun u => rfl)
  obtain ⟨y, hy, z, hz, hedge⟩ := lineSource3_badLine_edge hn D E hsrc
  have hb0 : sourceClass D.inducingData .line ⟨lineSource3 D.inducingData E, hsrc⟩ ∈
      boundarySummand D.inducingData .line := by
    rw [← sourceClass_range D.inducingData .line]
    exact LinearMap.mem_range_self _ _
  obtain ⟨b, hb, hkeep, hdrop⟩ := exists_cutoff_line D.inducingData false hb0
  refine mem_periodRealized_iff.mpr ⟨b, boundarySummand_le_automorphicLineSpan D hb, hdrop, y,
    hy.trans ((sourceCoordinate_apply D.inducingData .line false _).trans hkeep.symm), ?_⟩
  exact hedge.trans (mkQ_eq_smul_levelPeriodMap g z fun A =>
    (hz A).trans (congrArg (fun x => ((n + 1 : ℕ) : ℂ) • x) (hlink A).symm))

/-- **Every classical level-three weight vector has its period class realized.**  For every
cohomological cuspidal datum `D` and every classical level-three vector `w` of rotation weight
`-(n + 3)`, the cusp form of `w` lies in `periodRealized n hn`. -/
theorem memberRealized (n : ℕ) (hn : 0 < n) (D : CohomologicalCuspData n) :
    Contracts.MemberRealized n hn D := by
  intro w
  by_cases hw : w = 0
  · have h0 : w.1 = 0 := congrArg Subtype.val hw
    exact ⟨0, by simp [h0], Submodule.zero_mem _⟩
  · have hσ : LevelThreeCusp D.cusp := levelThreeCusp_of_weightVector (classicalToWeight D.cusp n w)
      (fun h => hw (Subtype.ext (by simpa [classicalToWeight] using congrArg Subtype.val h)))
    obtain ⟨g, hgf, hlink⟩ := exists_period_form D.inducingData hσ w
    exact ⟨g, hgf, mem_periodRealized_of_link hn D g
      (l3FamilyDataWt D.inducingData hσ (-((n : ℤ) + 3)) rfl
        (AnalyticClasses.continuousStages D.inducingData) (classicalToWeight D.cusp n w))
      hlink⟩

end TernaryPeriodPolynomials.Automorphic.Period.MemberRealized
