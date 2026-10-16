module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.BadLineLevel3
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal

@[expose] public section


/-!
# The edge class of the bad-line coordinate of a level-three line source

For a paper datum `D` and a level-three Levi cocycle datum `E`, the bad-line Shapiro
coordinate of the line source `lineSource3 D E` lies in the radical kernel
`badLineLocalRadicalKernel n` of the local cohomology at the bad line, and its image under the edge
map `badLineEdge` is the class of the crossed cocycle `A ↦ (n + 1) • E.α(A) 1` of
`Γ₁'(3)` in `Sym^{n+1}`.  This is the identity underlying the nonvanishing argument
`bd_classOf_ne_zero`, extracted from its contradiction.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers (ambientCocycleToGroup)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag)
open TernaryPeriodPolynomials.LevelThree.BadLineCoordinates (ΛB)
open TernaryPeriodPolynomials.LevelThree.BadLineTransitions (Ux Lm)
open TernaryPeriodPolynomials.LevelThree.BadLineModel
  (wc eAz eAz_val wedge_of_pair semidirect_eq_model)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
  (badLineLocalRadicalKernel)
open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge levi_orig)
open TernaryPeriodPolynomials.Separation (sourceCoordinate)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
  (sourceCocycles evaluatedSource evaluatedSource_realizes)
open TernaryPeriodPolynomials.SourceConstruction
  (LineLeviCocycleData3 lineSource3 bdA3 bdA3_Lm bdA3_one bdA3_radical bd3_represents bdL
    bdL_radical bd_relative bd_edge_value bdPair bdPair_wedge bdAρ BadCupRepresents
    BadLeviRadical BadRadicalLaw)

namespace TernaryPeriodPolynomials.Automorphic.Period.EdgeIdentity

variable {n : ℕ}

/-- **The edge class of a relative cocycle of `ΛB`.**  The class of a relative cocycle lies in the
radical kernel of the local cohomology at the bad line, and its edge is the class of the Levi
cocycle `eAz` of the associated radical-zero cycle. -/
theorem badLineEdge_classOf (hn : 0 < n) (C : cocycles ΛB (ρn n))
    (hrel : ∀ x y : ℤ × ℤ, ambientCocycleToGroup ΛB (ρn n) C (Ux x, Ux y) = 0) :
    ∃ hy : classOf ΛB (ρn n) C ∈ badLineLocalRadicalKernel n,
      badLineEdge n hn ⟨classOf ΛB (ρn n) C, hy⟩ =
        (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ
          (eAz n hn (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel)) := by
  have hmodel : standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) =
      (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel).val :=
    (standardBadLineInhomogeneousH2Equiv_classOf n C).trans
      (congrArg (inhomogeneousBoundaries (standardBadLineRepresentation n)).mkQ
        (semidirect_eq_model n C))
  have hy : classOf ΛB (ρn n) C ∈ badLineLocalRadicalKernel n := by
    have h : standardBadLineInhomogeneousH2Equiv n (classOf ΛB (ρn n) C) ∈
        LinearMap.ker (radicalRestrictionH2 integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)) := by
      rw [hmodel]
      exact radicalZeroH2ToFull_mem_ker integralBadLineSplitting.conjAct
        (standardBadLineRepresentation n)
        ((radicalZeroBoundaries integralBadLineSplitting.conjAct
          (standardBadLineRepresentation n)).mkQ
          (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel))
    exact h
  exact ⟨hy, levi_orig n hn (ambientCocycleToGroup ΛB (ρn n) C) hrel (classOf ΛB (ρn n) C) hy
    hmodel⟩

/-- **The Levi cocycle of a cup cocycle**: for a cocycle `C` of `ΛB` representing the cup product
of the potentials `a` and `l`, the Levi cocycle `eAz` of its radical-zero cycle has values
`(n + 1) • (a (Lm A) - a 1)`. -/
theorem eAz_wc_val (hn : 0 < n) (C : cocycles ΛB (ρn n))
    (a : RationalGL3 → Binary.HomogeneousPoly (n + 1))
    (l : RationalGL3 → (Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n))
    (hrep : BadCupRepresents n C a l) (ha : BadLeviRadical n a) (hl : BadRadicalLaw n l)
    (hrel : ∀ x y : ℤ × ℤ, ambientCocycleToGroup ΛB (ρn n) C (Ux x, Ux y) = 0)
    (A : binaryArithmeticLevel) :
    (eAz n hn (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel)).val A =
      ((n + 1 : ℕ) : ℂ) • (a ((Lm A : ΛB) : RationalGL3) - a 1) := by
  rw [eAz_val]
  exact (wedge_of_pair n hn (ambientCocycleToGroup ΛB (ρn n) C) hrel A
    (bdPair (a ((Lm A : ΛB) : RationalGL3) - a 1))
    (bdAρ n (l ((Lm A : ΛB) : RationalGL3) (a ((Lm A : ΛB) : RationalGL3) - a 1)))
    (fun v => bd_edge_value hrep ha hl A v)).trans (bdPair_wedge _)

/-- **The edge of the bad-line coordinate of a level-three line source.**  The bad-line Shapiro
coordinate of `lineSource3 D E` lies in the radical kernel of the local cohomology at the bad line,
and its edge class is the class of the crossed cocycle `A ↦ (n + 1) • E.α(A) 1` of
`Γ₁'(3)` in `Sym^{n+1}`. -/
theorem lineSource3_badLine_edge (pos : 0 < n) (D : CohomologicalCuspData n)
    (E : LineLeviCocycleData3 D.cusp n)
    (hsrc : IsSourceCocycle D.inducingData .line (lineSource3 D.inducingData E)) :
    ∃ y : badLineLocalRadicalKernel n,
      y.val = sourceCoordinate D.inducingData .line false ⟨lineSource3 D.inducingData E, hsrc⟩ ∧
      ∃ z : crossedCocycles (binaryArithmeticRepresentation n),
        (∀ A : binaryArithmeticLevel, z.val A =
          ((n + 1 : ℕ) : ℂ) • E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) A.val) 1) ∧
        badLineEdge n pos y = (crossedBoundaries (binaryArithmeticRepresentation n)).mkQ z := by
  let src : sourceCocycles D.inducingData .line := ⟨lineSource3 D.inducingData E, hsrc⟩
  have hz := evaluatedSource_realizes D.inducingData .line src
  have hrep := bd3_represents D.inducingData E rfl hz
  let C : cocycles ΛB (ρn n) :=
    fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      (cuspFlag .line false) (evaluatedSource D.inducingData .line src)
  have hrepC : BadCupRepresents n C (bdA3 E) (bdL n) := fun g h => hrep g h
  have ha : BadLeviRadical n (bdA3 E) := bdA3_radical E
  have hl : BadRadicalLaw n (bdL n) := bdL_radical n
  have hrel : ∀ x y : ℤ × ℤ, ambientCocycleToGroup ΛB (ρn n) C (Ux x, Ux y) = 0 :=
    fun x y => bd_relative hrepC ha x y
  obtain ⟨hy, hedge⟩ := badLineEdge_classOf pos C hrel
  refine ⟨⟨classOf ΛB (ρn n) C, hy⟩, rfl,
    eAz n pos (wc n (ambientCocycleToGroup ΛB (ρn n) C) hrel), fun A => ?_, hedge⟩
  have h := eAz_wc_val pos C (bdA3 E) (bdL n) hrepC ha hl hrel A
  rw [bdA3_Lm, bdA3_one, sub_zero] at h
  exact h

end TernaryPeriodPolynomials.Automorphic.Period.EdgeIdentity
