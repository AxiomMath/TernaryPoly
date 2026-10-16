module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Bad.LineFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.LeviReduction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineInnerInstance

@[expose] public section


/-!
# Identifying `badLineEdge`'s value with the global inner bad-line companion class
(M4, bad line, step 2a)

Identification phrased directly in terms of an `InnerBoundary` witness: for `coordinate` with an `InnerBoundary` witness and
`cuspRes n trivialCharacter .line false coordinate ∈ badLineLocalRadicalKernel n`, the
`badLineEdge` of that point *is* `innerBadLineArithmeticBinaryMap n hn aBad` for the global
companion class `aBad` (`BadLineInnerInstance.exists_innerBadLineClasses_matching`), and that
value is parabolic (`BadLineInnerInstance.exists_innerBadLineClasses_nonzero_parabolic`'s own
Hecke-free parabolicity half, re-derived here directly from `innerBadLineArithmeticBinaryMap_parabolic`
so this file does not need the nonvanishing hypothesis `hcusp` at all).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M4, bad line, step 2a.** For an `InnerBoundary` line coordinate, the `badLineEdge` of its
bad-line cusp value equals `innerBadLineArithmeticBinaryMap n hn aBad` for the global companion
class `aBad`, which is parabolic — both facts with no Hecke/eigenvalue hypothesis at all. -/
theorem badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (hmem : cuspRes n trivialCharacter .line false coordinate ∈ badLineLocalRadicalKernel n) :
    ∃ aBad : innerBadLineClasses n,
      badLineEdge n hn ⟨cuspRes n trivialCharacter .line false coordinate, hmem⟩ =
        innerBadLineArithmeticBinaryMap n hn aBad ∧
      innerBadLineArithmeticBinaryMap n hn aBad ∈ parabolicCrossedH1 (levelRep (n + 1) 0) := by
  have matching := exists_innerBadLineClasses_matching inner
  obtain ⟨aBad, haBad⟩ := matching
  have hmem' : fixedPointH2 rationalLevel (ρn n) standardBadLine aBad.val ∈
      badLineLocalRadicalKernel n := by rw [haBad]; exact hmem
  have hsub : (⟨cuspRes n trivialCharacter .line false coordinate, hmem⟩ :
        badLineLocalRadicalKernel n) =
      ⟨fixedPointH2 rationalLevel (ρn n) standardBadLine aBad.val, hmem'⟩ :=
    Subtype.ext haBad.symm
  refine ⟨aBad, ?_, ?_⟩
  · rw [hsub]
    have hval : (localToModel n
          ⟨fixedPointH2 rationalLevel (ρn n) standardBadLine aBad.val, hmem'⟩).val =
        (standardBadLineInnerToRadicalKernel n (innerBadLineLocalEquiv n aBad)).val := by
      show standardBadLineInhomogeneousH2Equiv n (fixedPointH2 rationalLevel (ρn n) standardBadLine
          aBad.val) =
        standardBadLineInhomogeneousH2Equiv n (innerBadLineLocalEquiv n aBad).val
      congr 1
    have hkey : localToModel n
        ⟨fixedPointH2 rationalLevel (ρn n) standardBadLine aBad.val, hmem'⟩ =
          standardBadLineInnerToRadicalKernel n (innerBadLineLocalEquiv n aBad) :=
      Subtype.ext hval
    rw [badLineEdge_apply, hkey]
    refine (LinearMap.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
    refine congrArg (binaryLeviH1Equiv n).toLinearMap ?_
    refine (LinearMap.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
    refine congrArg (explicitBinaryMixedH1Equiv n hn).toLinearMap ?_
    exact ((LinearMap.comp_apply _ _ _).trans (LinearMap.comp_apply _ _ _)).symm
  · have h1 := binaryParabolicH1_le n (innerBadLineArithmeticBinaryMap_parabolic n hn aBad)
    exact h1

end TernaryPeriodPolynomials.Argument.FacePairing
