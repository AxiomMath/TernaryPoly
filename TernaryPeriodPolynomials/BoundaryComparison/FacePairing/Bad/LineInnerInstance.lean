module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalReconstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityLevelThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Local.PairingCaseL0EvenBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction

@[expose] public section


/-!
# A global inner bad-line companion class, and its parabolicity and nonvanishing (M1a + M1, bad
line)

Bad-line analogue of `GoodLineEdgeParabolic.lean` + `GoodLineEdgeNonvanishing.lean`, but *not* built
from `BadLineFinal.lean`'s `badLineEdge`. Instead, the entire bad-line
M1/M1a content is reproved directly from Sol's pre-existing `EisensteinGraph.InnerCuspidalArithmetic`
machinery (`innerBadLineClasses`, `innerBadLineArithmeticBinaryMap`), using a *global* companion
class rather than `badLineEdge`'s *local* one.

**Construction.** Given `coordinate : StratumH2 n trivialCharacter .line` with an `InnerBoundary`
witness, `innerBoundary_fixedPointH2_locallyInner` places its bad-line cusp residue
(`cuspRes n trivialCharacter .line false coordinate`, defeq to
`fixedPointH2 rationalLevel (ρn n) standardBadLine coordinate` by unfolding `cuspRes`/`cuspFlag`/`ρn`,
since `cuspFlag .line false` and `standardBadLine` are both *literally* `QuotientGroup.mk (1 :
RationalGL3)`) in `locallyInnerClasses n trivialCharacter .line standardBadLine`;
`exists_innerBadLine_of_local` then produces a *global* `aBad : innerBadLineClasses n` whose own
bad-line cusp residue is literally *equal* to `coordinate`'s (`exists_innerBadLineClasses_matching`).

Since `innerBadLineArithmeticBinaryMap` depends only on `aBad`, not on `coordinate` itself, this is
enough:

* **Nonvanishing.** `aBad`'s nonvanishing (hence its image's, by
  `innerBadLineArithmeticBinaryMap_zero_iff`) follows from `coordinate`'s cusp residue being
  nonzero, transported through the matching equation.
* **Parabolicity.** `aBad`'s image's parabolicity is `innerBadLineArithmeticBinaryMap_parabolic`
  directly (`∈ binaryParabolicH1 n`), bridged into `parabolicCrossedH1 (ParabolicBounds.levelRep
  (n + 1) 0)` (the domain `badLine_left_nondegenerate` needs) via `binaryParabolicH1_le` and the
  *rfl*-level identification `parabolicCrossedH1_binary_eq` (`LocalPairingCaseL0EvenBridge.lean`).
-/

noncomputable section

open GeneralEisenstein Matrix
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **M1, bad line, global companion.** Given an `InnerBoundary` line coordinate, a global
`innerBadLineClasses` element whose bad-line cusp residue matches `coordinate`'s. -/
theorem exists_innerBadLineClasses_matching {n : ℕ}
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate) :
    ∃ aBad : innerBadLineClasses n,
      fixedPointH2 rationalLevel (ρn n) standardBadLine aBad.val =
        cuspRes n trivialCharacter .line false coordinate :=
  exists_innerBadLine_of_local n
    ⟨cuspRes n trivialCharacter .line false coordinate,
      innerBoundary_fixedPointH2_locallyInner inner standardBadLine⟩

/-- **M1a + M1, bad line.** If an `InnerBoundary` line coordinate's bad-line cusp residue is
nonzero, there is a global `innerBadLineClasses` companion `aBad` whose arithmetic binary image is
both nonzero and parabolic (lies in `parabolicCrossedH1 (ParabolicBounds.levelRep (n + 1) 0)`). -/
theorem exists_innerBadLineClasses_nonzero_parabolic {n : ℕ} (hn : 0 < n)
    {coordinate : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line coordinate)
    (hcusp : cuspRes n trivialCharacter .line false coordinate ≠ 0) :
    ∃ aBad : innerBadLineClasses n,
      innerBadLineArithmeticBinaryMap n hn aBad ≠ 0 ∧
      innerBadLineArithmeticBinaryMap n hn aBad ∈
        parabolicCrossedH1 (levelRep (n + 1) 0) := by
  obtain ⟨aBad, haBad⟩ := exists_innerBadLineClasses_matching inner
  refine ⟨aBad, fun h => hcusp ?_, ?_⟩
  · have hz := (innerBadLineArithmeticBinaryMap_zero_iff n hn aBad).mp h
    rw [← haBad, hz]
    exact map_zero _
  · have h1 := binaryParabolicH1_le n (innerBadLineArithmeticBinaryMap_parabolic n hn aBad)
    rwa [parabolicCrossedH1_binary_eq n] at h1

end TernaryPeriodPolynomials.Argument.FacePairing
