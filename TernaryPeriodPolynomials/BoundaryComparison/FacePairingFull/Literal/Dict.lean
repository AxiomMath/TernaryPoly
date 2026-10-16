module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineEdgeInnerIdentification
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Bad.LineEdgeNonvanishing
public import TernaryPeriodPolynomials.BoundaryComparison.GoodPlaneSpan.EdgeParabolicAssembly

@[expose] public section


/-!
# The literal dictionary: inner classes to the parabolic cohomology of the reference faces

For `n > 0` the maps
* `badLineParabolic hn : innerClasses n .line →ₗ parabolicCrossedH1 (levelRep (n+1) 0)`,
  `b ↦ -badLineEdge (cuspRes false b)` (restriction to the bad-line cusp stabilizer, then the Kostant
  edge map to `H¹(Γ₁'(3), Sym^{n+1})`);
* `goodPlaneParabolic hn : innerClasses n .plane →ₗ parabolicCrossedH1 (levelRep (n+1) (-1))`,
  `ξ ↦ goodPlaneEdge (cuspRes true ξ)` (restriction to the good-plane cusp stabilizer, then the Kostant
  edge map to `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`)
are the level-three blocks of the cuspidal dictionary of the face pairing; they land in the parabolic
(cuspidal) classes for every inner class. The literal level-three pairings
(`LocalPairingCaseL0Even.badGoodPairingEven`, `badGoodPairingOdd`) are defined on these spaces.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.LevelThree.BadLineLocal
open TernaryPeriodPolynomials.LevelThree.BadLineFinal (badLineEdge)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge3 (goodPlaneEdge)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1_eq)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

variable (n : ℕ)

/-- The bad-flag Shapiro coordinate of an inner line class, in the radical kernel. -/
def innerLineToRadicalKernel : innerClasses n .line →ₗ[ℂ] badLineLocalRadicalKernel n :=
  ((cuspRes n trivialCharacter .line false).comp (innerClasses n .line).subtype).codRestrict _
    fun b => cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary (n := n) b.property

variable {n}


theorem neg_badLineEdge_mem_parabolic (hn : 0 < n) (b : innerClasses n .line) :
    -(badLineEdge n hn (innerLineToRadicalKernel n b)) ∈
      parabolicCrossedH1 (binaryArithmeticRepresentation n) := by
  obtain ⟨aBad, h1, h2⟩ := badLineEdge_cuspRes_eq_innerBadLineArithmeticBinaryMap hn
    (coordinate := b.val) b.property (cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary b.property)
  have e : badLineEdge n hn (innerLineToRadicalKernel n b) = _ := h1
  rw [e]
  exact neg_mem h2

/-- The bad-line literal dictionary: an inner line class goes to the parabolic class
`-badLineEdge(cuspRes false b)` of `H¹(Γ₁'(3), Sym^{n+1})`. -/
def badLineParabolic (hn : 0 < n) :
    innerClasses n .line →ₗ[ℂ] parabolicCrossedH1 (binaryArithmeticRepresentation n) :=
  (-((badLineEdge n hn).comp (innerLineToRadicalKernel n))).codRestrict _
    (neg_badLineEdge_mem_parabolic hn)

theorem goodPlaneEdge_mem_parabolic (hn : 0 < n) (ξ : innerClasses n .plane) :
    goodPlaneEdge hn (cuspRes n trivialCharacter .plane true ξ.val) ∈
      parabolicCrossedH1 (levelRep (n + 1) (-1)) := by
  have h := TernaryPeriodPolynomials.Argument.GoodPlaneSpan.goodPlaneEdgeParabolic n hn
    ξ.val ξ.property
  rw [← parabolicCrossedH1_eq (levelRep (n + 1) (-1))] at h
  exact h

/-- The good-plane literal dictionary: an inner plane class goes to the parabolic class
`goodPlaneEdge(cuspRes true ξ)` of `H¹(Γ₁'(3), Sym^{n+1} ⊗ det⁻¹)`. -/
def goodPlaneParabolic (hn : 0 < n) :
    innerClasses n .plane →ₗ[ℂ] parabolicCrossedH1 (levelRep (n + 1) (-1)) :=
  ((goodPlaneEdge hn).comp ((cuspRes n trivialCharacter .plane true).comp
    (innerClasses n .plane).subtype)).codRestrict _ (goodPlaneEdge_mem_parabolic hn)

theorem badLineParabolic_coe (hn : 0 < n) (b : innerClasses n .line)
    (c : StratumH2 n trivialCharacter .line) (hc : c = b.val)
    (hinner : InnerBoundary n trivialCharacter .line c) :
    ((badLineParabolic hn b : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
        CrossedH1 (binaryArithmeticRepresentation n)) =
      -badLineEdge n hn ⟨cuspRes n trivialCharacter .line false c,
        cuspRes_false_mem_badLineLocalRadicalKernel_of_innerBoundary hinner⟩ := by
  subst hc
  rfl

theorem goodPlaneParabolic_coe (hn : 0 < n) (ξ : innerClasses n .plane)
    (c : StratumH2 n trivialCharacter .plane) (hc : c = ξ.val) :
    ((goodPlaneParabolic hn ξ : parabolicCrossedH1 (levelRep (n + 1) (-1))) :
        CrossedH1 (levelRep (n + 1) (-1))) =
      goodPlaneEdge hn (cuspRes n trivialCharacter .plane true c) := by
  subst hc
  rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
