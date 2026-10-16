module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.OddGood
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Swap.Comparison

@[expose] public section


/-!
# The cochain face pairings against the literal per-face parabolic pairings

For `n > 0` and inner classes `b` (line), `ξ` (plane) the cochain pairing `⟨b, ξ⟩_Q`
(`facePairing n b ξ`) is a sum of the library's parabolic pairings (`badGoodPairingEven`, `badGoodPairingOdd`,
`LevelOne.parabolicPairing`) evaluated on the dictionary classes `badLineParabolic`, `goodPlaneParabolic`
(level three) and `goodLineParabolic`, `badPlaneParabolic` (level one):

* `n` even (`facePairing_even_literal`):
  `⟨b, ξ⟩_Q = ((n+1)!/3) · badGoodPairingEven (badLineParabolic b) (goodPlaneParabolic ξ)`
  (the level-one block is empty: the good-flag cusp residue of an inner line class vanishes at even `n`);
* `n` odd (`facePairing_odd_literal`):
  `⟨b, ξ⟩_Q = (-(n+1)!/3) · badGoodPairingOdd (badLineParabolic b) (goodPlaneParabolic ξ)
    + (n+1)! · ⟨goodLineParabolic b, badPlaneParabolic ξ⟩_{GL₂(ℤ)}`.

The constants `κ_bl = ±(n+1)!/3` and `κ_gl = (n+1)!` are nonzero (the scalars `c_n` of convention C4, block by
block). By the swap relation `⟨B, A⟩_Q = a ⟨A, B⟩_P`, `a = ±1`, the plane pairing `⟨ξ, b⟩_P` is `a` times
the same expressions (`facePairingP_even_literal`, `facePairingP_odd_literal`).

What is and is not proved. The four dictionary maps are the restriction to a cusp stabilizer (`cuspRes`) followed by the
library's explicit edge maps (`badLineEdge`, `goodPlaneEdge`, `phiL`, `edgeH2`). Nothing in this file says that they are the
paper's identifications of the mixed cuspidal groups with the parabolic cohomology of the faces; only the following is
established, in other files:
* `Literal.Bijective`: the four maps are linear isomorphisms of the inner classes onto the parabolic spaces (a statement about
  these particular maps, not about any comparison with another dictionary);
* `Literal.FaceIdentification`: the bad-line map equals MINUS the Hochschild-Serre map `Face.badLineLocallyInnerEquivParabolic`,
  and the good-plane and identity-plane maps equal the parabolic identifications of `Face/*`, which at the planes are defined
  by the same edge maps (so this is definitional there);
* `Literal.GoodLineIdentification` (which imports this file, so the comparison is not used here): at the good line the map
  `phiL ∘ cuspRes true` is the inverse of the Hochschild-Serre map `Face.parabolicToGoodLine`, with sign `+1`
  (`goodLineParabolic_eq_hs`, `parabolicToGoodLine_goodLineParabolic`).

So the edge-map dictionary is compared with the Hochschild-Serre/Kostant composites at the bad line (sign `-1`) and the good
line (sign `+1`), and, in files that import this one, at the identity plane (`Literal.BadPlaneIdentification`) and the
good plane (`Literal.GoodPlaneIdentification`), both with sign `+1`, each with the library-native presentation of the stabilizer.
(`Face/*` defines its plane parabolic identifications by the edge maps themselves, so `Literal.FaceIdentification`'s
plane equalities are definitional; the genuine plane comparisons are the two files above.) Nothing here claims a geometric
(de Rham, Stokes, orientation) normalization of any of the four maps, and the theorems of this file are statements about the
edge-map dictionary.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Even (badGoodPairingEven)
open TernaryPeriodPolynomials.BoundaryDuality.LocalPairingCaseL0Odd (badGoodPairingOdd)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne
  (parabolicPairing)
open TernaryPeriodPolynomials.Argument.FacePairingFull

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

theorem facePairing_odd_literal_of_reps {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (b : innerClasses n .line) (ξ : innerClasses n .plane)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.val)
    (hw : EdgePrimitive z w)
    (hy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ.val)
    (flat : PlaneEdgeExact y) :
    facePairing n b ξ = (-((n + 1).factorial : ℂ) / 3) *
        badGoodPairingOdd hodd (badLineParabolic hn b) (goodPlaneParabolic hn ξ) +
      ((n + 1).factorial : ℂ) *
        parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
          (goodLineParabolic hn b) (badPlaneParabolic hn hodd ξ) :=
  (facePairing_eq_lineValue_add b ξ z w y hz hw hy).trans
    (congrArg₂ (· + ·) (lineValue_zero_odd hn hodd b ξ z w hz hw y hy flat)
      (lineValue_one_odd hn hodd b ξ z w hz hw y hy))

/-- **Odd `n`: the cochain line pairing is the sum of the two literal parabolic pairings.** -/
theorem facePairing_odd_literal {n : ℕ} (hn : 0 < n) (hodd : Odd n) (b : innerClasses n .line)
    (ξ : innerClasses n .plane) :
    facePairing n b ξ = (-((n + 1).factorial : ℂ) / 3) *
        badGoodPairingOdd hodd (badLineParabolic hn b) (goodPlaneParabolic hn ξ) +
      ((n + 1).factorial : ℂ) *
        parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
          (goodLineParabolic hn b) (badPlaneParabolic hn hodd ξ) :=
  (exists_line_reps b).elim fun _ h1 => h1.elim fun _ h2 =>
    (exists_plane_rep ξ).elim fun _ h3 =>
      facePairing_odd_literal_of_reps hn hodd b ξ _ _ _ h2.1 h2.2 h3.1 h3.2

theorem eq_sign_mul_of_sign_mul {a P Q : ℂ} (ha : a = 1 ∨ a = -1) (h : Q = a * P) :
    P = a * Q := by
  rcases ha with rfl | rfl
  · rw [h, one_mul, one_mul]
  · rw [h]; ring

/-- **The plane face pairing against the literal pairings, even `n`.** There is a sign `a = ±1` with
`⟨A, B⟩_P = a · ((n+1)!/3) · badGoodPairingEven (badLineParabolic B) (goodPlaneParabolic A)` for all inner
classes. -/
theorem facePairingP_even_literal {n : ℕ} (hn : 0 < n) (heven : Even n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (A : innerClasses n .plane) (B : innerClasses n .line),
      Plane.facePairingP n A B = a * ((((n + 1).factorial : ℂ) / 3) *
        badGoodPairingEven heven (badLineParabolic hn B) (goodPlaneParabolic hn A)) :=
  Swap.exists_swap_relation.elim fun a h =>
    ⟨a, h.1, fun A B => (eq_sign_mul_of_sign_mul h.1 (h.2 n A B)).trans
      (congrArg (a * ·) (facePairing_even_literal hn heven B A))⟩

/-- **The plane face pairing against the literal pairings, odd `n`.** -/
theorem facePairingP_odd_literal {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    ∃ a : ℂ, (a = 1 ∨ a = -1) ∧ ∀ (A : innerClasses n .plane) (B : innerClasses n .line),
      Plane.facePairingP n A B = a * ((-((n + 1).factorial : ℂ) / 3) *
          badGoodPairingOdd hodd (badLineParabolic hn B) (goodPlaneParabolic hn A) +
        ((n + 1).factorial : ℂ) *
          parabolicPairing (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
            (goodLineParabolic hn B) (badPlaneParabolic hn hodd A)) :=
  Swap.exists_swap_relation.elim fun a h =>
    ⟨a, h.1, fun A B => (eq_sign_mul_of_sign_mul h.1 (h.2 n A B)).trans
      (congrArg (a * ·) (facePairing_odd_literal hn hodd B A))⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
