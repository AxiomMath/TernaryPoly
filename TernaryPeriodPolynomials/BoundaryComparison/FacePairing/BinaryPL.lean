module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLLiteral
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLiteralBridge
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDLiteralBridgeL0
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDEvenPlane

@[expose] public section


/-!
# Export: the Poincare-Lefschetz instance for the binary Levi groups `GL₂(ℤ)` and `Γ₁'(3)` (`ar:eq:facepair`, base factor)

Formalized by Claude Sonnet 5.5.

* `Setup`: compactly supported cohomology `Hc` (relative cocycles `(Z, v)`, `Z(gᵢ) = (gᵢ - 1) vᵢ`, modulo `(g ↦ g u - u, (u,u,u) + f)`),
  the TRUE compact-support map `j` (forget the primitives; kernel = image of `H⁰` of the cusp subgroups, image = the parabolic classes),
  the Poincare-Lefschetz cup pairings `PD : Hc(E) × H¹(E*) → ℂ`, `PDt : H¹(E) × Hc(E*) → ℂ` (minus the transpose for the dual
  system), `hT` (`j'` is the transpose of `j`, the skew-symmetry of the cup product), and the pairing `imagePairing` of the images.
* `imagePairing_eq` (`GL₂(ℤ)`, `Γ₁'(3)`): the pairing of the images IS the library's parabolic cup pairing.
* `imagePairing_*_nondegenerate`: nondegenerate on both sides, from the left parabolic Poincare duality for the system and for its dual.
* `levelOne_dual_is_contragredient`: the dual system is the contragredient twisted by the determinant (the orientation character).
-/

open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

namespace TernaryPeriodPolynomials.Argument.Statements.FacePairingBinaryPL

/-! ### The cusp-relative cohomology, the true compact-support map and the Poincare-Lefschetz pairings (generic) -/

/-- **`j'` is the transpose of `j`**: `PD c (j' c') = PDt (j c) c'` (skew-symmetry of the cup product on relative cocycles). -/
alias lefschetz_transpose := BinaryPL.Setup.hT
/-- **The image of the compact-support map `j` is the space of parabolic (cuspidal) classes.** -/
alias lefschetz_range_j := BinaryPL.Setup.range_j
/-- **The kernel of `j`**: a relative class maps to zero iff its crossed homomorphism is a coboundary (the image of `H⁰` of the
cusp subgroups). -/
alias lefschetz_jMap_eq_zero_iff := BinaryPL.Model.jMap_eq_zero_iff
/-- **The Lefschetz pairing of the images is the library's parabolic cup pairing.** -/
alias lefschetz_imagePairing_eq_parabolicPairing := BinaryPL.Setup.imagePairing_eq_parabolicPairing
/-- **`PDt : H¹(E) × Hc(E*) → ℂ` is nondegenerate on the `H¹(E)` side.** -/
alias lefschetz_PDt_nondegenerate := BinaryPL.Setup.PDt_nondegenerate
/-- **`PD : Hc(E) × H¹(E*) → ℂ` is nondegenerate on the `H¹(E*)` side.** -/
alias lefschetz_PD_nondegenerate := BinaryPL.Setup.PD_nondegenerate
/-- **The annihilator of `Im j'` in `Im j` is zero.** -/
alias lefschetz_imagePairing_left_nondegenerate := BinaryPL.Setup.imagePairing_left_nondegenerate
/-- **The annihilator of `Im j` in `Im j'` is zero.** -/
alias lefschetz_imagePairing_right_nondegenerate := BinaryPL.Setup.imagePairing_right_nondegenerate
/-- **Skew-symmetry of the triple cup form on constrained triples.** -/
alias tripleForm_skew := BinaryPL.tripleForm_skew
/-- **Skew-symmetry of the Poincare-Lefschetz cup formula of two relative cocycles.** -/
alias pdRaw_skew := BinaryPL.pdRaw_skew

/-! ### The literal faces -/

/-- **Level one (good line / identity plane, `n` odd): the Lefschetz pairing of the images of compactly supported cohomology is the
literal parabolic cup pairing.** -/
alias levelOne_imagePairing_eq := BinaryPL.Literal.levelOne_imagePairing_eq
/-- **Level one: the pairing between the images is nondegenerate on both sides.** -/
alias levelOne_imagePairing_nondegenerate := BinaryPL.Literal.levelOne_imagePairing_nondegenerate
/-- **Level one: the dual system is the contragredient twisted by the determinant** (`⟨v, ρ'(g) w⟩ = det(g) ⟨ρ(g⁻¹) v, w⟩`). -/
alias levelOne_dual_is_contragredient := BinaryPL.Literal.levelOne_dual_is_contragredient
/-- **Level three (bad line / good plane, `n` odd): the Lefschetz pairing of the images is the literal parabolic cup pairing.** -/
alias levelThree_imagePairing_eq := BinaryPL.Literal.levelThree_imagePairing_eq
/-- **Level three: the pairing between the images is nondegenerate on both sides.** -/
alias levelThree_imagePairing_nondegenerate := BinaryPL.Literal.levelThree_imagePairing_nondegenerate
/-- **Level three: the dual system is the contragredient twisted by the determinant.** -/
alias levelThree_dual_is_contragredient := BinaryPL.Literal.levelThree_dual_is_contragredient
/-- **Level three, `n` even: the bad-line / good-plane pairing is the Lefschetz pairing of the images composed with the transport.** -/
alias badGoodPairingEven_eq_imagePairing := BinaryPL.Literal.badGoodPairingEven_eq_imagePairing

/-! ### The Kostant coordinates and the plane's own dual system, for the LITERAL contragredient `E*` -/

/-- **Level-one bridge (good line) for the literal contragredient** `E*`, trivial character, `n` odd: same modules `Sym^{n+1}`, `Sym^{n+1} ⊗ det⁻¹`, same constant `-(n+1)!`. -/
alias levelOneBridgeTrivialLiteral := LiteralBridge.levelOneBridgeTrivialLiteral
/-- **Level-one bridge (good line) for the literal contragredient**, character with `χ(-1_∞) = -1`. -/
alias levelOneBridgeOddLiteral := LiteralBridge.levelOneBridgeOddLiteral
/-- **Level-three bridge (bad line), `n` even, for the literal contragredient**: `M = M' = Sym^{n+1}`, constant `(n+1)!/3`. -/
alias levelThreeBridgeBadLiteral := LiteralBridge.levelThreeBridgeBadLiteral
/-- **Level-three bridge (bad line), `n` odd, for the literal contragredient**: constant `-(n+1)!/3`. -/
alias levelThreeBridgeBadOddLiteral := LiteralBridge.levelThreeBridgeBadOddLiteral
/-- **The Kostant pairing of `E` with the literal `E*`** is `-(n+1)!` times the apolar pairing of the coordinates. -/
alias kostant_literal_eq := LiteralBridge.kostant_literal_eq
/-- **Levi equivariance of the literal coordinate** (exact determinant character). -/
alias PsiLit_levi := LiteralBridge.PsiLit_levi
/-- **The even bad-line / good-plane pairing is minus the Lefschetz pairing of the images for the plane's own dual system.** -/
alias badGoodPairingEven_eq_neg_plane := BinaryPL.EvenPlane.badGoodPairingEven_eq_neg_plane
alias badGoodPairingEven_eq_neg_imagePairing := BinaryPL.EvenPlane.badGoodPairingEven_eq_neg_imagePairing
/-- **The plane's pairing with the cusp-exchanged plane system is a twisted pairing.** -/
alias planeTwisted := BinaryPL.EvenPlane.planeTwisted

end TernaryPeriodPolynomials.Argument.Statements.FacePairingBinaryPL
