module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.PositiveDegree
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.LineClassesVanishZero

@[expose] public section


/-! Target: the perfect face pairing `ar:eq:facepair` of Appendix C.2 on the line faces, in the
boundary-building cochain model (see `LemmaC2.lean` for the encoding of `E*`). Mixed cuspidal
face classes are exactly the classes with zero restriction to every complete flag
(`InnerBoundary`), as shown at the end of Appendix C.4.

Proved for every `n`. For `0 < n` it dispatches on parity to the branch lemmas of
`TernaryPeriodPolynomials/Revision/Proofs/FacePairing`: even `n` always has nonzero bad-flag cusp
residue (`GoodLineVacuityEven.cuspRes_line_false_ne_zero_of_even`, Hecke-free) and dispatches to
`EvenBadLineAnchor.face_pairing_perfect_even_badLine`; odd `n` case-splits on which cusp residue of
`b` is nonzero and dispatches to `OddGoodLineAnchor.face_pairing_perfect_odd_goodLine` or
`OddBadLineAnchor.face_pairing_perfect_odd_badLine` (the latter via the proved
`GoodPlanePeriodsRealizedVanishesOnBadProof.goodPlanePeriodsRealizedVanishesOnBad_proof`.

The `n = 0` case is vacuous: every `InnerBoundary` line class `b` at `n = 0` vanishes
(`LineClassesVanishZero.eq_zero_of_innerBoundary_atZero`). Its good-flag cusp residue vanishes
(`GoodLineVacuityZero.cuspRes_line_true_eq_zero_atZero`), so `b` lies in `innerBadLineClasses 0`,
which is trivial: the bad-line mixed class embeds into the degree-`0` binary parabolic `H¹` of the
level group (`InnerArithmeticBinaryZero`, via the degree-`0` radical identification
`ExplicitRadicalBinaryEquivZero`), and that parabolic `H¹` vanishes by the sharp dimension bound
(`BinaryParabolicZero.binaryParabolicH1_zero_eq_bot`). -/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes eq_zero_iff_cuspRes)
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Perfect line pairing (`ar:eq:facepair`, `R = Q`).** Every nonzero mixed cuspidal line
class `b ∈ 𝒞_Q(E)` pairs nontrivially with some mixed cuspidal class of `𝒞_Q(E*)`, represented
by a mixed cuspidal plane class `ξ` of `E` moved to the lines by the involution: for every choice
of representatives and primitives the boundary cup product of `b` with `ξ` is not exact in the
boundary building. -/
theorem face_pairing_perfect (n : ℕ) :
    ∀ b : StratumH2 n trivialCharacter .line, InnerBoundary n trivialCharacter .line b → b ≠ 0 →
    ∃ ξ : StratumH2 n trivialCharacter .plane, InnerBoundary n trivialCharacter .plane ξ ∧
      ∀ z : MaximalCycles n trivialCharacter .line,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b →
      ∀ w : EdgeCochains n trivialCharacter 1,
        (∀ x e, z.val.val x (endpoint .line e) = differentialOneRaw w.val x e) →
      ∀ y : MaximalCycles n trivialCharacter .plane,
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) y = ξ →
      ∀ γ : (Fin 4 → RationalGL3) → Flags .line → ℂ,
        γ ∈ cochains rationalLevel (functionRepresentation scalarTrivial (Flags .line)) 3 →
        (∀ x F, differentialThreeRaw γ x F =
          dualPairing n (z.val.val ![x 0, x 1, x 2] F)
            (y.val.val ![dualInvolution (x 2), dualInvolution (x 3), dualInvolution (x 4)]
              (dualFlag F))) →
        ¬ BoundaryExact (fun x e =>
          dualPairing n (w.val ![x 0, x 1] e)
            (y.val.val ![dualInvolution (x 1), dualInvolution (x 2), dualInvolution (x 3)]
              (dualFlag (endpoint .line e))) - γ x (endpoint .line e)) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- Degree zero: there is no nonzero inner line class (see the module docstring).
    subst hn0
    intro b hinner hb
    exact absurd (eq_zero_of_innerBoundary_atZero hinner) hb
  · exact face_pairing_perfect_pos n hn

end TernaryPeriodPolynomials
