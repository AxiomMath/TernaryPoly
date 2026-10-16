module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineVacuityEven
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.EvenBadLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.OddGoodLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.OddBadLineAnchor
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.PlanePeriodsRealizedVanishesOnBadProof

@[expose] public section


/-!
# The perfect face pairing in positive degree

The dispatch of the face-pairing target for `0 < n` (parity, then which line cusp residue of `b`
is nonzero), as a lemma, so that `line_constant_term_comparison` (which needs `n ≥ 4`) depends only on the
positive-degree branches. The degree-zero case of the target is separate.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes eq_zero_iff_cuspRes)
open TernaryPeriodPolynomials.Argument.FacePairing

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **The perfect face pairing for `0 < n`.** -/
theorem face_pairing_perfect_pos (n : ℕ) (hn : 0 < n) :
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
  intro b inner hb
  rcases Nat.even_or_odd n with heven | hodd
  · exact face_pairing_perfect_even_badLine hn heven inner
      (cuspRes_line_false_ne_zero_of_even hn heven inner hb)
  · by_cases hT : cuspRes n trivialCharacter .line true b = 0
    · have hF : cuspRes n trivialCharacter .line false b ≠ 0 := fun hF0 =>
        hb ((eq_zero_iff_cuspRes .line b).mpr ⟨hT, hF0⟩)
      exact face_pairing_perfect_odd_badLine hn hodd inner hF
        (goodPlanePeriodsRealizedVanishesOnBad_proof n hn hodd)
    · exact face_pairing_perfect_odd_goodLine hn hodd inner hT

end TernaryPeriodPolynomials.Argument.FacePairing
