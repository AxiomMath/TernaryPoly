module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.EvenBad
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.OddGood
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Anchors.OddBad
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.LineVacuityEven
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Good.PlanePeriodsRealizedVanishesOnBadProof

@[expose] public section


/-!
# The face pairing has zero left kernel, for every `n`

For `0 < n` the branch lemmas of `Proofs/FacePairing` produce, for every inner line class `b ≠ 0`,
an anchor (`FacePairingAnchor`) whose trace pairing is nonzero; for `n = 0` there is no nonzero
inner line class. Hence the left kernel of `facePairing n` is zero
(`facePairing_left_nondegenerate`), which is the quantitative form of `face_pairing_perfect`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes eq_zero_iff_cuspRes)
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull.Anchors

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- Every nonzero inner line class has a face-pairing anchor. -/
theorem exists_anchor (n : ℕ) {b : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line b) (hb : b ≠ 0) : FacePairingAnchor b := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    exact absurd (eq_zero_of_innerBoundary_atZero inner) hb
  · rcases Nat.even_or_odd n with heven | hodd
    · exact facePairingAnchor_even_badLine hn heven inner
        (cuspRes_line_false_ne_zero_of_even hn heven inner hb)
    · by_cases hT : cuspRes n trivialCharacter .line true b = 0
      · have hF : cuspRes n trivialCharacter .line false b ≠ 0 := fun hF0 =>
          hb ((eq_zero_iff_cuspRes .line b).mpr ⟨hT, hF0⟩)
        exact facePairingAnchor_odd_badLine hn hodd inner hF
          (goodPlanePeriodsRealizedVanishesOnBad_proof n hn hodd)
      · exact facePairingAnchor_odd_goodLine hn hodd inner hT

/-- **The left kernel of the face pairing is zero.** -/
theorem facePairing_left_nondegenerate (n : ℕ) (b : innerClasses n .line)
    (h : ∀ ξ : innerClasses n .plane, facePairing n b ξ = 0) : b = 0 := by
  by_contra hb0
  have hb : b.val ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
  obtain ⟨ξ, hξ, hdet⟩ := traceDetects_of_anchorData (exists_anchor n b.property hb)
  obtain ⟨z, hz, u, hu⟩ := b.property
  have hξ' := hξ
  obtain ⟨y, hy, _⟩ := hξ'
  have hzero := h ⟨ξ, hξ⟩
  rw [facePairing_apply_eq (b := b) (ξ := ⟨ξ, hξ⟩) hz (fun x e => hu x e) hy] at hzero
  exact hdet z hz u (fun x e => hu x e) y hy hzero

end TernaryPeriodPolynomials.Argument.FacePairingFull
