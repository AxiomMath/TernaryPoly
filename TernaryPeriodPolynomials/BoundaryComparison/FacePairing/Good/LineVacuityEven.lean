module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.BridgeXNonvanishingOfInnerBoundary
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Identity.PlaneEven

@[expose] public section


/-!
# The good-line cusp residue vanishes unconditionally for `InnerBoundary` classes at even `n`
(Hecke-free)

`LocalUniqueness.lean`'s own `localJoint_goodLine_eq_bot_of_even` shows the Hecke joint eigenspace
`localJoint ...` is trivial at even `n` by: taking `y` in that eigenspace, obtaining `y ∈ ML n` via
the Hecke-dependent step `localJoint_le_ML c hc hy`, then applying `phiL n hn` and the twist-agnostic
vanishing fact `IdentityPlaneEven.arithmeticH1_eq_zero_of_odd (n+1) (Even.add_one heven) 0 _` (valid
because `n` even makes `n + 1` odd, and `arithmeticBinaryRep (n+1) 0`'s underlying `H1` always
vanishes in odd degree, by the central `-1` acting trivially-twisted-by-sign — no Hecke theory
involved in *this* step), and finally `phiL_injective` to conclude `y = 0`.

The *only* Hecke-dependent ingredient in that argument is producing the membership `y ∈ ML n` in the
first place. `BridgeXNonvanishingOfInnerBoundary.cuspRes_mem_ML_of_innerBoundary` already supplies
exactly that membership *unconditionally*, directly from `InnerBoundary`, with no Hecke hypothesis
at all (`fixedPointH2_mem_KL_of_innerBoundary` + `psiL_cuspRes_eq`). Substituting it for the
Hecke-dependent step reruns the rest of the library's own argument verbatim and yields: **every**
`InnerBoundary` line class has zero good-flag (`v = true`) cusp residue when `n` is even — not just
inside the Hecke joint eigenspace.

Combined with `CuspReduction.eq_zero_iff_cuspRes` (`a = 0 ↔ cuspRes true a = 0 ∧ cuspRes false a =
0`), the contrapositive gives: for even `n`, an `InnerBoundary` line class `b ≠ 0` is *forced* to have
nonzero *bad*-flag (`v = false`) cusp residue — the good-line branch of the face-pairing assembly is
never available at even `n`; only the bad-line branch can be.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.IdentityPlaneEven (arithmeticH1_eq_zero_of_odd)

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Good-line cusp-residue vacuity at even `n` (Hecke-free).** For an `InnerBoundary` line class
and even `n`, the good-flag cusp residue is always zero. Hecke-free analogue of
`LocalUniqueness.localJoint_goodLine_eq_bot_of_even`, substituting its Hecke-dependent membership
step by `cuspRes_mem_ML_of_innerBoundary`. -/
theorem cuspRes_line_true_eq_zero_of_even {n : ℕ} (hn : 0 < n) (heven : Even n)
    {b : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line b) :
    cuspRes n trivialCharacter .line true b = 0 := by
  have hyM := cuspRes_mem_ML_of_innerBoundary inner
  have h0 : phiL n hn ⟨cuspRes n trivialCharacter .line true b, hyM⟩ = phiL n hn 0 := by
    rw [map_zero]
    exact arithmeticH1_eq_zero_of_odd (n + 1) (Even.add_one heven) 0 _
  exact congrArg Subtype.val (phiL_injective hn h0)

/-- **Consequence: the bad-flag residue is forced nonzero for a nonzero `InnerBoundary` line class
at even `n` (Hecke-free).** -/
theorem cuspRes_line_false_ne_zero_of_even {n : ℕ} (hn : 0 < n) (heven : Even n)
    {b : StratumH2 n trivialCharacter .line}
    (inner : InnerBoundary n trivialCharacter .line b) (hb : b ≠ 0) :
    cuspRes n trivialCharacter .line false b ≠ 0 := by
  intro hfalse
  exact hb ((eq_zero_iff_cuspRes .line b).mpr
    ⟨cuspRes_line_true_eq_zero_of_even hn heven inner, hfalse⟩)

end TernaryPeriodPolynomials.Argument.FacePairing
