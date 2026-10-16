module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.LineInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.PlaneInvariance
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Main
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Orientation
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Nonvanishing
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Descent
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.Final
public import TernaryPeriodPolynomials.BoundaryComparison.Stokes.LevelN

@[expose] public section


/-!
# Frame invariance of the canonical face pairing and the literal Stokes lemma at `Γ(M)`, `6 ∣ M`

Paper: `ar:eq:facepair` and Lemma `ar:lem:stokes`.

* `TwistEquiv`, `facePairingCan_twist`: a frame change `h ↦ q h γ` of a face is a twisted isomorphism of the split extensions `ℤ² → Γ_h → Γ(N)` (conjugation of the middle group, radical map `φ_q`, Levi map conjugation by `A ∈ GL₂(ℤ)`),
  and the canonical pairing changes by `det φ · det A`: the Koszul sign of the radical and the cup-form sign of the modular curve (orientation reversal of the Farey tree for `det A = -1`).
* `lineFrame_sign`, `planeFrame_sign`: `det φ_q · det A = a² = 1` for the frames of a face.
* `canAt_transport`, `canAtP_transport`: the canonical pairing of mixed classes at the frame `q h γ` equals the one at `h`, for arbitrary coefficient modules.
* `frameInvarianceLine`, `frameInvariancePlane`: the Props `FrameInvarianceLine/Plane` (Step 1b) for the global classes `E_n`, `E_n^*` of `Γ(M)` with zero flag restrictions.
* `stokes_literal_level`: `ε_P ∑_P ⟨r_P a, r_P b⟩_P + ε_Q ∑_Q ⟨r_Q a, r_Q b⟩_Q = 0` for `6 ∣ M`, with the canonical pairings `canAtClassP`, `canAtClass`, from Step 2 (`OrbitIdentLine/Plane`) as a hypothesis; Step 2 is proved for all `6 ∣ M` (`step2_of_dvd`), so the lemma is unconditional: see `stokes_gammaN_literal_uncond` below.
* `step2_of_dvd`, `stokes_gammaN_literal_uncond` (from the `orbitIdentLine` and the `orbitIdentPlane`): Step 2 at every level `M` with `6 ∣ M`, and the literal Stokes lemma at `Γ(N)` for every `N ≥ 3`, with no further hypothesis.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.FrameInvariance

export TernaryPeriodPolynomials.Argument.FrameInvariance
  (TwistEquiv radXi radXi_levi h1_eq_of_twist edge_kerMapX radPairing_xi facePairingCan_twist CuspConjNat cuspConjNat
    head_smul_neg tail_smul_neg integ_comp_neg sum_tri_normalizer lineFrameEquiv planeFrameEquiv lineFrame_sign
    planeFrame_sign canAt_transport canAtP_transport res_h2Map_inner frameInvarianceLine frameInvariancePlane)

export TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
  (planeFaceOrientationSign lineFaceOrientationSign stokes_literal_level stokes_literal_level_of StokesGammaNLiteral
    stokesGammaNLiteral_of_six_dvd RestrictionIdent stokesGammaNLiteral_of_restriction restrictionIdent stokes_gammaN_literal
    step2_of_dvd stokes_gammaN_literal_uncond)

export TernaryPeriodPolynomials.Argument
  (line_internal_characters plane_internal_characters orientation_signs_forced exists_nonzero_line_sum orientation_signs_forced')

end TernaryPeriodPolynomials.Argument.Statements.FrameInvariance
