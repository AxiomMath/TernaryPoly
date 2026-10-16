module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadIsoFace
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.MackeyEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.LineIdent
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.PlaneIdent

@[expose] public section


/-!
# Finite-index induction on the radical lattice for the canonical face pairing

Paper: `ar:eq:facepair`; Step 2 of the literal Stokes lemma at `Γ(N)`, radical part (Koszul pairing of radical lattices of index
`m₀² = (M/6)²`).

* `phiC_ind`, `phiC_ind_dual` (cocycle level): for a split sub-extension `Stab ≤ S` with radical `m₀ℤ²` (`Compat`) the Koszul pairing of radical cocycles with values in `Fun(S/Stab, E)` (resp. its literal
  contragredient) is the sum over the Levi cosets `Γ(N)/Γ(M)` of the Koszul pairings of the pulled-back evaluated cocycles.  **The scalar is exactly `1`**: the factor `m₀²` of `altForm_gen`
  (change of lattice, `PhiC` of the induced cocycle on the sublattice) cancels the orbit size `m₀²` of the radical lattice on `S/Stab` (`sum_orbits`, `index_latt`).
* `radPairing_ind`: the same for the Koszul pairing on radical `H¹` classes (the hypothesis `hE` of `cuspidal_pairing_phi`).
* `facePairingCan_ind`: the canonical face pairing of `H¹(N, Fun(S/Stab, E))` is the canonical face pairing of `H¹(N', E)` after the Levi-equivariant comparison, constant `1`.
* `facePairingCan_ind_edge`: the same on the Hochschild-Serre edges of classes with vanishing radical restriction (`kerMapW`: pull-back along `α : E₂ → S` and evaluation at the base point).
* `facePairingCan_iso_edge` (`RadIsoFace`): the canonical face pairing of the edges under an isometric comparison of coefficient modules over the same Levi group, constant `1`.
* `mackey_edge` (`MackeyEdge`): the canonical face pairing at `S` of the orbit components `j a`, `qᵀ b` of classes `a`, `b` at a stabiliser extension equals the canonical face pairing at that extension of their transports `kerMapW a`, `kerMapWD b`.
* `orbit_ident_gen` (`GenIdent`): the orbit identity for arbitrary `K ≤ Γ(6)`, `K' ≤ Γ(M)`, constant exactly `1`; `orbitIdentLine` (`LineIdent`): `OrbitIdentLine M n hM` for the line faces.
* `cuspidal_pairing_phi`: the cup-form normalised cuspidal pairing under a comparison of coefficient modules over `Γ(M) ≤ Γ(N)`, with an arbitrary constant `c`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.RadicalInduction

open TernaryPeriodPolynomials.Argument.RadicalInduction

export TernaryPeriodPolynomials.Argument.RadicalInduction
  (Compat YN WI AS sum_orbits index_latt phiC_ind phiC_ind_dual radPairing_ind facePairingCan_ind facePairingCan_ind_edge
    cuspidal_pairing_phi kerMapW kerMapWD phiRad phiRadD kapDual facePairingCan_iso facePairingCan_iso_edge mackey_edge
    orbit_ident_gen orbitIdentLine orbitIdentPlane plane_hmem plane_hback plane_hinl plane_hspl)

end TernaryPeriodPolynomials.Argument.Statements.RadicalInduction
