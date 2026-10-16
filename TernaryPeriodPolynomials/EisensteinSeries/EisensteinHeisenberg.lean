module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisFlagEmbed
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Heisenberg.HeisIso

@[expose] public section


/-!
# Export: averaging over the Heisenberg radical of a flag (Nomizu-Kasuya) and the restriction class at a flag

Formalized by Claude Sonnet 5.5.

All statements are proved without Fourier series and without a spectral sequence; the proofs are in `Proofs/EisensteinClass/Heisenberg/`.

## The Chevalley-Eilenberg complex of the Heisenberg algebra with unipotent coefficients
* `CE E = Fin 8 → E` is `Λ•(ℝ³)* ⊗ E` (`ε_k`, `ι_k` integer matrices); for a unipotent module `ρ` (`HeisMod`) the constant differential is `𝔇 = Σ ε_k ρ_k - ε₀ ε₁ ι₂` (`ceD0`), and
  `D = Σ_k ε_k X_k + 𝔇` on smooth cochains `ℝ³ → CE E` squares to zero (`Dop_Dop`).

## The Nomizu-Kasuya theorem for the Heisenberg nilmanifold
* `heis_nomizu_ce`: every `D`-closed smooth cochain `u` periodic for the lattice with generators `(ax, 0, 0)`, `(0, ay, 0)`, `(0, 0, az)` (left translations) is cohomologous in the periodic complex
  to its constant Haar average: `u - heisAv u = D η` with `η` periodic and smooth, and `𝔇 (heisAv u) = 0`.
* `heisAv_Dop`: `Av` is a cochain map; `heisAv_const`: `Av ∘ ι = I`; `heis_inclusion_injective`.  Hence `ι` is an isomorphism on cohomology with inverse induced by `Av`.

## Coefficient transport and the flag group
* `HeisRep`: a smooth unipotent representation of the Heisenberg group (`gauge`: `ρ(p)⁻¹ s(p)`); `HeisRep.heisMod` derives `[ρ₀, ρ₁] = ρ₂` central, nilpotent, from it.
* `frame_curl`, `frame_div`: in the gauge-trivialized left-invariant frame, the exterior derivative of `E`-valued forms is the Chevalley-Eilenberg differential `D = d + ρ(θ) ∧`.
* `polyRep_heisRep`: the polynomial coefficient representation `Sym^n ⊗ det⁻¹` (`Coef n`) restricted to the Heisenberg radical is a smooth unipotent representation.
* `flag_gens`, `flag_range`: for the actual flag group `Γ_B = Γ(N) ∩ B(ℤ)` (`flagGroup N`, `N ≥ 3`) the lattice is `(Nℤ)³` in Malcev coordinates and the relation `f(x+N, y, z+Ny) = f` is
  the left translation by the element `[[1,N,0],[0,1,0],[0,0,1]] ∈ Γ_B` (derived from the group).
* `heis_class_av`: for a closed `E`-valued `2`-form on the Heisenberg chart, equivariant for a group acting through left translations by a lattice with these generators, the form with the constant average
  as frame coefficients has the same class in `H²(G, E)` (zig-zag class); `deRhamClass_exact`: the class of `d` of an equivariant `1`-form is `0`.
* `flag_restriction_averaged`: **the averaged pullback along `i_{B,t}` represents the restriction class**: for a closed `Γ`-equivariant `E_n`-valued `2`-form `W` on `Ω` (`InvComponents Γ n`) and
  `Γ_B ≤ Γ`, the restriction of `[W] ∈ H²(Γ, E_n)` to `Γ_B` is the zig-zag class of a closed equivariant form `ωc` on the Heisenberg chart whose gauge-trivialized frame coefficients are the constant
  Haar average of those of `i_{B,t}^* W` (a `𝔇`-cocycle of the Chevalley-Eilenberg complex with coefficients in `E_n`).

## Not proved
* The de Rham theorem for the nilmanifold `Γ_B \ N_B` (identification of `H²(Γ_B, E)` with the cohomology of the periodic complex): the statements here are at the level of the periodic de Rham complex and of
  the zig-zag class map; no use of the identification is needed for the representability statement above.
* The determinant twist is trivial on the radical (`det = 1`), the dual module is not treated separately (any smooth unipotent `HeisRep`, in particular the contragredient, is covered by the abstract theorems).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinHeisenberg

open TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg

alias heis_nomizu := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heis_nomizu
alias heis_nomizu_ce := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heis_nomizu_ce
alias heis_D_squared := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.Dop_Dop
alias heis_av_cochain_map := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heisAv_Dop
alias heis_av_const := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heisAv_const
alias heis_inclusion_injective :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heis_inclusion_injective
alias heis_frame_curl := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.frame_curl
alias heis_frame_div := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.frame_div
alias heis_polyRep_heisRep := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.polyRep_heisRep
alias heis_flag_gens := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.flag_gens
alias heis_flag_range := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.flag_range
alias heis_class_av := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.heis_class_av
alias heis_deRhamClass_exact := TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.deRhamClass_exact
alias flag_restriction_averaged :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.Heisenberg.flag_restriction_averaged

end TernaryPeriodPolynomials.Argument.Statements.EisensteinHeisenberg
