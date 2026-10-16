module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Flags
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Rational

@[expose] public section


/-!
# Line faces and complete flags of `Γ(N)`: mixed cuspidal groups, Hochschild-Serre edges, exclusion of nonmixed components

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

For `h ∈ SL₃(ℤ)` and `Γ(N)` (`N` arbitrary for the face data; `N ≥ 3` for the identification with the full rational stabilizer):

* `lineFaceRep N h n`: the module `E_n` restricted to the line group `Γ_{Q'} = Γ(N) ∩ h⁻¹ Q(ℤ) h` (`gammaNQAt N h`), a split extension
  of the Levi `Γ₂(N)` by the radical lattice `Nℤ²` (`lineFaceExt`, `lineFaceSplitting`);
* `flagRep N h n`: `E_n` restricted to the flag group `Γ(N) ∩ h⁻¹ B(ℤ) h` (`gammaNBAt N h`); the flags over the line are the cusps of the
  binary Levi, with stabilizers `lineFlagStab N h F` in the line group (`lineFlagStab_one_iff` identifies `F = 1` with the flag group);
* `lineFaceCuspidal N h n`: the literal mixed cuspidal group `𝒞_{Q'}(E)`, its Hochschild-Serre edge `lineFaceEdge` and the injectivity
  `lineFaceEdge_injective`; `lineFaceCuspidalInH2`: its image in `H²(Γ_{Q'}, E_n)`;
* `exists_lineFace_of_rational_line`: every rational line cusp is of this form (the line analogue of `exists_face_of_rational_plane`).

`gammaN_line_faces` bundles the edge injectivity, the transport of the mixed group by conjugation, the identification of the image of the mixed
group with the locally inner classes and the exclusion of nonmixed components (a class vanishing at every flag, or even at one flag for the
radical, lies in the mixed term).
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GammaNFaces

open TernaryPeriodPolynomials.Argument.GammaNFaces TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.SphericalDetection.Helpers

alias line_edge_injective := lineFaceEdge_injective
alias mixed_eq_locally_inner := lineFaceCuspidalInH2_eq_locallyInner
alias nonmixed_excluded := lineFace_mixed_of_flags_vanish
alias flag_restriction_edge := lineFace_flag_restriction_edge
alias rational_line_cusp := exists_lineFace_of_rational_line

/-- **Line faces of `Γ(N)`**: injective Hochschild-Serre edge, conjugation transport of the mixed cuspidal
group, mixed term = locally inner classes, and exclusion of nonmixed components. -/
theorem gammaN_line_faces (N : ℕ) [NeZero N] (h : SL(3, ℤ)) (n : ℕ) :
    Function.Injective (lineFaceEdge N h n) ∧
    Submodule.map (groupCohomology.map (MonoidHom.id (CongruenceSubgroup.Gamma N))
      (lineFaceModIso N h n).hom 1).hom (lineCuspidal N n) = lineFaceCuspidal N h n ∧
    lineFaceCuspidalInH2 N h n = lineLocallyInner N h n ∧
    (∀ y : groupCohomology.H2 (lineFaceRep N h n),
      (∀ F : GL (Fin 2) ℚ, twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0) →
        y ∈ lineFaceCuspidalInH2 N h n) ∧
    (∀ (F : GL (Fin 2) ℚ) (y : groupCohomology.H2 (lineFaceRep N h n)),
      twoCohomologyRestriction (lineFlagStab N h F).subtype (lineFaceRep N h n) y = 0 →
        twoCohomologyRestriction (lineFaceExt N h).inl (lineFaceRep N h n) y = 0) :=
  ⟨lineFaceEdge_injective N h n, map_lineCuspidal_eq_lineFaceCuspidal N h n,
    lineFaceCuspidalInH2_eq_locallyInner N h n,
    fun y hy => lineFace_mixed_of_flags_vanish N h n y hy,
    fun F y hy => restriction_radical_eq_zero_of_flag N h n F y hy⟩

end TernaryPeriodPolynomials.Argument.Statements.GammaNFaces
