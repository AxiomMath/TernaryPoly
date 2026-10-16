module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.LineClassPaper
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.ClassicalSeeds
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.EntrySeed
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.EichlerForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.SeedPassageFinal
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeedEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.LineSeed

@[expose] public section


/-!
# CMP-8 (K† comparison): classical seeds versus the adelic sections of the entry

Two statements are proved here.

**(1) Domain adequacy** (`Proofs/KDaggerComparison/ClassicalSeeds.lean`).  The classes to which the `bad_plane_data_injective` applies
(inner plane classes of `K†` vanishing at the good planes) are exactly the paper's bad-plane data, the transfers of the spans of the
holomorphic and antiholomorphic seeds of `Γ(N)`:
* `inner_components_are_seed_transfers`: every inner class has Shapiro components at a good and a bad plane that are transfers of
  seed-span classes (`lemma_C3_final_sentence` (A));
* `appendix_C6_classical_seeds`: for every seed-span class `yb` at a bad plane there is an inner class `ξ` with good component `0` and
  bad component the transfer of `yb`, and `bad_plane_data_injective` gives `ξ = 0` as soon as `T ξ` vanishes at every good line.

**(2) The entry section is a classical seed class** (`Proofs/KDaggerComparison/EntrySeed.lean`), plane half, level one.  For the
bad-plane section `a_pl = badPlaneClass S I` of the entry computation (class of `badPlaneWeight · planeSource`):
* `badPlane_edge`: its bad-plane binary edge is `-[φ_I]`;
* `badPlaneClass_seed_class`, `badPlaneClass_seed_class_exists`: for the classical level-one cusp form `f` of the Eichler input, the
  restriction to `Λ₀⁺` of its bad-plane coordinate is `-((n+1)/2)` times the complexified de Rham class of the classical seed
  `ω_f + \overline{ω_{f^*}}`; its good-plane coordinate is zero (`Entry.cuspRes_plane_true_badPlane`);
* `eichler_classical_section`: the binary adelic section of the Eichler vector is the classical `v_h` of the same level-one form
  (`H4`'s `vhModel_eq_full`), so `f` is the classical form behind the adelic section.

**(3) The Eichler form is a nonzero multiple of `S.form`** (`Proofs/KDaggerComparison/EichlerForm.lean`): `eichlerForm_eq_smul_form`
says that the classical level-one form `f` of the Eichler vector (its function is the scalar function of `S.vector`) is nonzero, has
`a₁(f) ≠ 0` and satisfies `f = a₁(f) • S.form` as cusp forms (equality of the underlying functions, not only of q-expansions);
`scalar_hasPrimeHeckeRelations` gives the prime Hecke relations of the vector's scalar function with the eigenvalues of `S.form`.

**(4) The line half, edge level** (`Proofs/KDaggerComparison/{LineSeedEdge,LineSeed}.lean`).  The good-line stabilizer `Λ₁ = ℤ² ⋊ GL₂(ℤ)` already has an
edge theory in the library (`edgeK`, injective on the classes with zero restriction to the lower radical).  For the good-line section
`a_li = goodLineClass S I = [goodLineWeight · lineSource D (lineLevi I)]`:
* `goodLine_edge`: its coordinate at the good line `⟨e₃⟩` (the Shapiro coordinate at the reference good line transported by any transporter `γ`) lies
  in `KL n` and has edge `-3(n+1) · [Sw ∘ ψ_f ∘ pivot]`, `ψ_f` the classical period cocycle (twist `0`, parity `0`) of the level-one form of the Eichler
  input (`eichlerClassicalCocycle_eq`);
* `goodLine_coordinate_eq_smul_of_edge`: injectivity of `edgeK` determines the coordinate by this edge;
* `paperGoodLine_edge`: for the paper's own good-line section (line seed `σ_h`; `λ_li = -1` against `a_li`) the edge is
  `+3(n+1) · [Sw ∘ ψ_f ∘ pivot]`.
The classical line seed is thus identified with an explicit scalar through its Eichler-Shimura period class; a geometric (zig-zag) line seed class
for the line face, the analogue of `eq_seed_of_edge`, is not built (the seed enters through its integral cochain `cΣ`, `EntryDictionary`).

Not covered: the geometric (zig-zag) line seed class of the line face, and the passage from
`Λ₀⁺` to the `Γ(N)`-level `seedBoundary` (which also needs the transport of the seed to the other bad-orbit cusps).

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.KDaggerCMP8

alias inner_components_are_seed_transfers :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.inner_components_are_seed_transfers
alias appendix_C6_classical_seeds :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.appendix_C6_classical_seeds
alias badPlane_edge := TernaryPeriodPolynomials.Argument.KDaggerComparison.badPlane_edge
alias badPlaneClass_seed_class :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.badPlaneClass_seed_class
alias badPlaneClass_seed_class_exists :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.badPlaneClass_seed_class_exists
alias scalar_hasPrimeHeckeRelations :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.scalar_hasPrimeHeckeRelations
alias eichlerForm_eq_smul_form :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.eichlerForm_eq_smul_form
alias phiPlane_badPlaneClass :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.phiPlane_badPlaneClass
alias phiPlaneAt_bad_face_forms :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.phiPlaneAt_bad_face_forms
alias entryCoeff := TernaryPeriodPolynomials.Argument.KDaggerComparison.entryCoeff
alias entryTuple := TernaryPeriodPolynomials.Argument.KDaggerComparison.entryTuple
alias eichler_classical_section :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.eichler_classical_section

alias goodLine_edge := TernaryPeriodPolynomials.Argument.KDaggerComparison.goodLine_edge
alias goodLine_coordinate_eq_smul_of_edge :=
  TernaryPeriodPolynomials.Argument.KDaggerComparison.goodLine_coordinate_eq_smul_of_edge
alias paperGoodLine_edge := TernaryPeriodPolynomials.Argument.KDaggerComparison.paperGoodLine_edge

/-! ### Line half, geometric (S1, LS15): the good-line coordinate restricted to `Λ₁⁺` is the line seed class -/

alias lineSeedIdentity := TernaryPeriodPolynomials.Argument.LineSeed.lineSeedIdentity
alias paperLineSeedIdentity := TernaryPeriodPolynomials.Argument.LineSeed.paperLineSeedIdentity

end TernaryPeriodPolynomials.Argument.Statements.KDaggerCMP8
