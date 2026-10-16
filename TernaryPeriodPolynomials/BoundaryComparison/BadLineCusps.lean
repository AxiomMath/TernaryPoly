module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BadLineCuspsWiring
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.SymBoundaryFactors
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.JFClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BassSerre
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.ModelCocycle

@[expose] public section


/-!
# The binary quotient and its cusps, and its use in Proposition 4.2

Export of `TernaryPeriodPolynomials.Argument.FiberModel.BadLineCusps` and `BadLineCuspsWiring`.  Paper
the paper, proof of `lem:bad-line-coordinate`,
"The binary quotient and its cusps" and "Detection of the polynomial".  Clause by clause:

* "Transport to `(a,b)=(-Y,Z-2Y)` ... `𝒜(a,b)=(-b,a-b)`, `ℬ(a,b)=(-a,b-a)`,
  `ℛ(a,b)=(-a,b-4a)` ... `(1+𝒜+𝒜²)Ĵ=0` and `Ĵ(a,b)=-Ĵ(b,a)` ... `(1-𝒜)u=Ĵ` and `ℬu=u`":
  `hat_a0, hat_b0, hat_r0` (the transport), `PositiveCocycle.relations`,
  `BadLineRelations.hat_cube`, `hat_antisymm`, `hat_primitive`.
* lower cusp (`Z ↦ Z-3Y`, coinvariant = `Z^d` coefficient, reflection fixes it and
  reverses the translation, so the full cusp `H¹` vanishes): `lower_coinvariants`,
  `lower_invariants`, `PositiveCocycle.lower_reflection_sign`, `PositiveCocycle.lower_cusp`.
* upper cusp (`Y ↦ Y-Z`, coinvariant = `Y^d` coefficient, reflection acts on `H¹` by
  `(-1)^{d+1}`, automatically zero for even `d`): `upper_coinvariants`,
  `BadLineRelations.upper_reflection_sign`, `BadLineRelations.upper_eval_even`.
* odd `d`, `J_f(Y,3Y)=0`, `(Ĵ+𝒜Ĵ)(a,2a)=-Ĵ(a,-a)=0`, "Both cusp restrictions
  therefore vanish in every parity": `BadLineRelations.upper_eval_of_J3`, `upper_cusp`,
  `PositiveCocycle.cusp_restrictions_vanish`.
* "Detection of the polynomial": `detection`.
* Wiring: `BadLineCuspsWiring.relations_of_symmetricSolution` (the library's
  `J_f = bernoulliObstruction f`, binary image `toBinary`, satisfies the relations and
  `J_f(Y,3Y) = 0`, `J_f(0,Z) = 0`) and `prop_4_2_cusp_argument` (upper cusp restriction vanishes;
  coboundary implies `J_f = 0`).  These re-derive, in the paper's own terms, the cusp-restriction and
  detection steps that the `symmetric_obstruction_vanishes` obtains through
  `PolynomialBoundaryBridge.polynomial_boundary_bridge`; the proofs are unchanged.

Additions:

* Hochschild-Serre for the cusp stabilizers `⟨t,r⟩` (infinite dihedral),:
  `IsCocycle.dihedral_iff` (restriction to `⟨t,r⟩` is a coboundary iff `c(t) = Q - tQ`, by averaging
  over `⟨r⟩`), `lower_cusp_H1_vanishes` ("its full cusp `H¹` vanishes", every `d`),
  `upper_class_sign` (`λ_Y(c T) = (-1)^{d+1} λ_Y(c T)`), `upper_cusp_restriction_iff`,
  `upper_cusp_H1_vanishes_of_even`, `PositiveCocycle.cusp_H1_restrictions_vanish`: statements about
  the actual stabilizers `cuspStabLower = ⟨U₀,R₀⟩`, `cuspStabUpper = ⟨T,R₀⟩` of `Γ₂`.
* `lem:sym-boundary-factors` over `ℂ` via the coefficient base change, and
  `J_f(0,Z) = 0`, `J_f(Y,3Y) = 0` from it: `SymBoundaryFactors.lemma_2_2_complex`,
  `sym_boundary_factors`, `bernoulliObstruction_zero_Y`, `bernoulliObstruction_three_Y`.
* `j_F`: `JFClass.PositiveCocycle.jF_zero_iff` (`[u] = 0` in
  `V/(V^{⟨A,B⟩}+V^R)` iff the positive cocycle is a coboundary), `eq_zero_of_jF_zero` (detection from
  `j_F = 0`), `primitive_spec` (`(1-A)u = J`, `Bu = u`), `closure_a0_b0_r0` (`Γ₂ = ⟨A₀,B₀,R₀⟩`).  The
  converse existence of a cocycle with prescribed generator values is not used by the paper
  (the cocycle `𝒥(φ_l)` is given; only the injectivity direction is used) and is not proved.
* Bass-Serre/Schreier, `BassSerre`: index four (`isComplement`), cycle types
  `(2,2)`, `(3,1)` (`cycle_types`), the Schreier generators (`schreier_values`),
  `Γ₀(3) = ⟨-1,A₀,U₀⟩`, `Γ₁(3) = ⟨A₀,U₀⟩`, `-1 ∉ Γ₁(3)`.  The Bass-Serre structure theorem itself
  (`Γ₁(3) ≅ C₃ * ℤ` from the quotient graph of groups; `PSL₂(ℤ) ≅ C₂*C₃`) is not formalized; the
  conclusion `eq:Gamma-presentation` is `Exports/TernaryPeriodPolynomials.Argument.FiberModel.gamma2_free_product` (ping-pong).
* `ModelCocycle.prop_4_2_bad_line_literal`: the model's literal mixed-bar-edge radical coordinate
  of `z_F` is a positive cocycle on all of `Γ₂` (`modelCocycle_isCocycle`, `modelCocycle_positive`,
  value `J_f` at `A₀`, `0` at `B₀, R₀`), its cusp restrictions are coboundaries, and `j_F = 0`
  implies `J_f = 0`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.BadLineCusps

open TernaryPeriodPolynomials.Argument.FiberModel

export BadLineCusps
  (PositiveCocycle BadLineRelations lower_coinvariants lower_invariants upper_coinvariants detection
    hat_a0 hat_b0 hat_r0 calA_cube calB_sq calB_calA calB_calA_calA)

export BadLineCuspsWiring (relations_of_symmetricSolution prop_4_2_cusp_argument)

export ModelCocycle (prop_4_2_bad_line_literal modelCocycle_isCocycle modelCocycle_positive zF_literal)

end TernaryPeriodPolynomials.Argument.Statements.BadLineCusps
