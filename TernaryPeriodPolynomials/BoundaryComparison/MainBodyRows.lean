module

public import TernaryPeriodPolynomials.PeriodPolynomial.SignedBinary.SignedBinary
public import TernaryPeriodPolynomials.PeriodPolynomial.SignedBinary.Lift
public import TernaryPeriodPolynomials.ArithmeticCohomology.SupportMixing
public import TernaryPeriodPolynomials.ModularForm.Periods.FirstDegreeTen
public import TernaryPeriodPolynomials.SymmetricSolution.CoefficientCondition.CoefficientCondition
public import TernaryPeriodPolynomials.SymmetricSolution.CoefficientCondition.Binary
public import TernaryPeriodPolynomials.SymmetricSolution.Bernoulli.Derivative
public import TernaryPeriodPolynomials.SymmetricSolution.HSymmetry.HSymmetry
public import TernaryPeriodPolynomials.SymmetricSolution.HSymmetry.J
public import TernaryPeriodPolynomials.SymmetricSolution.HSymmetry.PeriodP
public import TernaryPeriodPolynomials.Polynomial.NormKernel.Chains
public import TernaryPeriodPolynomials.SymmetricSolution.Residue.Equation
public import TernaryPeriodPolynomials.SymmetricSolution.Residue.Fiber
public import TernaryPeriodPolynomials.ArithmeticCohomology.H1Column.Log
public import TernaryPeriodPolynomials.Building.RowIdentities
public import TernaryPeriodPolynomials.GroupCohomology.Ext.RowIdentities
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.RowIdentities
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.Rows
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.HochschildSerreRows
public import TernaryPeriodPolynomials.ArithmeticCohomology.GoodLine.RowIdentities
public import TernaryPeriodPolynomials.GroupCohomology.Radical.LineRadical
public import TernaryPeriodPolynomials.GroupCohomology.Radical.LeviLaw
public import TernaryPeriodPolynomials.SymmetricSolution.Residue.Action
public import TernaryPeriodPolynomials.GroupCohomology.Ext.Segment
public import TernaryPeriodPolynomials.ArithmeticGroup.LeviVcd
public import TernaryPeriodPolynomials.GroupCohomology.Ext.Yoneda
public import TernaryPeriodPolynomials.GroupCohomology.Ext.YonedaPushout
public import TernaryPeriodPolynomials.GroupCohomology.Ext.YonedaUse
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.OppositePlane
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Line
public import TernaryPeriodPolynomials.SymmetricSolution.NormalJet.Derivative
public import TernaryPeriodPolynomials.PeriodPolynomial.PeriodCZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Clauses
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Tables
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.Bridge
public import TernaryPeriodPolynomials.SymmetricSpace.Model
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient
public import TernaryPeriodPolynomials.SymmetricSpace.Dimension
public import TernaryPeriodPolynomials.SymmetricSpace.NormalizedOrientation
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.Lemma41iiiMixedComponent
public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.Lemma41iiiInjective
public import TernaryPeriodPolynomials.BoundaryComparison.RadicalCohomologyTables
public import TernaryPeriodPolynomials.ModularForm.HeckeEuler.Product
public import TernaryPeriodPolynomials.ModularForm.HeckeEuler.Operators
public import TernaryPeriodPolynomials.ModularForm.HeckeComposite.Series
public import TernaryPeriodPolynomials.ModularForm.HeckeComposite.Arith
public import TernaryPeriodPolynomials.ModularForm.HeckeComposite.Function

@[expose] public section


/-!
# Aliases for the main-body rows reviewed as "missing"

(S1: MR-4, MR-5).
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### MR-4 and MR-5: the signed binary relation sets `𝓑_d^ε`, -/

namespace SignedBinary

open TernaryPoly.Paper TernaryPeriodPolynomials.Argument.Identities

/-- **MR-4**: `𝓑_d = 𝓑_d^+ = 𝒫_d^{0,odd}(ℚ)`, as submodules of `ℚ[X,Y]`. -/
theorem B_eq_oddPeriodSpace (d : ℕ) : signedBinary 1 d = oddPeriodSpace ℚ d := signedBinary_one_eq d

/-- **MR-4**: `𝓑_d^0 = 𝓑_d^- = 𝒫_d^{0,ev}(ℚ)`, as submodules of `ℚ[X,Y]`. -/
theorem B0_eq_evenPeriodSpace (d : ℕ) : signedBinary (-1) d = evenPeriodSpace ℚ d := signedBinary_neg_one_eq d

/-- **MR-5**: for `q ∈ 𝓑_d^ε`, `ε = ±1`, `d > 0`: `w = x+y+z` divides `Φ(q)`, and `L(q) = Φ(q)/w` is homogeneous of
degree `d-1`, cyclically invariant and of symmetry `ε`. -/
theorem polynomial_lift {ε : ℚ} (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) {q : Binary ℚ} (hq : q ∈ signedBinary ε d) :
    (X 0 + X 1 + X 2 : Ternary ℚ) ∣ cyclicLift q ∧
      cyclicLift q = (X 0 + X 1 + X 2 : Ternary ℚ) * polynomialLift q ∧
      (polynomialLift q).IsHomogeneous (d - 1) ∧
      bind₁ ![X 1, X 2, X 0] (polynomialLift q) = polynomialLift q ∧
      bind₁ ![X 1, X 0, X 2] (polynomialLift q) = ε • polynomialLift q :=
  signedBinary_lift hε hd hq

end SignedBinary

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### MR-1, MR-2, MR-3 (H9): first degree ten, support mixing, coefficient condition -/

namespace H9

/-- **MR-1**: `W_d(F) = 0` for `d < 10`, `W_10(F) ≠ 0`, `dim W_10(F) = 2`. -/
alias first_nonzero_solution_degree_ten :=
  TernaryPeriodPolynomials.Argument.Identities.first_nonzero_solution_degree_ten

/-- **MR-1**: the vanishing below degree ten, for a field of characteristic zero. -/
alias solutionSpace_eq_bot_of_lt_ten :=
  TernaryPeriodPolynomials.Argument.Identities.solutionSpace_eq_bot_of_lt_ten

/-- **MR-2**: the support-mixing example `y²z ↦ (x−y)²z = x²z − 2xyz + y²z`. -/
alias support_mixing_example :=
  TernaryPeriodPolynomials.Argument.Identities.support_mixing_example

/-- **MR-2**: the same identity read off the operator `threeTermNorm`. -/
alias threeTermNorm_support_mixing :=
  TernaryPeriodPolynomials.Argument.Identities.threeTermNorm_support_mixing

/-- **MR-3**: a nonzero homogeneous `q` of degree `22` in `𝓑_22^+` (literal
`eq:signed-binary` conditions) with vanishing `XY²¹` coefficient. -/
alias coefficient_condition_not_sufficient :=
  TernaryPeriodPolynomials.Argument.Identities.coefficient_condition_not_sufficient

end H9

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### H9 follow-ups: MR-3 on the paper's objects, the Bernoulli identity, and eq:H-symmetry -/

namespace H9Coverage

/-- **MR-3, binary form**: a nonzero `q ∈ 𝓑_22` (the literal `signedBinary 1 22`) with vanishing `XY²¹` coefficient. -/
alias coefficient_condition_not_sufficient_B :=
  TernaryPeriodPolynomials.Argument.Identities.coefficient_condition_not_sufficient_B

/-- **MR-3, paper object**: the same witness in `𝒫_22^{0,odd}(ℚ) = TernaryPoly.Paper.oddPeriodSpace ℚ 22`. -/
alias coefficient_condition_not_sufficient_odd :=
  TernaryPeriodPolynomials.Argument.Identities.coefficient_condition_not_sufficient_odd

/-- The second Bernoulli identity as a literal `ℚ⟦X⟧` identity. -/
alias bernoulli_second_cancellation :=
  TernaryPeriodPolynomials.Argument.Identities.bernoulli_second_cancellation

/-- **eq:H-symmetry**: the stand-alone literal statement, for a polynomial `v` in `ℚ[X,Y,Z]` with `Sv = Cv = v`. -/
alias eq_H_symmetry := TernaryPeriodPolynomials.Argument.Identities.HSymmetry.eq_H_symmetry

/-- **lem:period-extraction**: the parity clauses `p` odd in `X`, even in `Y`, with `∂_X p = bind₁ (X₁, -X₀) ∂_X p`,
under the hypotheses `hp₁ : ∂_X p = -H v`, `hp₀ : p(0,Y) = 0`, and `hCv` (the `C_v` identity). -/
alias p_parity := TernaryPeriodPolynomials.Argument.Identities.HSymmetry.p_parity

/-- **`hCv` from `J_v = 0`**: `p_parity` with the `C_v` hypothesis discharged by the Bernoulli obstruction
`bernoulliObstruction (complexify v hv) = 0` (`NormalJet.periodC_eq_zero_of_J_zero`), for a symmetric odd homogeneous `v` over `ℚ`.
Formalized by Claude Haiku 5.5. -/
alias p_parity_of_J_zero := TernaryPeriodPolynomials.Argument.Identities.HSymmetryJ.p_parity_of_J_zero

/-- **`p = -∫₀^X H(s,Y) ds` (the paper's `periodP`, as a binary lift)**: `periodP (cpx v) = liftJ (-antiQ (HJet v))`.
Formalized by Claude Haiku 5.5. -/
alias periodP_eq_liftJ_anti :=
  TernaryPeriodPolynomials.Argument.Identities.HSymmetryPeriodP.periodP_eq_liftJ_anti

/-- **`p_parity` for the paper's `p`**: for a homogeneous odd symmetric `v` over `ℚ` with `J_v = 0`, the binary
`p = -∫₀^X H(s,Y) ds` satisfies the five clauses of `eq:H-symmetry`/`lem:period-extraction`, with `hp₁`, `hp₀` and `hCv` all discharged
(no hypothesis on `p`). Formalized by Claude Haiku 5.5. -/
alias p_parity_periodP :=
  TernaryPeriodPolynomials.Argument.Identities.HSymmetryPeriodP.p_parity_periodP

/-- **degree five**: the normal forms of the degree-five spanning elements give, successively, `a³b`, `a²c`, `ab²`, `bc`. -/
alias appendixD_chain_deg5 :=
  TernaryPeriodPolynomials.Argument.Identities.AppendixDChains.chain_deg5

/-- **degree six**: the normal forms give, successively, `c²`, `abc`, `b³`, `a²b²`. -/
alias appendixD_chain_deg6 :=
  TernaryPeriodPolynomials.Argument.Identities.AppendixDChains.chain_deg6

/-- **`𝓜` against `AdaptedBasis`**: the standard monomials of `𝓜` are the indices
`{0,…,8,10,11,12,14,15,17,19,21,22,25,27}`. -/
alias appendixD_M_indices :=
  TernaryPeriodPolynomials.Argument.Identities.AppendixDChains.M_indices

/-- **the fifteen non-exceptional monomials of `𝓜`**: the index set `𝓜 \ {11,12,15,19,21}`
(the normal-form identities `(1+π)m = m` for these are `nf_onePlusProjector_nonExc`, not aliased here). -/
alias appendixD_nonExc_indices :=
  TernaryPeriodPolynomials.Argument.Identities.AppendixDChains.nonExc_indices

/-- **the `hCv` question**: `v = XYZ` is symmetric and odd homogeneous with `HJet v` not symmetric under `(X,Y) ↦ (-Y,X)`-type
parity, so the parity of `H` is not a consequence of the symmetry of `v` and odd homogeneity; the hypothesis `hCv` is needed. -/
alias H_parity_not_from_symmetry :=
  TernaryPeriodPolynomials.Argument.Identities.HSymmetry.H_parity_not_from_symmetry

end H9Coverage

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### MR-8: the `H¹` column of `eq:table-weights` and `log ρ(U_ij) = -x_j ∂_{x_i}`, -/

namespace H1Column

/-- **MR-8**: `H¹(N_P, E) ≅ Sym^{n+1}(x,y)*` as an `L_P`-module: a linear isomorphism onto the binary forms of degree `n+1`
(on cocycles the degree-raised contraction `(a, b) ↦ x·a|_{z=0} + y·b|_{z=0}`), under which the Levi element `A ∈ GL₂(ℤ)` acts (by the genuine
conjugation action on `H¹`) as the inverse substitution `A⁻¹`, without determinant twist. -/
alias plane_radical_H1 := TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.plane_radical_H1

/-- **MR-8**: `H¹(N_L, E) ≅ η⁻¹ det(D) · Sym^{n+1}(y,z)*` as an `L`-module: the Levi element `diag(η, D)` acts as the inverse
substitution by `D` times the character `η⁻¹ det D`. -/
alias line_radical_H1 := TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.line_radical_H1

/-- **MR-8**: the action of `U_ij` on `E_n` is the exponential of the nilpotent operator `-x_j ∂_{x_i}`. -/
alias rho_unipotent_eq_exp := TernaryPeriodPolynomials.Argument.Identities.rho_unipotent_eq_exp

/-- **MR-8**: `log ρ(U_ij) = -x_j ∂_{x_i}`, the (finite) logarithm series of `ρ(U_ij)` on `E_n`. -/
alias log_rho_unipotent := TernaryPeriodPolynomials.Argument.Identities.log_rho_unipotent

/-- **MR-8**: `-x_j ∂_{x_i}` is the only nilpotent endomorphism of `E_n` with exponential `ρ(U_ij)`. -/
alias log_rho_unique := TernaryPeriodPolynomials.Argument.Identities.log_rho_unique

end H1Column

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### literal statements for the clauses marked "unverified" -/

namespace ReviewRows

/-- The apartment of an ordered basis of `ℚ³` is the oriented hexagon `L₁ → P₁₂ → L₂ → P₂₃ → L₃ → P₃₁ → L₁` (sum of its six oriented edges). -/
alias apartment_hexagon := TernaryPeriodPolynomials.Argument.Identities.basisApartment_hexagon

/-- Permuting the basis multiplies the apartment by the sign of the permutation. -/
alias apartment_perm_sign := TernaryPeriodPolynomials.Argument.Identities.basisApartment_perm

/-- The identity apartment has only good vertices. -/
alias identity_apartment_vertices_good := TernaryPeriodPolynomials.Argument.Identities.identity_apartment_vertices_good

/-- `K` is the group of invertible integral matrices preserving the coordinate sum modulo three. -/
alias K_iff_sum_preserved := TernaryPeriodPolynomials.Argument.Identities.K_iff_sum_preserved

/-- A retained line has a unique primitive vector whose coordinate sum is one modulo three. -/
alias good_line_unique_primitive := TernaryPeriodPolynomials.Argument.Identities.good_line_unique_primitive

/-- The stabilizers `H_P, H_L, H_BB, H_BG` with their displayed matrices written out entrywise. -/
alias stabilizers_explicit := TernaryPeriodPolynomials.Argument.Identities.stabilizers_explicit

/-- In even degree the four stabilizer vanishings make `Ext¹_K(Q₀, E_n) = 0`. -/
alias ext_Q0_vanishing := TernaryPeriodPolynomials.Argument.Identities.ext_Q0_vanishing

/-- `K† = B₃ K B₃⁻¹`, i.e. `g ∈ K†` (defined by `e₃* g ≡ e₃* mod 3`) iff `B₃⁻¹ g B₃ ∈ K`. -/
alias arithmeticLevel_eq_conj := TernaryPeriodPolynomials.Argument.Identities.arithmeticLevel_eq_conj

/-- `e₃* B₃ = ℓ = (1,1,1)` (modulo three). -/
alias lastRow_vecMul_B3 := TernaryPeriodPolynomials.Argument.Identities.lastRow_vecMul_B3

/-- `K†` fixes `e₃*` modulo three, derived as in the paper from `ℓ k ≡ ℓ`. -/
alias conj_fixes_lastRow := TernaryPeriodPolynomials.Argument.Identities.conj_fixes_lastRow

/-- The rational level `K†` of the Lean definitions is the `B₃`-conjugate of the rational image of `K`. -/
alias rationalLevel_eq_conj := TernaryPeriodPolynomials.Argument.Identities.rationalLevel_eq_conj

/-- `T† = B₃ T↑`: `B₃` is an isomorphism of incidence graphs from the good (coordinate sum) graph to the good (last coordinate) graph. -/
alias graphIso_B3 := TernaryPeriodPolynomials.Argument.Identities.graphIso_B3

/-- `T† = B₃ T↑` on flags: the Lean `GoodFlag` of `B₃ g` is goodness of the flag `g` in the coordinate-sum sense. -/
alias goodFlag_B3_iff := TernaryPeriodPolynomials.Argument.Identities.goodFlag_B3_iff

/-- **Lemma 4.1 (i)**: the class `a_F` has a representative with only the mixed Hochschild-Serre term, for every choice of paths and realizing cocycle. -/
alias lemma41_i_class := TernaryPeriodPolynomials.Argument.Identities.lemma41_i_class

/-- **Lemma 4.1 (i), intrinsic form**: the restrictions of `a_F` to the radical `U` and to the Levi `L` of the bad-line stabilizer vanish, and `H²(L, M) = 0` for every
`L`-module `M` (no further Hochschild-Serre filtration term). -/
alias lemma41_i_intrinsic := TernaryPeriodPolynomials.Argument.Identities.lemma41_i_intrinsic

/-- The integral Levi `{±1} × Γ₂` has rational cohomological dimension one: `H²(L, M) = 0` for every complex `L`-module `M`. -/
alias levi_H2_zero := TernaryPeriodPolynomials.Argument.Identities.leviQ_H2_zero

/-- **Appendix C, **: the stabilizer of the good line `ℚ e₃` in `K†` is `{[[D, 0], [3(a,b), 1]] : D ∈ GL₂(ℤ), a, b ∈ ℤ}`. -/
alias goodLine_stabilizer_explicit := TernaryPeriodPolynomials.Argument.Identities.goodLine_stabilizer_explicit

end ReviewRows

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### MR-6 and MR-7: the boundary-jet lemma, -/

namespace BoundaryJet

open TernaryPeriodPolynomials.Argument.Identities

/-- **MR-6**: `J_v(X, 0, Z) = Z · v(Z, -X, X)` for every homogeneous `v` (no norm hypothesis, no symmetry hypothesis). -/
alias J_opposite_line := TernaryPeriodPolynomials.Argument.Identities.J_opposite_line

/-- **MR-6**: the same as an identity of polynomials, `J_v(X, 0, Z) = Z · v(Z, -X, X)`. -/
alias J_bind_second_zero := TernaryPeriodPolynomials.Argument.Identities.J_bind_second_zero

/-- **MR-6**: `J_v = 0` implies `v` vanishes identically on the opposite-pair plane `(Z, -X, X)`. -/
alias opposite_plane_of_J_zero := TernaryPeriodPolynomials.Argument.Identities.opposite_plane_of_J_zero

/-- **MR-6**: `J_v = 0` and `v` symmetric imply `c₊ = (x+y)(y+z)(z+x)` divides `v`. -/
alias cPlus_dvd_of_J_zero := TernaryPeriodPolynomials.Argument.Identities.cPlus_dvd_of_J_zero

/-- **MR-7, `eq:normal-jet`, first identity**: `J_v(X, Y, 3Y) = 0` for every odd symmetric `v`, as an identity in `ℂ[X, Y]`;
no norm hypothesis. -/
alias normal_jet_vanishes :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.bind_sigma3_bernoulliObstruction

/-- **MR-7, first identity**, evaluated: `J_v(a, b, 3b) = 0` for all `a, b ∈ ℂ`. -/
alias normal_jet_vanishes_values :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.J_normal_line

/-- **MR-7, `eq:normal-jet`, second identity**: for odd symmetric `v` (no norm hypothesis),
`∂_Z J_v |_{Z=3Y} = τ² B(3𝒟) B(𝒟) C_v`, with the paper's `p = -∫₀^X H(s,Y) ds` and `C_v = p(X-Y,Y) - p(X,Y) - h`. -/
alias normal_jet_derivative :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.normal_jet_derivative_literal

/-- **MR-7, second identity**, for any homogeneous `p` of degree `m` with `∂_X p = -H`. -/
alias normal_jet_derivative_of_antiderivative :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.normal_jet_derivative

/-- `-B(t) + t B'(3t)(1+eᵗ+e²ᵗ) + t e²ᵗ B(3t) = -e²ᵗ B(3t) B(t)` over `ℂ`. -/
alias bernoulli_second_cancellation_complex :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.bernoulli_derivative_identity

end BoundaryJet

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### Residue fibre as `(V_{n+1}/L·V_n) ⊗ (ℚL)^*` (H9) -/

namespace ResidueTensor

/-- The residue fibre `ResidueFiber n H` is isomorphic to `(V_{n+1}/L·V_n) ⊗ (ℚL)^*`, for the chosen equation `L` of `H`. -/
alias residueFiberTensorEquiv :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.residueFiberTensorEquiv

/-- The library residue of the fraction `q/L` at `H` is `[q] ⊗ L^∨` under that isomorphism. -/
alias residue_fraction_tensor :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.residue_fraction_tensor

/-- Replacing `(p, L)` by `(c·p, c·L)`, `c ≠ 0`, does not change `[p] ⊗ L^∨`. -/
alias residue_scale_tensor :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.residue_scale_tensor

/-- The functional `L^∨` on `ℚL` takes the value one at `L`. -/
alias lineDual_self := TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.lineDual_self

/-- Two nonzero linear forms on `ℚ³` with the same kernel are proportional. -/
alias proportional_of_same_kernel :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.proportional_of_same_kernel

/-- Nonzero linear forms with the same kernel are proportional (`V 1` form). -/
alias same_kernel_proportional :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.same_kernel_proportional

/-- `L` is an equation of `H`, i.e. a nonzero linear form defining the same hyperplane data. -/
alias IsEquationOf := TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.IsEquationOf

/-- Any two equations of `H` are proportional. -/
alias equation_proportional :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.equation_proportional

/-- The span of an equation of `H` does not depend on the chosen equation. -/
alias span_eq_of_equation :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.span_eq_of_equation

/-- The range of multiplication by an equation of `H` is independent of the chosen equation. -/
alias range_mulLin_eq := TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.range_mulLin_eq

/-- The residue of the fraction at `H` is literally independent of the chosen equation `L` of `H`. -/
alias residue_independent_of_equation :=
  TernaryPeriodPolynomials.Argument.Identities.ResidueTensor.residue_independent_of_equation

end ResidueTensor

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### Last sentence of the paper, and the bad-plane paragraph of the proof of `thm:J-vanishes` -/

namespace BadPlane

/-- (last sentence): for odd symmetric `v` (no norm hypothesis), `J_v = 0` implies `C_v = 0`; the operator `τ² B(3𝒟) B(𝒟)` is invertible. -/
alias periodC_eq_zero_of_J_zero :=
  TernaryPeriodPolynomials.Argument.Identities.NormalJet.periodC_eq_zero_of_J_zero

/-- **(a), `H¹`:** `H¹(N_P, E_n) ≅ det⁻¹ Sym^{n+1}((ℚ²)*)` as `GL₂(ℤ)`-modules, at the level `K†` (`P_0 =` the stabilizer of `⟨e₁,e₂⟩`, `E_n` the twisted coefficients). -/
alias radicalH1_iso := TernaryPeriodPolynomials.Argument.Identities.BadPlane.radicalH1_iso

/-- **(a), `H⁰`:** the invariants `E_n^{N_P}` are the line `det⁻¹` (used for `H²(L_P, E^{N_P}) = 0`). -/
alias radicalH0_iso := TernaryPeriodPolynomials.Argument.Identities.BadPlane.radicalH0_iso

/-- **(a), `H¹` with an arbitrary determinant twist** `E_{n,e} = Sym^n ⊗ det^e` (lattice model over `ℚ`): `H¹(N_P, E_{n,e}) ≅ det^e Sym^{n+1}`. -/
alias plane_radical_H1_twisted :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.plane_radical_H1_twisted

/-- **(a), `H²` with an arbitrary determinant twist:** `H²(N_P, E_{n,e}) ≅ det^{e-1} Sym^n`; `e = -1` is the displayed `det⁻² Sym^n` (the existing table was for `e = 0`). -/
alias plane_radical_H2_twisted :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.plane_radical_H2_twisted

/-- **(b),:** for `n > 0` and every twist `e`, `H²(N_P, E_{n,e})` has no nonzero `GL₂(ℤ)`-invariant (only the two opposite binary unipotents are used). -/
alias plane_H2_fixed_zero_twisted :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.plane_H2_fixed_zero_twisted

/-- **(b)/(c) at `K†`:** for `n > 0` every class of `H²(P_0, E_n)` restricts to zero on `N_P`. -/
alias radical_restriction_zero :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.radical_restriction_zero

/-- **(c),:** for `n > 0` the Hochschild-Serre edge `H²(P_0,E_n) → H¹(GL₂(ℤ), det⁻¹ Sym^{n+1})` is defined on every class (only the mixed restriction survives) ... -/
alias mixedEdge := TernaryPeriodPolynomials.Argument.Identities.BadPlane.mixedEdge

/-- ... and it is injective (the Levi has cohomological dimension one: `H²(GL₂(ℤ), det⁻¹) = 0`). -/
alias mixedEdge_injective := TernaryPeriodPolynomials.Argument.Identities.BadPlane.mixedEdge_injective

/-- **(d),:** at a binary cusp `B = cuspGL F` the mixed edge map of the flag stabilizer `N_P ⋊ B` is injective. -/
alias binary_cusp_edge_injective :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.binary_cusp_edge_injective

/-- **(e), local form:** zero radical restriction and cuspidal mixed edge iff restriction zero on every flag stabilizer. -/
alias cuspidal_iff_flags := TernaryPeriodPolynomials.Argument.Identities.BadPlane.cuspidal_iff_flags

/-- **(e), global form:** flag vanishing makes the plane class (at the bad plane `P_0` of `K†`) cuspidal. -/
alias plane_class_cuspidal_of_flag_vanishing :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.plane_class_cuspidal_of_flag_vanishing

/-- The lattice model of `N_P` used for the tables is the matrix group `identityPlaneRadicalInclusion` of the `K†` model. -/
alias radicalInclusion_eq_planeHom :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.radicalInclusion_eq_planeHom

/-- The Levi section `diag(A,1)` of the `K†` model is the matrix `planeElement A 0` of the tables. -/
alias leviSection_eq_planeElement :=
  TernaryPeriodPolynomials.Argument.Identities.BadPlane.leviSection_eq_planeElement

end BadPlane

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### The symmetric space `𝒳 ≅ SL₃(ℝ)/SO(3)`, -/

namespace SymmetricSpace

open TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace

/-- **(a):** `g ↦ (g gᵗ)⁻¹` maps `SL₃(ℝ)` onto the positive definite matrices of determinant one. -/
alias formMap_surjective := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.formMap_surjective

/-- **(a):** its fibres are the cosets of `SO(3)`: `(g gᵗ)⁻¹ = (h hᵗ)⁻¹ ↔ g⁻¹ h ∈ SO(3)`. -/
alias formMap_eq_iff := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.formMap_eq_iff

/-- **(a):** `SL₃(ℝ)/SO(3) ≃ {Q > 0, det Q = 1}`, `g SO(3) ↦ (g gᵗ)⁻¹`. -/
alias quotEquiv := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.quotEquiv

/-- **(a):** the equivalence is equivariant for the left action `g·Q = g^{-t} Q g⁻¹`. -/
alias quotEquiv_smul := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.quotEquiv_smul

/-- **(a):** the right action `Q ↦ gᵗ Q g` and the left action `g·Q = Q·g⁻¹`. -/
alias rightAct_mul := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.rightAct_mul

/-- **(a):** the Gram-matrix version `g SO(3) ↦ g gᵗ`, equivariant for congruence `g·P = g P gᵗ`. -/
alias quotEquivGram_smul := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.quotEquivGram_smul

/-- **(a):** `𝒳 = {Q > 0}/ℝ_{>0}`, determinant-one representatives: `{Q > 0, det Q = 1} ≃ 𝒳`. -/
alias normalizeEquiv := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.normalizeEquiv

/-- **(a):** `SL₃(ℝ)/SO(3) ≃ 𝒳`, `g SO(3) ↦ [(g gᵗ)⁻¹]`, equivariant for `g·[Q] = [g^{-t} Q g⁻¹]`. -/
alias cosetEquiv_smul := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.cosetEquiv_smul

/-- **(b):** the tangent space (symmetric trace-zero matrices) has dimension `5 = 6 - 1`. -/
alias finrank_tangent := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.finrank_tangent

/-- **(b):** the trace-one slice is homeomorphic to a subset of the five-dimensional space `tangentMat` ... -/
alias chartHomeo := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.chartHomeo

alias isOpen_chartImage := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.isOpen_chartImage

/-- **(c):** the library's `SymmetricSpacePositive.Space` (trace-one positive definite matrices) is `𝒳`: `S ↦ [S]`. -/
alias spaceEquiv := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.spaceEquiv

/-- **(c):** equivariance for the library's congruence `S ↦ g S gᵗ` (followed by the trace normalization). -/
alias spaceEquiv_act := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.spaceEquiv_act

/-- **(c):** through `Q = S⁻¹` the congruence action becomes the paper's `g·Q = g^{-t} Q g⁻¹`. -/
alias spaceEquivQ_act := TernaryPeriodPolynomials.Argument.Identities.SymmetricSpace.spaceEquivQ_act

end SymmetricSpace

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-!
## Rows 399, 276, 329 (Claude Sonnet 5.5)
-/

namespace R2

/-- the action of the line Levi `(η, D)`, `η = ±1`, `D ∈ GL₂(ℤ)`, on `H²(N_L, E)`. -/
alias lineLeviH2Action := TernaryPeriodPolynomials.Argument.Identities.R2LineRadical.lineLeviH2Action

/-- `H²(N_L, Sym^n)` is the line `ℚ` on which the Levi `(η, D)` acts by `η^{-n-2} det(D)` (any `D ∈ GL₂(ℤ)`, in particular `D ∈ Γ₂`). -/
alias lineH2_leviAction := TernaryPeriodPolynomials.Argument.Identities.R2LineRadical.lineH2_leviAction

/-- the general Levi action restricts to the library's diagonal sign group action `lineH2Action`. -/
alias lineLeviH2Action_diagonal := TernaryPeriodPolynomials.Argument.Identities.R2LineRadical.lineLeviH2Action_diagonal

/-- the independent line sign `η` acts by `η^{-n-2}`. -/
alias lineH2_lineSign := TernaryPeriodPolynomials.Argument.Identities.R2LineRadical.lineH2_lineSign

/-- the Levi element `diag(t, L)` in `GL₃(ℚ)`, `t = ±1`, `L ∈ GL₂(ℤ)`. -/
alias leviGL := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.leviGL

/-- `diag(t, L) ∈ K†` for `L ∈ Γ₂`. -/
alias leviGL_mem_rationalLevel := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.leviGL_mem_rationalLevel

/-- `g⁻¹ U(r) g = U(t r L)`. -/
alias leviGL_conjugate := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.leviGL_conjugate

/-- `J(g·b)(v) = t⁻² J(b)(L⁻¹ v)` for the radical coordinate of a one-cocycle of `N_L` with values in `E_{n,1}`. -/
alias radicalPair_leviLaw_binary := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.radicalPair_leviLaw_binary

/-- the independent integral line sign acts trivially on the radical coordinate. -/
alias radicalPair_lineSign := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.radicalPair_lineSign

/-- the radical coordinate does not involve `X`. -/
alias radicalPair_pderiv_zero := TernaryPeriodPolynomials.Argument.Identities.R2LeviLaw.radicalPair_pderiv_zero

/-- `R_n = ⨁_H (V_{n+1}/L_H V_n) ⊗ (ℚ L_H)^*` and the `GL₃(ℚ)`-action on it in tensor form. -/
alias ResidueTensorSum := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.ResidueTensorSum

alias tensorAction := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.tensorAction

/-- the action is the transport of the quotient-presentation action along H9's `residueFiberTensorEquiv`. -/
alias tensorAction_residueTensorAll := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.tensorAction_residueTensorAll

/-- `g · ([p] ⊗ λ)_H = ([g p] ⊗ μ)_J` where `μ(g ℓ) = λ(ℓ)`. -/
alias tensorAction_lof_tmul := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.tensorAction_lof_tmul

/-- `eq:residue-exact` in tensor form with both equivariances. -/
alias tensorResidue_short_exact := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.tensorResidue_short_exact

alias tensorResidue_simplePole := TernaryPeriodPolynomials.Argument.Identities.ResidueAction.tensorResidue_simplePole

/-- The first map of the exact segment `H¹(H_BB,E) ⊕ H¹(H_BG,E) → Ext¹_{K†}(Q₀,E) → H²(H_L,E) ⊕ H²(H_P,E)`. -/
alias extSegmentIn := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.segmentIn

/-- ... and the second map (connecting map followed by Shapiro). -/
alias extSegmentOut := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.segmentOut

/-- **The displayed segment is exact** (`Ext` is Mathlib's `Ext` in `Rep ℚ K†`). -/
alias ext_Q0_segment_exact := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.ext_Q0_segment_exact

/-- The Shapiro identifications `Ext¹(ℚ[edges],E) ≃ H¹(H_BB)×H¹(H_BG)` and `Ext²(ℚ[vertices],E) ≃ H²(H_L)×H²(H_P)`. -/
alias edgesExtEquiv := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.edgesExtEquiv

alias verticesExtEquiv := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.verticesExtEquiv

/-- The four vanishings make `Ext¹_{K†}(Q₀,E) = 0`, as a corollary of the exact segment. -/
alias ext_Q0_vanishing_of_segment := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.ext_Q0_vanishing_of_segment

alias ext_Q0_vanishing_via_segment := TernaryPeriodPolynomials.Argument.Identities.ExtSegment.ext_Q0_vanishing_via_segment

/-- Rational cohomology of a virtually free group vanishes above degree one, for every rational representation. -/
alias VirtuallyFree := TernaryPeriodPolynomials.Argument.Identities.LeviVcd.VirtuallyFree

alias VirtuallyFree.isZero := TernaryPeriodPolynomials.Argument.Identities.LeviVcd.VirtuallyFree.isZero

/-- Dimension shifting: `H² ≡ 0` for all coefficients gives `H^m ≡ 0` for `m ≥ 2`. -/
alias isZero_of_H2_isZero := TernaryPeriodPolynomials.Argument.Identities.LeviVcd.isZero_of_H2_isZero

/-- **The arithmetic Levi groups (`GL₂(ℤ)`, its subgroups such as `Γ₂`, `{±1} × Γ₂`, sign groups) have rational cohomology vanishing above degree one.** -/
alias levi_cohomology_vanishes_above_one := TernaryPeriodPolynomials.Argument.Identities.LeviVcd.levi_cohomology_vanishes_above_one


/-- The class of an extension is zero iff it splits. -/
alias yoneda_extClass_eq_zero_iff_split := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.extClass_eq_zero_iff_split

/-- An extension `0 → E → X → V → 0` (the paper's objects of `Ext¹(V,E)`). -/
alias yoneda_Extension := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.Extension

/-- Equivalence of extensions. -/
alias yoneda_Extension_Equiv := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.Extension.Equiv

/-- The class depends only on the equivalence class. -/
alias yoneda_Extension_cls_eq_of_equiv := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.Extension.cls_eq_of_equiv

/-- The obstruction `δf ∈ Ext¹(X₃,E)` to extending `f : X₁ → E` over `X₁ → X₂`. -/
alias yoneda_obstruction := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.obstruction

/-- `f` extends iff its obstruction vanishes. -/
alias yoneda_extends_iff_obstruction_eq_zero := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.extends_iff_obstruction_eq_zero

/-- The pushout extension `0 → E → (E ⊕ X₂)/{(f x,-ι x)} → X₃ → 0`. -/
alias yoneda_pushoutExtension := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.pushoutExtension

/-- `f` extends over `X₂` iff the pushout extension splits. -/
alias yoneda_extends_iff_pushout_splits := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.extends_iff_pushout_splits

/-- Extensions of the same class are equivalent. -/
alias yoneda_equiv_of_cls_eq := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.equiv_of_cls_eq

/-- Same class iff equivalent. -/
alias yoneda_cls_eq_iff_equiv := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.cls_eq_iff_equiv

/-- **The Yoneda bijection**: `{extensions of V by E}/≃ ≃ Ext¹(V,E)`, for Mathlib's `Ext` in `Rep ℚ G`. -/
alias yoneda_extensionClassEquiv := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.extensionClassEquiv

/-- Every class of `Ext¹(V,E)` is the class of an extension. -/
alias yoneda_exists_extension_with_class := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.exists_extension_with_class

/-- The boundary functional extends iff its obstruction in `Ext¹(Q₀,E)` vanishes. -/
alias yoneda_boundary_functional_extends_iff := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.boundary_functional_extends_iff

/-- ... iff the pushout extension splits. -/
alias yoneda_boundary_functional_extends_iff_split := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.boundary_functional_extends_iff_split

/-- In alternating even degree every Good-cycle functional extends and its pushout extension splits (`Ext¹_{K†}(Q₀,E) = 0`). -/
alias yoneda_alternating_even_extension := TernaryPeriodPolynomials.Argument.Identities.ExtYoneda.alternating_even_extension

end R2

/-! ### Sign (c) of Lemma 3.3 and Lemma 4.1 (iii) with the paper's premise -/

/-- **Lemma 3.3 with the paper-normalized pair**: the flat (boundary = coordinate apartment) and the averaged generator `-[T₀]` have local intersection number `+1`
(normal-projection degree at the transverse point, `Geometric.geoLocalIntersection`), and the diagram reads the top-cell coefficient literally. -/
alias lemma_3_3_paper_normalized :=
  TernaryPeriodPolynomials.Argument.Identities.Orientation.lemma_3_3_paper_normalized

/-- **The paper's orientation sentence** for the chosen pair. -/
alias paper_orientation_sentence_paper :=
  TernaryPeriodPolynomials.Argument.Identities.Orientation.paper_orientation_sentence_paper

/-- With the paper pair the geometric top evaluator reads the coefficient with constant `1` (compare the existential `apartment_evaluation_eq_coefficient`). -/
alias apartment_evaluation_eq_coefficient_paper :=
  TernaryPeriodPolynomials.Argument.Identities.Orientation.apartment_evaluation_eq_coefficient_paper

/-- The local intersection number of the flat with the paper generator is `+1`. -/
alias paperLocalIntersection_avgGenPaper :=
  TernaryPeriodPolynomials.Argument.Identities.Orientation.paperLocalIntersection_avgGenPaper

/-- **Lemma 4.1 (iii) for the cocycle of a polynomial functional with the specified paths**: vanishing of the mixed Hochschild-Serre component forces `J_f = 0`. -/
alias lemma41_iii := TernaryPeriodPolynomials.Argument.Identities.lemma41_iii

/-- **Lemma 4.1 (iii), class form**: for the class `a_F` of any realizing cocycle of any path family. -/
alias lemma41_iii_class := TernaryPeriodPolynomials.Argument.Identities.lemma41_iii_class

/-- **Edge injectivity of the Hochschild-Serre map on pure-mixed classes of the bad-line stabilizer**: mixed component zero iff the restriction to the stabilizer is zero. -/
alias mixedComponentZero_iff_resH2 := TernaryPeriodPolynomials.Argument.Identities.mixedComponentZero_iff_resH2

/-- The same for classes having a pure-mixed representative. -/
alias mixedComponentZeroClass_iff := TernaryPeriodPolynomials.Argument.Identities.mixedComponentZeroClass_iff

end TernaryPeriodPolynomials.Argument.Statements.Identities

namespace TernaryPeriodPolynomials.Argument.Statements.Identities

/-! ### Main-body rows: composite Hecke operators and the Euler product, -/

namespace HeckeEuler

/-- the Euler product `L(f, s) = ∏_p (local factor)` for a normalized eigenform `h` of weight `k`,
`(k/2 + 1) < Re s`. Formalized by Claude Haiku 5.5. -/
alias euler_product :=
  TernaryPeriodPolynomials.Argument.Identities.heckeLSeries_eulerProduct

/-- **Multiplicativity**: `T_m T_n = T_{mn}` for coprime `m, n > 0`, on functions with a q-expansion
`∑ c_N q^N` (the cusp-form case is `compositeHecke_comp_coprime` applied to `⇑h`).
Formalized by Claude Haiku 5.5. -/
alias composite_comp_coprime :=
  TernaryPeriodPolynomials.Argument.Identities.compositeHecke_comp_coprime

/-- **Eigenform**: `T_m h = a_h(m) h` for every `m ≥ 1` and every normalized eigenform `h` of level one.
Formalized by Claude Haiku 5.5. -/
alias composite_eigenform :=
  TernaryPeriodPolynomials.Argument.Identities.compositeHecke_eigenform

end HeckeEuler

end TernaryPeriodPolynomials.Argument.Statements.Identities
