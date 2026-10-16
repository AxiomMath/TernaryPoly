module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.InnerConj
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.FrameIndep
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.CupEval
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Sum7
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Slant

@[expose] public section


/-!
# Export: `H³` of the flag stabilizers of `Γ(6)` is one-dimensional, with an explicit bar-cycle functional

Formalized by Claude Sonnet 5.5.

* `H3_ext_le`: for every group extension of `ℤ` by `ℤ²`, `dim_ℚ H³(B, ℚ) ≤ 1` (Bass-Serre dimension shifting along `ℤ` with the tree machinery, three times: `H1_int`, `H2_int2`).
* `cycle_isCycle`, `cycle_theta`: for a group with Heisenberg coordinates `(a, b, c) = (γ₀₁, γ₁₂, γ₀₂)` and elements `X`, `Y` of coordinates `(p,0,0)`, `(0,q,0)`, the seven-term bar chain
  `[X|Y'|W] - [Y|X|W] + [Y|W|X] - [X|W|Y'] + [W|X|Y'] - [W|Y|X] - [W|Y'|W]` (`W = [X,Y]`, `Y' = X⁻¹YX`) is a cycle, and the cocycle `θ(g₁,g₂,g₃) = b(g₁) a(g₂) (2 c(g₃) + a(g₂) b(g₃))` takes
  the value `-2 p² q²` on it.
* `flagStabData`, `flagStabDataOf`: for the stabilizer of every complete flag, `dim H³ = 1`, with nonzero evaluation functional `λ` (`λ[θ] = ∑ z(g) θ(g)` on cocycles).
* `flagLam F`, `flagGen F`: `λ_F` and the class `G_F` with `λ_F G_F = 1`, in the form `groupCohomology (Rep.res (stabilizer Γ6 F).subtype (𝟙_ _)) 3`; `flagLam_eq_smul_flagGen`.
* `lam_cup`: the value of `λ` on a cup product `u ∪ β` of a `1`-cocycle and a `2`-cocycle with trivial coefficients.
* `flagH3Data`: the classes `G o = G_{o.out}` as the `H3FlagData` of `GammaNStokes/ConstUniform`.

* `map_conj_self`: **inner automorphisms act trivially on `Hⁿ(G, A)` in every degree**, for every `Rep k G`: `groupCohomology.map (conjHom g) (conjBack g A) n = 𝟙` (`conjBack g A = ρ(g⁻¹)`).
* `flagLam_frame`, `flagGen_frame`, `flagDataAt_lam_indep`: `λ_F` and `G_F` do not depend on the choice of a frame `g` with `flagOf g = F`.
* `heisCycle_eval`, `lam_eval`, `lam_cup12`: `λ` of a class represented by a `3`-cochain (in particular a `cup12`) is the seven-term sum `c(X,Y',W) - c(Y,X,W) + c(Y,W,X) - c(X,W,Y') + c(W,X,Y') - c(W,Y,X) - c(W,Y',W)`.
* `sum7_cup12_flag`, `sum7_cup21_flag`, `lam_eval_sub`: M3c(iii), the closed form of the seven-term sum of the flag cup cochains for the Hochschild-Serre normal form, and `λ` of a difference of cochains.
* `exists_chainEval_eq_mul_lam`, `chainEval_theta_eq`: any bar `3`-cycle of a flag group evaluates on cocycles as `m · λ`, with `m` read off from the Heisenberg cocycle.

Not proved here: the compatibility of the classes `G_F` across the flags over one line or plane (hypotheses (B_L), (B_P) of `ConstUniform`).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.FlagH3

open TernaryPeriodPolynomials.Argument.FlagH3

alias H3_ext_le := TernaryPeriodPolynomials.Argument.FlagH3.H3_ext_le
alias H2_int2 := TernaryPeriodPolynomials.Argument.FlagH3.H2_int2
alias heis_theta_cocycle := TernaryPeriodPolynomials.Argument.FlagH3.HeisCoords.theta_cocycle
alias heis_cycle_isCycle := TernaryPeriodPolynomials.Argument.FlagH3.HeisCoords.cycle_isCycle
alias heis_cycle_theta := TernaryPeriodPolynomials.Argument.FlagH3.HeisCoords.cycle_theta
alias flagLam_flagGen := TernaryPeriodPolynomials.Argument.FlagH3.flagLam_flagGen
alias flagLam_ne_zero := TernaryPeriodPolynomials.Argument.FlagH3.flagLam_ne_zero
alias flagLam_eq_smul_flagGen := TernaryPeriodPolynomials.Argument.FlagH3.flagLam_eq_smul_flagGen
alias finrank_flagCohomology := TernaryPeriodPolynomials.Argument.FlagH3.finrank_flagCohomology
alias map_conj_self := TernaryPeriodPolynomials.Argument.FlagH3.map_conj_self
alias flagLam_frame := TernaryPeriodPolynomials.Argument.FlagH3.flagLam_frame
alias flagGen_frame := TernaryPeriodPolynomials.Argument.FlagH3.flagGen_frame
alias flagDataAt_lam_indep := TernaryPeriodPolynomials.Argument.FlagH3.flagDataAt_lam_indep
alias heisCycle_eval := TernaryPeriodPolynomials.Argument.FlagH3.heisCycle_eval
alias flagLam_eval := TernaryPeriodPolynomials.Argument.FlagH3.FlagCohomDatum.lam_eval
alias flagLam_cup12 := TernaryPeriodPolynomials.Argument.FlagH3.FlagCohomDatum.lam_cup12
alias sum7_cup12_flag := TernaryPeriodPolynomials.Argument.FlagH3.sum7_cup12_flag
alias sum7_cup21_flag := TernaryPeriodPolynomials.Argument.FlagH3.sum7_cup21_flag
alias flagLam_eval_sub := TernaryPeriodPolynomials.Argument.FlagH3.FlagCohomDatum.lam_eval_sub
alias exists_chainEval_eq_mul_lam := TernaryPeriodPolynomials.Argument.FlagH3.exists_chainEval_eq_mul_lam
alias chainEval_theta_eq := TernaryPeriodPolynomials.Argument.FlagH3.HeisCoords.chainEval_theta_eq
alias flagLam_cup := TernaryPeriodPolynomials.Argument.FlagH3.FlagCohomDatum.lam_cup

end TernaryPeriodPolynomials.Argument.Statements.FlagH3
