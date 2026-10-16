module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.GammaNAverage
public import TernaryPeriodPolynomials.EisensteinSeries.Class.AveragePreserves
public import TernaryPeriodPolynomials.EisensteinSeries.Class.RestAverage
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinConstantTerm

@[expose] public section


/-!
# Fiber averaging on the plane face and the reduction of the constant-term vanishing

## Proved
* `avInv`: for the plane group `Γ_P = Γ(N) ∩ P(ℤ)` acting on the boundary model `e(P) = ℝ² × ℍ`, the torus
  average `∫_{[0,1]²} ρ(t_{N(a,b)})⁻¹ τ_{N(a,b)}^* F da db` is a linear map on the closed `Γ_P`-invariant
  `E_n`-valued 2-forms (smooth, closed, `Γ_P`-invariant: `d_avForm`, `pullForm_avForm`, `latticeData_gammaN`).
* `constantTermVanishing_of_average`: `AveragePreservesClass N n` (Kasuya, abelian radical) and
  `RestAverageVanishes N n f hn` (unfolded zero modes) imply `ConstantTermVanishing N n f hn`, i.e. (by
  `constant_term_iff`) the constant term of the literal class is the seed class.

* `average_preserves_class`: obligation (a), `AveragePreservesClass N n` (the torus average does not change the
  de Rham class; proved by Cartan/Koszul homotopies and a normalized zig-zag, `Proofs/EisensteinClass/
  AveragePreserves.lean`).
* `constant_term_of_restAverage`: the constant-term identity from (b) alone.
* `rest_average_vanishes`: obligation (b), `RestAverageVanishes N n f hn` for `3 ≤ N`, `4 ≤ n` (unfolding over the
  orbits of the radical lattice on `Γ_P \ Γ(N)`; cuspidality along the stabilizing horocycle;
  `Proofs/EisensteinClass/{UnfoldCusp,UnfoldGeom,UnfoldOrbit,UnfoldSum,RestAverage}.lean`).
* `constant_term_identity`: for `3 ≤ N` and `4 ≤ n`, `r_P [𝓔_P(ω_h)] = [seed of f]` at the plane face
  (holomorphic seed at the standard cusp), with no hypothesis.

## Not proved
The other plane cusps, the antiholomorphic seed, the line radical and the flag/Heisenberg radical (`r_B`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

/-- **The constant term of the literal class is the seed class, given fiber averaging.** -/
theorem constant_term_of_average (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
    (ha : AveragePreservesClass N n) (hb : RestAverageVanishes N n f hn) :
    EisensteinClass.resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :=
  (constant_term_iff N n f hn).2 (constantTermVanishing_of_average N n f hn ha hb)

/-- **Obligation (a), proved**: the torus average does not change the de Rham class. -/
theorem average_preserves_class (N : ℕ) [NeZero N] (n : ℕ) : AveragePreservesClass N n :=
  averagePreservesClass N n

/-- **The constant term of the literal class is the seed class, given only the unfolding (b).** -/
theorem constant_term_of_restAverage (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
    (hb : RestAverageVanishes N n f hn) :
    EisensteinClass.resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :=
  constant_term_of_average N n f hn (average_preserves_class N n) hb

/-- **Obligation (b), proved**: the torus average of the non-identity part of the series vanishes
(`3 ≤ N`, `4 ≤ n`). -/
theorem rest_average_vanishes (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (hN : 3 ≤ N) :
    RestAverageVanishes N n f hn :=
  restAverageVanishes N n f hn hN

/-- **The constant term of the literal class at the plane face is the seed class** (`3 ≤ N`, `4 ≤ n`),
holomorphic seed at the standard cusp: no hypothesis. -/
theorem constant_term_identity (N : ℕ) [NeZero N] (n : ℕ)
    (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (hN : 3 ≤ N) :
    EisensteinClass.resP N n (eisensteinClass_gammaN N n f hn) =
      cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :=
  constant_term_of_restAverage N n f hn (rest_average_vanishes N n f hn hN)

end TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
