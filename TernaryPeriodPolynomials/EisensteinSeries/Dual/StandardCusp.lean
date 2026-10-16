module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GammaNSeries
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinAverage

@[expose] public section


open CategoryTheory MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# The standard cusp: the bridge `resP ↔ resTo (Γ_{1⁻¹P1})` and the unconditional dual row `r_Q ℰ_Q^∨ = η`

Formalized by Claude Sonnet 5.5.

the `resP` restricts to `gammaNP N` with the plane-face representation, whereas the transport theorem
(`Cusps.dual_restrictions_transport`) uses `resTo (gammaNPAt N h)`.  For `h = 1` the two differ by the identity conjugation
`conjP N 1 : Γ_{1⁻¹P1} ≃* Γ_P`: `resTo_standard : resTo (Γ_{1⁻¹P1}) c = stdPull (resP c)` (transitivity of restriction, `restrict_comp`), and `resTo_standard_at`
for any `h0 = 1` (needed for `ȷ(1) = 1`).

`dual_rQ_standard` (UNCONDITIONAL for `3 ≤ N`, `4 ≤ n`): the restriction of the dual series class `ℰ_Q^∨(ω_f)` to the line-cusp group
`Γ_Q = Γ(N) ∩ Q(ℤ)` is `η = ȷ^*(seed of f)` (`dualSeedClass`), by transport of the `constant_term_identity` (`r_P ℰ_P(ω_f) = [seed of f]`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
theorem rhoAt_one_compat (g : gammaNPAt N (1 : SL(3, ℤ))) :
    rhoAt N 1 n g = (gammaNPlaneData N).rhoR n ((conjP N (1 : SL(3, ℤ))) g) := by
  rw [rhoR_eq_gammaRho (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g)]
  change gammaRho (gammaN N) n (inclAt N 1 g) = gammaRho (gammaN N) n (inclP N (conjP N 1 g))
  congr 1
  apply Subtype.ext
  simp [conjP]
  rfl

/-- The pullback along the (identity) conjugation `Γ_{1⁻¹P1} ≃ Γ_P`, carrying `H²(Γ_P, E)` to `H²(Γ_{1⁻¹P1}, E)`. -/
def stdPull : groupCohomology.H2 (Rep.of ((gammaNPlaneData N).rhoR n)) →
    groupCohomology.H2 (Rep.of (rhoAt N (1 : SL(3, ℤ)) n)) :=
  fun x => (groupCohomology.map (conjP N (1 : SL(3, ℤ))).toMonoidHom
    (resMor (conjP N (1 : SL(3, ℤ))).toMonoidHom (rhoAt N 1 n) ((gammaNPlaneData N).rhoR n)
      (rhoAt_one_compat N n)) 2).hom x

omit [NeZero N] in
/-- **Bridge `resP` ↔ `resTo`**: the restriction `resTo (Γ_{1⁻¹P1})` is `resP` followed by the pullback along the identity conjugation. -/
theorem resTo_standard (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    resTo (gammaNPAt N (1 : SL(3, ℤ))) (gammaNPAt_le N 1) (gammaRho (gammaN N) n) c' =
      stdPull N n (EisensteinClass.resP N n c') :=
  restrict_comp (conjP N (1 : SL(3, ℤ))).toMonoidHom (inclP N) (inclAt N (1 : SL(3, ℤ)))
    (fun g => Subtype.ext (by simp [conjP]; rfl)) (gammaRho (gammaN N) n) ((gammaNPlaneData N).rhoR n)
    (rhoR_eq_gammaRho (gammaNPlaneData N) (inclP N) (fun g => gammaNPlaneData_plm N g))
    (rhoAt N 1 n) (rhoAt_one_compat N n) (fun _ => rfl) c'

/-- `stdPull` transported to any `h0 = 1`. -/
def stdPullAt (h0 : SL(3, ℤ)) (hh : h0 = 1) : groupCohomology.H2 (Rep.of ((gammaNPlaneData N).rhoR n)) →
    groupCohomology.H2 (Rep.of (rhoAt N h0 n)) := by
  subst hh
  exact stdPull N n

omit [NeZero N] in
theorem resTo_standard_at (h0 : SL(3, ℤ)) (hh : h0 = 1)
    (c' : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n))) :
    resTo (gammaNPAt N h0) (gammaNPAt_le N h0) (gammaRho (gammaN N) n) c' =
      stdPullAt N n h0 hh (EisensteinClass.resP N n c') := by
  subst hh
  exact resTo_standard N n c'

/-- The dual of the seed class at the standard cusp: `η = ȷ^*(seed)` in `H²(Γ_{1⁻¹Q1}, E^∨)`. -/
def dualSeedClass (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoN N n).comp (Subgroup.inclusion (gammaNQAt_le_N N (1 : SL(3, ℤ)))))) :=
  pullQP N n 1 (stdPullAt N n (jmath 1) jmath_one
    (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)))

/-- **`r_Q ℰ_Q^∨(η) = η` at the standard cusp, unconditional** (`3 ≤ N`, `4 ≤ n`): the line-cusp restriction of the dual series is the
`ȷ`-pullback of the seed class, by transport of S6's `constant_term_identity`. -/
theorem dual_rQ_standard (hn : 4 ≤ n) (hN : 3 ≤ N) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    resTo (gammaNQAt N (1 : SL(3, ℤ))) (gammaNQAt_le_N N 1) (dualRhoN N n) (dualSeriesClass_gammaN N n f hn) =
      dualSeedClass N n f := by
  rw [dualSeriesClass_gammaN_eq]
  refine ((dual_restrictions_transport (N := N) (n := n) (eisensteinClass_gammaN N n f hn)).1 1).trans ?_
  unfold dualSeedClass
  rw [resTo_standard_at N n (jmath 1) jmath_one, constant_term_identity N n f hn hN]

end TernaryPeriodPolynomials.Argument.EisensteinDual
