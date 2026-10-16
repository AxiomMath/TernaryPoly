module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.BridgeK
public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.BaseCusp

@[expose] public section


/-!
# The antiholomorphic series at the standard cusp: constant term

The antiholomorphic series is the coefficientwise conjugate of the holomorphic one
(`seriesFormK_true`), conjugation intertwines the coefficient representation (`map_conj_rho`), so its class
is the conjugation twist of the class of the holomorphic series (`eisensteinAtClass_true_eq`), and the
twist commutes with the restriction to `Γ_P` (`resP_conj`). Hence `r_P` of the antiholomorphic series is
the conjugation twist of the seed class, which is the class of the antiholomorphic seed
(`constant_term_identity_conj`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open scoped MatrixGroups ContDiff
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument
  TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
  TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
  TernaryPeriodPolynomials.Argument.Statements.ConvergenceC4

section Std

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)

/-- Coefficient conjugation intertwines `ρ|_Γ` with itself. -/
theorem intertwines_conj_gammaRho : Intertwines (conjCLM n) (gammaRho Γ n) (gammaRho Γ n) := by
  intro g v
  apply Coef.toPoly_injective
  rw [toPoly_gammaRho, conjCLM_apply, Coef.toPoly_conjCoef, conjCLM_apply, Coef.toPoly_conjCoef,
    toPoly_gammaRho, map_conj_rho]

variable (D : CuspData) {F : Type*} [FunLike F UpperHalfPlane ℂ] (Λ : Subgroup (GL (Fin 2) ℝ))
  [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (f : F)

omit [Λ.HasDetOne] [Λ.IsArithmetic] [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] in
/-- The antiholomorphic series is the conjugation twist of the holomorphic series, as closed forms. -/
theorem planeEisensteinAtInv_true_eq [Λ.HasDetOne] [Λ.IsArithmetic]
    [CuspFormClass F Λ ((n + 3 : ℕ) : ℤ)] (hn : 4 ≤ n) (hLevi : LeviInCusp D Γ Λ) :
    planeEisensteinAtInv true D Γ Λ n f hn hLevi =
      twInv (intertwines_conj_gammaRho Γ n) (planeEisensteinAtInv false D Γ Λ n f hn hLevi) := by
  unfold planeEisensteinAtInv
  apply InvComponents.toInv_twist
  intro y hy a b
  apply Coef.toPoly_injective
  show seriesFormK true D Γ n f y a b = MvPolynomial.map (starRingEnd ℂ)
    (seriesFormK false D Γ n f y a b)
  exact seriesFormK_true D Γ Λ n f y a b

end Std

section StdN

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
/-- Coefficient conjugation intertwines the coefficient representation of a plane group. -/
theorem intertwines_conj_rhoR {G : Type} [Group G] (D : PlaneData G) :
    Intertwines (conjCLM n) (D.rhoR n) (D.rhoR n) := by
  intro g v
  apply Coef.toPoly_injective
  rw [toPoly_rhoR, conjCLM_apply, Coef.toPoly_conjCoef, conjCLM_apply, Coef.toPoly_conjCoef,
    toPoly_rhoR, map_conj_rho]

omit [NeZero N] in
/-- The restriction to `Γ_P` commutes with the conjugation twist. -/
theorem resP_conj (x : H2 (Rep.of (gammaRho (gammaN N) n))) :
    resP N n ((groupCohomology.map (MonoidHom.id (gammaN N))
      (twMor (intertwines_conj_gammaRho (gammaN N) n)) 2).hom x) =
      (groupCohomology.map (MonoidHom.id (gammaNP N))
        (twMor (intertwines_conj_rhoR (n := n) (gammaNPlaneData N))) 2).hom (resP N n x) := by
  induction x using H2_induction_on with | _ z => ?_
  unfold resP
  rw [H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply, H2π_comp_map_apply]
  congr 1

omit [NeZero N] in
/-- The class of the antiholomorphic seed is the conjugation twist of the class of the seed. -/
theorem cuspSeedConjClass_eq (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) :
    cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) =
      (groupCohomology.map (MonoidHom.id (gammaNP N))
        (twMor (intertwines_conj_rhoR (n := n) (gammaNPlaneData N))) 2).hom
        (cuspSeedClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) := by
  rw [← deRhamClass_cuspSeedConj, ← deRhamClass_cuspSeed]
  have e : cuspSeedConjInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) =
      twInv (intertwines_conj_rhoR (n := n) (gammaNPlaneData N))
        (cuspSeedInv (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f)) := rfl
  rw [e]
  exact deRhamClass_twist convex_faceSet faceSet_nonempty _ _

/-- **`r_P` of the antiholomorphic series at the standard cusp is the antiholomorphic seed class**
(`3 ≤ N`, `4 ≤ n`; the literal antiholomorphic constant-term identity). -/
theorem constant_term_identity_conj (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)
    (hN : 3 ≤ N) :
    resP N n (eisensteinAtClass_gammaN N n f 1 true hn) =
      cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) := by
  have e1 : eisensteinAtClass_gammaN N n f 1 true hn =
      (groupCohomology.map (MonoidHom.id (gammaN N))
        (twMor (intertwines_conj_gammaRho (gammaN N) n)) 2).hom
        (eisensteinAtClass_gammaN N n f 1 false hn) := by
    unfold eisensteinAtClass_gammaN eisensteinAtClass
    rw [planeEisensteinAtInv_true_eq]
    exact deRhamClass_twist convex_Omega Omega_nonempty _ _
  rw [e1, resP_conj, TernaryPeriodPolynomials.Argument.FormClassK.eisensteinAtClass_gammaN_one, constant_term_identity N n f hn hN,
    cuspSeedConjClass_eq]

end StdN

end TernaryPeriodPolynomials.Argument.EisensteinClass
