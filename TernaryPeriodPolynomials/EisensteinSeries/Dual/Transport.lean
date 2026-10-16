module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Series
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Restrict

@[expose] public section


open MvPolynomial UpperHalfPlane ModularForm
open scoped UpperHalfPlane MatrixGroups ContDiff

/-!
# Transport of restrictions along `ȷ`

Formalized by Claude Sonnet 5.5.

`dual_restriction_transport`: for subgroups `S ≤ Γ`, `S' ≤ Γ'` with `ȷ(S) ⊆ S'`, the restriction to `S` of the
`ȷ`-pullback of a class of `Γ'` is the `ȷ`-pullback (`jRestr : S → S'`) of its restriction to `S'`.  This is the whole cohomological
content of the passage from the constant terms of `ℰ_P` for `ȷ(Γ)` to those of the dual series (`ar:eq:dualconstantterms`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass
open TernaryPeriodPolynomials.Argument.SeedC3

/-- The group restriction `H²(Γ, ρ) → H²(S, ρ|_S)` along the inclusion `S ≤ Γ`, the form used for the constant terms
`r_R` (S6: `resMor (inclAt N h) (rhoAt N h n) ... (fun _ => rfl)`). -/
def resTo {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} (S : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ))
    (hS : S ≤ Γ) {n : ℕ} (ρ : Representation ℝ Γ (Coef n)) :
    groupCohomology.H2 (Rep.of ρ) → groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion hS))) :=
  fun x => (groupCohomology.map (Subgroup.inclusion hS)
    (resMor (Subgroup.inclusion hS) (ρ.comp (Subgroup.inclusion hS)) ρ (fun _ => rfl)) 2).hom x

variable (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (α : Γ →* Γ')
  (hα : ∀ g : Γ, (α g).1 = jmath g.1)
  (S S' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (hS : S ≤ Γ) (hS' : S' ≤ Γ')
  (hSS' : ∀ s : S, jmath s.1 ∈ S')

/-- The restriction of `ȷ` to a homomorphism `S → S'`. -/
def jRestr : S →* S' where
  toFun s := ⟨jmath s.1, hSS' s⟩
  map_one' := Subtype.ext jmath_one
  map_mul' a b := Subtype.ext (jmath_mul a.1 b.1)

include hα

theorem jRestr_comm (s : S) :
    α (Subgroup.inclusion hS s) = Subgroup.inclusion hS' (jRestr S S' hSS' s) :=
  Subtype.ext (hα _)

/-- **Transport of restrictions along `ȷ`**: restricting the `ȷ`-pullback of a class `c'` of `Γ'` to `S` is the `ȷ`-pullback
(along `S → S'`) of the restriction of `c'` to `S'`.  The restricted dual coefficient system on `S` is `ρ_{Γ'}(ȷ(·))`. -/
theorem dual_restriction_transport (n : ℕ) (c' : groupCohomology.H2 (Rep.of (gammaRho Γ' n))) :
    resTo S hS (dualRho Γ Γ' α n)
        ((groupCohomology.map α (resMor α (dualRho Γ Γ' α n) (gammaRho Γ' n) (fun _ => rfl)) 2).hom c') =
      (groupCohomology.map (jRestr S S' hSS')
        (resMor (jRestr S S' hSS') ((dualRho Γ Γ' α n).comp (Subgroup.inclusion hS))
          ((gammaRho Γ' n).comp (Subgroup.inclusion hS'))
          (fun s => by
            simp only [MonoidHom.coe_comp, Function.comp_apply, dualRho]
            rw [jRestr_comm Γ Γ' α hα S S' hS hS' hSS' s])) 2).hom
        (resTo S' hS' (gammaRho Γ' n) c') :=
  restrict_pullback (Subgroup.inclusion hS) α (jRestr S S' hSS') (Subgroup.inclusion hS')
    (jRestr_comm Γ Γ' α hα S S' hS hS' hSS') (dualRho Γ Γ' α n) (gammaRho Γ' n) (fun _ => rfl)
    ((dualRho Γ Γ' α n).comp (Subgroup.inclusion hS)) (fun _ => rfl)
    ((gammaRho Γ' n).comp (Subgroup.inclusion hS')) (fun _ => rfl) _ c'

end TernaryPeriodPolynomials.Argument.EisensteinDual
