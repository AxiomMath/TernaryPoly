module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Package
public import TernaryPeriodPolynomials.EisensteinSeries.Class.DeRhamNatural

@[expose] public section


/-!
# Restriction of the class of an equivariant form to a subgroup

Paper: "the
restriction `r_R` is realized by group restriction" (the inclusion `Γ_R ↪ Γ`, the equivariant map
`i_{R,t}` of the boundary model into `𝒳`).

For subgroups `H ≤ Γ` of `SL₃(ℤ)` acting on `Ω` through `planeAct ∘ realMat`, the identity of `Ω` is
an `H`-to-`Γ` equivariant map (`incl`), and by the naturality of `ZigZag.deRhamClass`
(`DeRhamNatural.deRhamClass_natural`) the class of the family `W` regarded `H`-equivariantly is the
restriction `H²(Γ, E_n) → H²(H, E_n)` of its class (`deRhamClass_restrict`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3

variable {Γ H : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)} {n : ℕ}

/-- The coefficient representations are compatible with the inclusion `H ≤ Γ`. -/
theorem gammaRho_incl (hH : H ≤ Γ) (g : H) :
    gammaRho H n g = gammaRho Γ n (Subgroup.inclusion hH g) := by
  apply LinearMap.ext
  intro q
  apply Coef.toPoly_injective
  rw [toPoly_gammaRho, toPoly_gammaRho]
  rfl

/-- The identity of `Ω` as an `H`-to-`Γ` equivariant map along the inclusion. -/
def inclMap (hH : H ≤ Γ) :
    EquivMap isOpen_Omega isOpen_Omega (gammaAct H) (gammaAct Γ) (Subgroup.inclusion hH) where
  φ := id
  smooth := contDiffOn_id
  mapsTo := Set.mapsTo_id _
  equiv _ _ _ := rfl

theorem pullInv_inclMap (W : InvComponents Γ n) (hH : H ≤ Γ) :
    pullInv (inclMap hH) (gammaRho_incl hH) W.toInv = (W.restrict hH).toInv := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (pullBack isOpen_Omega (inclMap hH).smooth (inclMap hH).mapsTo 2 W.form :
    RawForm (Fin 5 → ℝ) (Coef n) 2) x = ((W.restrict hH).form : RawForm (Fin 5 → ℝ) (Coef n) 2) x
  rw [pullBack_apply isOpen_Omega _ _ _ hx, InvComponents.form_apply _ hx]
  change pullRaw id (W.form : RawForm (Fin 5 → ℝ) (Coef n) 2) x = _
  rw [pullRaw_id, W.form_apply hx]
  rfl

/-- **Restriction of the class of an equivariant form to a subgroup**: the class of `W`, regarded
as an `H`-equivariant form, is the image of its class under `H²(Γ, E_n) → H²(H, E_n)`. -/
theorem deRhamClass_restrict (W : InvComponents Γ n) (hH : H ≤ Γ) :
    ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct H) (gammaRho H n)
        (W.restrict hH).toInv =
      (groupCohomology.map (Subgroup.inclusion hH)
          (resMor (Subgroup.inclusion hH) (gammaRho H n) (gammaRho Γ n) (gammaRho_incl hH)) 2).hom
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ)
          (gammaRho Γ n) W.toInv) := by
  rw [← pullInv_inclMap W hH]
  exact deRhamClass_natural (inclMap hH) convex_Omega Omega_nonempty convex_Omega Omega_nonempty
    (gammaRho_incl hH) W.toInv

end TernaryPeriodPolynomials.Argument.EisensteinClass
