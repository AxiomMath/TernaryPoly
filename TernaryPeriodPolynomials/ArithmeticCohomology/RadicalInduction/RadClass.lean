module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadDual
public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.FaceCan

@[expose] public section


/-!
# The Levi-equivariant comparison of radical `H¹` and the sum formula for the Koszul pairing

Formalized by Claude Sonnet 5.5.

`φ = EdgeNat.modMor` (coefficient comparison `ev` at the base point of `S/Stab`, radical map `r ↦ r^{m₀}`, Levi map `Γ(M) ↪ Γ(N)`) and its contragredient `φ'`.  `radPairing_ind` is the hypothesis `hE` of
`cuspidal_pairing_phi` with the constant `c = 1`: the Koszul pairing of the radical `H¹` of `Fun(S/Stab, E)` is the sum over `Γ(N)/Γ(M)` of the pulled-back Koszul pairings of the radical `H¹` of `E`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open scoped Classical

variable {S E₂ : Type} [Group S] [Group E₂] {N M : ℕ} {ext : GroupExtension RadicalLattice S (Gamma N)} {s : ext.Splitting}
  {Stab : Subgroup S} {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ (Gamma M)} {s' : ext'.Splitting}
  {hle : Gamma M ≤ Gamma N} {m0 : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

variable (hc : Compat ext s Stab α ext' s' (Subgroup.inclusion hle) m0) (ρ : Representation ℂ S E)

/-- The comparison `Res_ιL H¹(N, Fun(S/Stab, E)) ⟶ H¹(N', E)`. -/
def phiRad : Rep.res (Subgroup.inclusion hle) (splitRadicalH1Representation s (WI ext Stab ρ)) ⟶
    splitRadicalH1Representation s' (AS α ρ) :=
  EdgeNat.modMor s s' α (Subgroup.inclusion hle) (powMonoidHom m0) hc.inl_eq hc.split_eq (WI ext Stab ρ) (AS α ρ)
    (evT ext Stab α ρ) (evT_hT α hc.mem_stab ρ)

/-- The comparison for the contragredient. -/
def phiRadD : Rep.res (Subgroup.inclusion hle) (splitRadicalH1Representation s (dualRepG (WI ext Stab ρ))) ⟶
    splitRadicalH1Representation s' (dualRepG (AS α ρ)) :=
  EdgeNat.modMor s s' α (Subgroup.inclusion hle) (powMonoidHom m0) hc.inl_eq hc.split_eq (dualRepG (WI ext Stab ρ))
    (dualRepG (AS α ρ)) (evTD ext Stab α ρ) (evTD_hT hc.mem_stab ρ)

instance [Fintype (YN ext Stab)] [FiniteDimensional ℂ E] : FiniteDimensional ℂ (WI ext Stab ρ) :=
  inferInstanceAs (FiniteDimensional ℂ (YN ext Stab → E))

end TernaryPeriodPolynomials.Argument.RadicalInduction
