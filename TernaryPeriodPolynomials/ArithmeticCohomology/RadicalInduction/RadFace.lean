module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadPairing

@[expose] public section


/-!
# The canonical face pairing and finite-index induction on the radical lattice

Formalized by Claude Sonnet 5.5.

**`facePairingCan_ind`**: let `ext : ℤ² → S → Γ(N)` be a split extension (Levi elements acting on the radical with determinant one), `α : E₂ → S` a homomorphism from a split extension `ext' : ℤ² → E₂ → Γ(M)`
(`Γ(M) ≤ Γ(N)`) whose image is the stabilizer `Stab` of the base point of the finite set `S/Stab` and which maps the radical `ℤ²` by `r ↦ r^{m₀}` and the Levi `Γ(M)` by the inclusion (`Compat`), and `ρ` a representation of
`S` on a finite-dimensional `E`.  Then the canonical face pairing of the cuspidal groups of `H¹(N, Fun(S/Stab, E))` and of its literal contragredient equals, with the constant exactly `1`, the canonical face pairing of
`𝒞(H¹(N', E))`, `𝒞(H¹(N', E^*))` after the Levi-equivariant comparisons `phiRad`, `phiRadD` (evaluation at the base point, radical map `r ↦ r^{m₀}`).  The constant is `1`: the factor `m₀²` of the transformation of the
Koszul form under the passage to the sublattice cancels the orbit size `m₀²`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open scoped Classical

variable {S E₂ : Type} [Group S] [Group E₂] {N M : ℕ} {ext : GroupExtension RadicalLattice S (Gamma N)} {s : ext.Splitting}
  {Stab : Subgroup S} {α : E₂ →* S} {ext' : GroupExtension RadicalLattice E₂ (Gamma M)} {s' : ext'.Splitting}
  {hle : Gamma M ≤ Gamma N} {m0 : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

variable (hc : Compat ext s Stab α ext' s' (Subgroup.inclusion hle) m0) (ρ : Representation ℂ S E)
  [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hdet' : ∀ A, radDet (splitRadicalInput s' A) = 1)

include hc hM hdet' in
theorem facePairingCan_ind [NeZero m0] [Fintype (YN ext Stab)] [Fintype (Gamma N ⧸ subM N M)] [FiniteDimensional ℂ E]
    (x : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (WI ext Stab ρ)))
    (y : cuspidalSubspace (Gamma N) (splitRadicalH1Representation s (dualRepG (WI ext Stab ρ)))) :
    facePairingCan hN.out s hc.det (WI ext Stab ρ) x y =
      facePairingCan hM s' hdet' (AS α ρ) (mapCusp hM hle (phiRad hc ρ) x) (mapCusp hM hle (phiRadD hc ρ) y) := by
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (WI ext Stab ρ)) := finiteDimensional_H1 (Rep.res ext.inl (WI ext Stab ρ))
  have : FiniteDimensional ℂ (splitRadicalH1Representation s (dualRepG (WI ext Stab ρ))) :=
    finiteDimensional_H1 (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))
  have : FiniteDimensional ℂ (splitRadicalH1Representation s' (AS α ρ)) := finiteDimensional_H1 (Rep.res ext'.inl (AS α ρ))
  have : FiniteDimensional ℂ (splitRadicalH1Representation s' (dualRepG (AS α ρ))) :=
    finiteDimensional_H1 (Rep.res ext'.inl (dualRepG (AS α ρ)))
  have h := cuspidal_pairing_phi (N := N) (M := M) hM hle (phiRad hc ρ) (phiRadD hc ρ)
    (radPairingOf (ext := ext) (perfectInv_dual (WI ext Stab ρ)))
    (radPairingOf (ext := ext') (perfectInv_dual (AS α ρ))) 1
    (fun γ a b => radPairingOf_levi (perfectInv_dual (WI ext Stab ρ)) s γ (hc.det γ) a b)
    (fun a ha => radPairingOf_left (perfectInv_dual (WI ext Stab ρ)) a ha)
    (fun b hb => radPairingOf_right (perfectInv_dual (WI ext Stab ρ)) b hb)
    (fun γ a b => radPairingOf_levi (perfectInv_dual (AS α ρ)) s' γ (hdet' γ) a b)
    (fun a ha => radPairingOf_left (perfectInv_dual (AS α ρ)) a ha)
    (fun b hb => radPairingOf_right (perfectInv_dual (AS α ρ)) b hb)
    (fun a b => radPairing_ind hc ρ a b)
    (facePairingCan hN.out s hc.det (WI ext Stab ρ)) (facePairingCan hM s' hdet' (AS α ρ))
    (isCupPairing_facePairingCan hN.out s hc.det (WI ext Stab ρ)) (isCupPairing_facePairingCan hM s' hdet' (AS α ρ)) x y
  rw [one_mul] at h
  exact h

end TernaryPeriodPolynomials.Argument.RadicalInduction
