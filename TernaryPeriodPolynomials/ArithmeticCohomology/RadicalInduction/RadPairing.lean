module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.RadClass

@[expose] public section


/-!
# The sum formula for the Koszul pairing of induced radical classes

Formalized by Claude Sonnet 5.5.

**`radPairing_ind`**: the hypothesis `hE` of `cuspidal_pairing_phi` for `V₁ = H¹(N, Fun(S/Stab, E))`, `V = H¹(N', E)`, with the constant `1`.
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

include hc in
theorem phiRad_apply (c : groupCohomology.cocycles₁ (Rep.res ext.inl (WI ext Stab ρ))) :
    (phiRad hc ρ).hom (groupCohomology.H1π _ c) = groupCohomology.H1π _ (pbCoc hc ρ c) := by
  unfold phiRad pbCoc EdgeNat.modMor EdgeNat.radH1Map oneCocyclePullbackMorphism
  exact oneCocyclePullbackH1_apply _ _ _ _ _ c

include hc in
theorem phiRadD_apply (c : groupCohomology.cocycles₁ (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) :
    (phiRadD hc ρ).hom (groupCohomology.H1π _ c) = groupCohomology.H1π _ (pbCocD hc ρ c) := by
  unfold phiRadD pbCocD EdgeNat.modMor EdgeNat.radH1Map oneCocyclePullbackMorphism
  exact oneCocyclePullbackH1_apply _ _ _ _ _ c

theorem range_incl (hle : Gamma M ≤ Gamma N) : (Subgroup.inclusion hle).range = subM N M := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact h.2
  · intro hg
    exact ⟨⟨g.1, hg⟩, rfl⟩

section Rad

variable [NeZero m0] [Fintype (YN ext Stab)] [Fintype (Gamma N ⧸ subM N M)] [FiniteDimensional ℂ E]

include hc in
/-- **The sum formula for the radical Koszul pairing, with the constant `1`.** -/
theorem radPairing_ind
    (a : groupCohomology.H1 (Rep.res ext.inl (WI ext Stab ρ)))
    (b : groupCohomology.H1 (Rep.res ext.inl (dualRepG (WI ext Stab ρ)))) :
    radPairingOf (ext := ext) (perfectInv_dual (WI ext Stab ρ)) a b =
      1 * ∑ x : Gamma N ⧸ subM N M, radPairingOf (ext := ext') (perfectInv_dual (AS α ρ))
        ((phiRad hc ρ).hom ((splitRadicalH1Representation s (WI ext Stab ρ)).ρ (Quotient.out x)⁻¹ a))
        ((phiRadD hc ρ).hom ((splitRadicalH1Representation s (dualRepG (WI ext Stab ρ))).ρ (Quotient.out x)⁻¹ b)) := by
  induction a using groupCohomology.H1_induction_on with
  | h c =>
    induction b using groupCohomology.H1_induction_on with
    | h c' =>
      rw [radPairingOf_spec, one_mul]
      have hx : ∀ x : Gamma N ⧸ subM N M, radPairingOf (ext := ext') (perfectInv_dual (AS α ρ))
          ((phiRad hc ρ).hom ((splitRadicalH1Representation s (WI ext Stab ρ)).ρ (Quotient.out x)⁻¹ (groupCohomology.H1π _ c)))
          ((phiRadD hc ρ).hom ((splitRadicalH1Representation s (dualRepG (WI ext Stab ρ))).ρ (Quotient.out x)⁻¹ (groupCohomology.H1π _ c'))) =
          PhiC (Rep.res ext'.inl (AS α ρ)) (Rep.res ext'.inl (dualRepG (AS α ρ))) (Module.Dual.eval ℂ (AS α ρ))
            (acoc (s := s) (Lsub := subM N M) hc ρ x c) (acocD (s := s) (Lsub := subM N M) hc ρ x c') := by
        intro x
        change radPairingOf (ext := ext') (perfectInv_dual (AS α ρ))
          ((phiRad hc ρ).hom (splitRadicalH1Action s (WI ext Stab ρ) (Quotient.out x)⁻¹ (groupCohomology.H1π _ c)))
          ((phiRadD hc ρ).hom (splitRadicalH1Action s (dualRepG (WI ext Stab ρ)) (Quotient.out x)⁻¹ (groupCohomology.H1π _ c'))) = _
        rw [splitRadicalH1Action_apply, splitRadicalH1Action_apply, phiRad_apply, phiRadD_apply, radPairingOf_spec]
        rfl
      rw [Finset.sum_congr rfl (fun x _ => hx x)]
      exact phiC_ind_dual hc ρ (range_incl hle) c c'

end Rad

end TernaryPeriodPolynomials.Argument.RadicalInduction
