module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa

@[expose] public section


/-!
# Lemma B.1, boundary route, milestone M1: `res_H` of a corestricted neat class

`kEquivGeneric_corN`: for the level-group duality `kEquivGeneric` (`FiberModel/KLevelGeneric`), the value on a
corestricted neat class `corN z` is the average `avg σ M.ρ N (psiGen z)` of the neat-level functional.
`H3_G_equiv_corN`, `resHLit_corN`: `res_H` of `corN z` is the literal `a = 0` residue of
`(1/[G:Γ(6)]) ∑_{q ∈ G/Γ(6)} ρ(q) Θ_N(z)(q⁻¹ • σ₀)`, `σ₀` the identity apartment.  This reduces the right hand
side of `PHCompat` to the neat-level duality `Θ_N = groupOrdinaryIso` evaluated on the `G/Γ(6)`-translates of the
identity apartment; no geometry beyond the library's neat-level duality is used.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly IntegralGL3Congruence CategoryTheory
open TernaryPeriodPolynomials.Argument.GroupHomology

section
variable {Kp : Type} [Group Kp] {N : Subgroup Kp} {e : N ≃* ↥principalSix}
  {σ : Representation ℚ Kp OrdinaryIncidenceChains.Cycles} {M : Rep.{0} ℚ Kp}
  [N.Normal] [N.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem symm_ofBijective_apply' {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] {f : M₁ →ₗ[R] M₂} (hf : Function.Bijective f) {x : M₂} {y : M₁}
    (h : f y = x) : (LinearEquiv.ofBijective f hf).symm x = y := by
  rw [LinearEquiv.symm_apply_eq]
  exact h.symm

theorem kEquivGeneric_corN
    (hσ : ∀ n : N, σ n = SymmetricSpaceBoundaryIncidenceHomology.ordinaryCyclesRep.ρ (e n))
    (h : NeatDualityEquivariantGen N e σ M) (z : groupHomology (Rep.res N.subtype M) 3) :
    ((kEquivGeneric hσ h (corN N M 3 z) : homKGen σ M) : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] M) =
      GroupHomology.avg σ M.ρ N (psiGen N e M z) := by
  unfold kEquivGeneric
  simp only [LinearEquiv.trans_apply]
  erw [symm_ofBijective_apply' _ (y := ⟨avgN N M 3 z, z, rfl⟩) (corN_avgN_gen z)]
  exact psiGen_avgN h z

end

end TernaryPeriodPolynomials.Argument.FiberModel

namespace TernaryPeriodPolynomials.Argument.AppendixBResidue

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence CategoryTheory
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology TernaryPoly.SinglePoleCoordinate

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **`H3_G_equiv` on a corestricted neat class is the average of the neat-level functional.** -/
theorem H3_G_equiv_corN (n : ℕ) (z : groupHomology (Rep.res principalSix.subtype (ResRep n)) 3) :
    ((H3_G_equiv n (corN principalSix (ResRep n) 3 z) : OrdinaryFullCoefficient.ResidueHom n (-1)) :
        OrdinaryIncidenceChains.Cycles →ₗ[ℚ] ResRep n) =
      avg stG (ResRep n).ρ principalSix
        (psiGen principalSix (MulEquiv.refl ↥principalSix) (ResRep n) z) := by
  unfold H3_G_equiv dualityG
  rw [LinearEquiv.trans_apply]
  exact kEquivGeneric_corN (fun n => stG_principal n) (neatDualityG n) z

/-- **`res_H` of a corestricted neat class**: the `a = 0` residue of the averaged neat functional on the identity
apartment, `(1/[G:Γ(6)]) ∑_{g ∈ G/Γ(6)} lit₀(comp₀(ρ(g) Θ_N(z)(g⁻¹ • σ₀)))`. -/
theorem resHLit_corN (n : ℕ) (z : groupHomology (Rep.res principalSix.subtype (ResRep n)) 3) :
    ((resHLit n (corN principalSix (ResRep n) 3 z) : OrdinaryResiduePeriod.periodSpace (n + 1)) :
        BinaryV (n + 1)) =
      SinglePoleCoordinate.literalFiberMap n 0 (SinglePoleSupport.component n (OrdinaryResidueSupport.axis 0)
        (((Fintype.card (IntegralGL ⧸ principalSix) : ℚ)⁻¹) •
          ∑ q : IntegralGL ⧸ principalSix,
            (ResRep n).ρ q.out
              (psiGen principalSix (MulEquiv.refl ↥principalSix) (ResRep n) z
                (stG q.out⁻¹ (OrdinaryApartmentPresentation.frameCycle 1))))) := by
  unfold resHLit
  rw [LinearMap.comp_apply, resH_val]
  have h := congrArg (fun φ => φ (OrdinaryApartmentPresentation.frameCycle 1)) (H3_G_equiv_corN n z)
  rw [avg_eq_sum] at h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, actL_apply] at h
  exact congrArg (fun v => SinglePoleCoordinate.literalFiberMap n 0
    (SinglePoleSupport.component n (OrdinaryResidueSupport.axis 0) v)) h

end TernaryPeriodPolynomials.Argument.AppendixBResidue
