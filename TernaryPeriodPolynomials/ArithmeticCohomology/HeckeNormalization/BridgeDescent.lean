module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.HeckeHom

@[expose] public section


/-!
# L6a: descent of a `β`-killing `Γ`-map `P1 → Sym^d` to a Hom for the exponent `-1`

Formalized by Claude Sonnet 5.5.

`piL` is onto with kernel `betaL (P0)` (`FareyKernel.exists_bdry_preimage`), so every `Φ ∈ PhiSp d` is `F ∘ piL` for a
unique `F : St → Sym^d`; `F` is equivariant for `homogeneousAction d (-1)` because `stD g = detQ g • action g` and
`homogeneousAction d (-1) (integral g) = detQ g • integralAction d 0 g` (`rho_neg_one`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface

open CategoryTheory TernaryPoly TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology

theorem piT_swap (x : PE) : piT.hom (swapMap.hom x) = - piT.hom x := by
  have key : piT.hom.toLinearMap ∘ₗ swapMap.hom.toLinearMap = - piT.hom.toLinearMap := by
    refine MonoidAlgebra.lhom_ext' fun q => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply, LinearMap.neg_apply]
    change piT.hom (swapMap.hom (MonoidAlgebra.single q 1)) = - piT.hom (MonoidAlgebra.single q 1)
    rw [swapMap_single, piT_single, piT_single, edgeSym_swap]
    simp
  exact LinearMap.congr_fun key x

theorem piL_surjective : Function.Surjective piL := by
  intro σ
  obtain ⟨x, hx⟩ := piT_surjective σ
  refine ⟨⟨antiLin x, antiLin_mem x⟩, ?_⟩
  change piT.hom (antiLin x) = σ
  rw [antiLin_apply, map_smul, map_sub, piT_swap, ← hx]
  change (1 / 2 : ℚ) • (piT.hom x - - piT.hom x) = piT.hom x
  module

theorem ker_piL (x : P1) (hx : piL x = 0) : ∃ t : P0, betaL t = x := by
  obtain ⟨w, hw⟩ := exists_bdry_preimage (x : PE) x.2 hx
  exact ⟨w, Subtype.ext hw⟩

theorem det_integral_eq (γ : IntegralGL) : ((integral γ).val.det : ℚ) = detQ γ := by
  have h : (integral γ).val.det = (γ.val.det : ℚ) := by
    change (γ.val.map (Int.castRingHom ℚ)).det = _
    exact (RingHom.map_det (Int.castRingHom ℚ) γ.val).symm
  rw [h]
  simp [detQ, Matrix.GeneralLinearGroup.val_det_apply]

theorem rho_neg_one (d : ℕ) (γ : IntegralGL) (q : BinaryModularSymbolCoefficients.HomogeneousPoly d) :
    BinaryModularSymbolCoefficients.homogeneousAction d (-1) (integral γ) q =
      detQ γ • (Dplain d).ρ γ q := by
  have h := TernaryPeriodPolynomials.Argument.AppendixBResidue.homogeneousAction_twist d 0 (-1) (integral γ) q
  rw [zero_add] at h
  rw [h, det_integral_eq]
  have hs : detQ γ ^ (-1 : ℤ) = detQ γ := by
    rw [zpow_neg_one]
    have := detQ_mul_self γ
    exact inv_eq_of_mul_eq_one_right this
  rw [hs]
  rfl

/-- **L6a.** A `Γ`-map `P1 → Sym^d` killing `β` descends to a `Γ`-equivariant `F : St → Sym^d` for the exponent `-1`. -/
theorem descend (d : ℕ) (Φ : P1 →ₗ[ℚ] (Dplain d)) (hΦ : Φ ∈ PhiSp d) :
    ∃ F : PeriodHom d, ∀ x : P1, Φ x = F.val (piL x) := by
  obtain ⟨h1, h2⟩ := hΦ
  have hker : LinearMap.ker piL ≤ LinearMap.ker Φ := by
    intro x hx
    obtain ⟨t, rfl⟩ := ker_piL x hx
    exact h2 t
  let F0 : St →ₗ[ℚ] (Dplain d) :=
    ((LinearMap.ker piL).liftQ Φ hker) ∘ₗ (LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm.toLinearMap
  have hF0 : ∀ x : P1, F0 (piL x) = Φ x := by
    intro x
    change ((LinearMap.ker piL).liftQ Φ hker) ((LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm (piL x)) = _
    have : (LinearMap.quotKerEquivOfSurjective piL piL_surjective).symm (piL x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    rw [this]; rfl
  refine ⟨⟨F0, ?_⟩, fun x => (hF0 x).symm⟩
  intro g c
  obtain ⟨x, rfl⟩ := piL_surjective c
  have hπ : piL (P1.ρ g x) = stD g (piL x) := by
    have := Rep.hom_comm_apply piT g (x : PE)
    exact this
  have e1 : action (integral g) (piL x) = detQ g • piL (P1.ρ g x) := by
    rw [hπ, stD_apply, smul_smul, detQ_mul_self, one_smul]
  change F0 (action (integral g) (piL x)) = _
  rw [e1, map_smul, hF0, h1, rho_neg_one, hF0]

end TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
