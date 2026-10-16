module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LAHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineLocalOp

@[expose] public section


/-!
# `localOp` of `T_p` at the twisted good-line cusp

The transport `ψ` from the good-line cusp to the stabilizer `Λ₁` of the good line intertwines the
local Hecke operator of any away-from-three correspondence `t` of `Γ diag(p,1,1) Γ` with the
operator of the explicit correspondence `goodLineCosets p`, for every coefficient system (the
argument only uses the group-theoretic fact `rExpl_double`).  Composing with the twisted binary edge
turns `localOp` into `sgnP p • 1 + (p^{n+2})⁻¹ • T_p`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.HeckeEigen.Satake

namespace TernaryPeriodPolynomials.Twisted

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LocalHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.LineCoordinates
open TernaryPeriodPolynomials.Spectral.GoodLineCosets
open TernaryPeriodPolynomials.Spectral.IdentityPlaneLocalOp

/-- **Transport from the good-line cusp to `Λ₁`**, for the character `χ`. -/
def psiLT (n : ℕ) (χ : RankOneCharacter) :
    CuspH2 n χ .line true →ₗ[ℂ] H2 Λ₁ (rationalCoefficientComponent n χ) :=
  stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) gammaL (cuspFlag .line true)
    (QuotientGroup.mk rationalGoodLine) gammaL_smul

theorem psiLT_injective (n : ℕ) (χ : RankOneCharacter) : Function.Injective (psiLT n χ) := by
  intro y y' h
  have e1 := transport_inverse rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul y
  have e2 := transport_inverse rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul y'
  change stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul y =
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul y' at h
  rw [← e1, ← e2, h]

/-- **Transport of `localOp` of `T_p` at the good-line cusp.** -/
theorem transport_localOpT (n : ℕ) (χ : RankOneCharacter) (p : Nat.Primes) (t : HeckeCorrespondence)
    (ht : AwayThree t) (hg : t.g = gP p.property) (hp3 : p.val ≠ 3)
    (y : CuspH2 n χ .line true) :
    psiLT n χ (localOp n χ t ht .line true y) =
      cohomologyAction (rationalCoefficientComponent n χ) (goodLineCosets p) (psiLT n χ y) := by
  classical
  have htr := transports_cuspFlag t ht .line true
  set S' := HeckeShapiro.localCorrespondence htr
  have hex : ∀ s : (goodLineCosets p).representatives, ∃ s' ∈ S'.representatives,
      (gammaL.val⁻¹ * s.val * gammaL.val)⁻¹ * s' ∈ fixedPointLevel rationalLevel (cuspFlag .line true) := by
    rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨a, b, hab⟩ := rExpl_double p hp3 i
    obtain ⟨r, hr, hrl⟩ := t.complete (gammaL⁻¹ * a) (b * gammaL)
    rw [hg] at hrl
    have hrl' : r⁻¹ * (gammaL.val⁻¹ * rExpl p i * gammaL.val) ∈ rationalLevel := by
      rw [hab]
      simpa [mul_assoc] using hrl
    refine ⟨HeckeShapiro.shifted htr r, ?_, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [HeckeShapiro.localCorrespondence_representatives]
      exact Finset.mem_image_of_mem _ hr
    · have h := rationalLevel.mul_mem (rationalLevel.inv_mem hrl') (HeckeShapiro.transporter_mem htr r)
      have he : (gammaL.val⁻¹ * rExpl p i * gammaL.val)⁻¹ * HeckeShapiro.shifted htr r =
          (r⁻¹ * (gammaL.val⁻¹ * rExpl p i * gammaL.val))⁻¹ * HeckeShapiro.transporter htr r := by
        simp only [HeckeShapiro.shifted]
        group
      rw [he]
      exact h
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (conj_fixes _ (rExpl_fixes p i)))
        (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  let F : (goodLineCosets p).representatives → S'.representatives := fun s => ⟨f s, hfmem s⟩
  have hinj : Function.Injective F := by
    intro s₁ s₂ h
    apply Subtype.ext
    apply (goodLineCosets p).disjoint s₁.val s₁.property s₂.val s₂.property
    have h12 := (fixedPointLevel rationalLevel (cuspFlag .line true)).mul_mem (hf s₁)
      ((fixedPointLevel rationalLevel (cuspFlag .line true)).inv_mem (hf s₂))
    have hF : f s₁ = f s₂ := congrArg Subtype.val h
    rw [hF] at h12
    have h3 := conj_mem_Λ₁ _ h12
    convert h3 using 1
    group
  have hcard : S'.representatives.card ≤ (goodLineCosets p).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    rw [card_representatives p.property t ht hg]
    change _ ≤ (Finset.univ.image (rExpl p)).card
    rw [Finset.card_image_of_injective _ (rExpl_injective p), Finset.card_univ, Fintype.card_sum,
      Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    apply le_of_eq
    ring
  have hbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective F hinj) ?_⟩
    simpa only [Fintype.card_coe] using hcard
  exact transport_cohomologyAction rationalLevel (rationalCoefficientComponent n χ) gammaL
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) gammaL_smul (goodLineCosets p) S'
    (Equiv.ofBijective F hbij) hf y


/-- **The local `T_p` at the twisted good-line cusp, on the binary edge.**  For every
away-from-three correspondence `t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`) and `n > 0`,
`E(ψ(localOp t y)) = sgnP p • E(ψ y) + (p^{n+2})⁻¹ • T_p E(ψ y)` with `E = edgeH2LT` the injective
binary edge into `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` and `ψ = psiLT` the injective transport to `Λ₁`. -/
theorem edgeH2LT_localOp (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (p : Nat.Primes)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP p.property) (hp3 : p.val ≠ 3)
    (y : CuspH2 n χ .line true) :
    edgeH2LT n χ hχ hn (psiLT n χ (localOp n χ t ht .line true y)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2LT n χ hχ hn (psiLT n χ y) +
        ((p.val : ℂ) ^ (n + 2))⁻¹ •
          LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p (edgeH2LT n χ hχ hn (psiLT n χ y)) := by
  rw [transport_localOpT n χ p t ht hg hp3 y]
  exact edgeH2LT_hecke n χ hχ p hn _

/-- The same for the `T_p` correspondence `TpExistence.tp p`. -/
theorem edgeH2LT_localOp_tp (n : ℕ) (χ : RankOneCharacter)
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n) (p : Nat.Primes)
    (hp3 : p.val ≠ 3) (y : CuspH2 n χ .line true) :
    edgeH2LT n χ hχ hn
        (psiLT n χ (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3) .line true y)) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2LT n χ hχ hn (psiLT n χ y) +
        ((p.val : ℂ) ^ (n + 2))⁻¹ •
          LevelOneHeckeH1.arithmeticHecke (n + 1) (-1) p (edgeH2LT n χ hχ hn (psiLT n χ y)) :=
  edgeH2LT_localOp n χ hχ hn p _ _ (TpExistence.tp_g p) hp3 y

end TernaryPeriodPolynomials.Twisted
