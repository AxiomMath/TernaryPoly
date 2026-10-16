module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.PAHecke

@[expose] public section


/-!
# `localOp` of `T_p` at the twisted identity-plane cusp

The local correspondence of an away-from-three Hecke correspondence `t` of `Γ diag(p,1,1) Γ` at the
identity plane has the same cosets as the explicit `identityPlaneCosets p`, for every coefficient
representation.  Hence `localOp n χ t` is the explicit local operator, and by `edgeH2T_hecke` the
twisted binary edge intertwines it with `sgnP p + p^{-(n+1)} T_p` (`edgeH2T_localOp`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral

namespace TernaryPeriodPolynomials.Twisted

open LocalHecke
open TernaryPeriodPolynomials.HeckeEigen.Satake TernaryPeriodPolynomials.HeckeCommutativity
open PlaneCoordinates LevelOneCosets IdentityPlaneCosets
open CuspOrbits CuspReduction IdentityPlaneCoordinate

/-- **`localOp` of `T_p` at the identity plane is the explicit local operator**, for every character. -/
theorem localOp_identityPlaneT (n : ℕ) (χ : RankOneCharacter) (p : Nat.Primes)
    (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP p.property) (hp3 : p.val ≠ 3) :
    localOp n χ t ht .plane false = cohomologyAction (ρT n χ) (identityPlaneCosets p) := by
  classical
  have htr := transports_cuspFlag t ht .plane false
  have hex : ∀ s : (identityPlaneCosets p).representatives,
      ∃ s' ∈ (HeckeShapiro.localCorrespondence htr).representatives, s.val⁻¹ * s' ∈ Λ₀ := by
    rintro ⟨s, hs⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨a, b, hab⟩ := IdentityPlaneLocalOp.sExpl_double p hp3 i
    obtain ⟨r, hr, hrl⟩ := t.complete a b
    rw [hg, ← hab] at hrl
    refine ⟨HeckeShapiro.shifted htr r, ?_, ?_⟩
    · rw [HeckeShapiro.localCorrespondence_representatives]
      exact Finset.mem_image_of_mem _ hr
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h := rationalLevel.mul_mem (rationalLevel.inv_mem hrl)
          (HeckeShapiro.transporter_mem htr r)
        convert h using 1
        simp only [HeckeShapiro.shifted]
        group
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (IdentityPlaneLocalOp.sExpl_fixes p i))
          (HeckeShapiro.shifted_smul htr hr)
  choose f hfmem hf using hex
  have hcard : (HeckeShapiro.localCorrespondence htr).representatives.card ≤
      (identityPlaneCosets p).representatives.card := by
    rw [HeckeShapiro.localCorrespondence_representatives]
    refine (Finset.card_image_le).trans ?_
    rw [IdentityPlaneLocalOp.card_representatives p.property t ht hg]
    change _ ≤ (Finset.univ.image (sExpl p)).card
    rw [Finset.card_image_of_injective _ (sExpl_injective p), Finset.card_univ, Fintype.card_option,
      Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    apply le_of_eq
    ring
  unfold localOp
  exact (IdentityPlaneLocalOp.cohomologyAction_eq_of_injective (ρT n χ) (identityPlaneCosets p)
    (HeckeShapiro.localCorrespondence htr) (fun s => ⟨f s, hfmem s⟩) hf hcard).symm

variable (n : ℕ) (χ : RankOneCharacter) (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
  (p : Nat.Primes) (hn : 0 < n) (hodd : Odd n)

/-- **The local `T_p` at the twisted identity-plane cusp, on the binary edge.** For every
away-from-three correspondence `t` of `Γ diag(p,1,1) Γ` (`p ≠ 3`) and odd `n > 0`,
`E(localOp t x) = sgnP p • E(x) + p^{-(n+1)} T_p E(x)`, with `E` the injective binary edge
`H²(Γ_F, V_χ) → H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁰)` and `T_p` the cohomological Hecke operator. -/
theorem edgeH2T_localOp (t : HeckeCorrespondence) (ht : AwayThree t) (hg : t.g = gP p.property)
    (hp3 : p.val ≠ 3) (x : CuspH2 n χ .plane false) :
    edgeH2T n χ hχ hn hodd (localOp n χ t ht .plane false x) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2T n χ hχ hn hodd x + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p (edgeH2T n χ hχ hn hodd x) := by
  rw [localOp_identityPlaneT n χ p t ht hg hp3]
  exact edgeH2T_hecke n χ hχ p hn hodd x

/-- The same identity for the `T_p` correspondence `TpExistence.tp p`, which exists for `p ≠ 3`. -/
theorem edgeH2T_localOp_tp (hp3 : p.val ≠ 3) (x : CuspH2 n χ .plane false) :
    edgeH2T n χ hχ hn hodd (localOp n χ (TpExistence.tp p) (TpExistence.tp_awayThree p hp3)
        .plane false x) =
      ((IdentityPlaneLocalOp.sgnP p : ℤ) : ℂ) • edgeH2T n χ hχ hn hodd x + ((p.val : ℂ) ^ (n + 1))⁻¹ •
        LevelOneHeckeH1.arithmeticHecke (n + 1) 0 p (edgeH2T n χ hχ hn hodd x) :=
  edgeH2T_localOp n χ hχ p hn hodd _ _ (TpExistence.tp_g p) hp3 x

end TernaryPeriodPolynomials.Twisted
