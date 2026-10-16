module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.CuspidalDim

@[expose] public section


/-!
# The Poincaré-Lefschetz pairing on cuspidal cohomology of `Γ(N)`

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

"On the base, the long exact sequence for a compactified modular curve identifies cuspidal cohomology with the image of compactly supported
cohomology. Poincaré-Lefschetz duality identifies the transpose of this compact-support-to-ordinary map with the corresponding map for the
dual local system. The induced pairing between the two images is therefore nondegenerate."

For `Γ = Γ(N)`, `N ≥ 3`, finite dimensional `Γ`-modules `A`, `A'` with a perfect invariant pairing `C : A × A' → ℂ`:
`cuspidal_pairing_exists` constructs a pairing `𝒞(A) × 𝒞(A') → ℂ`, where `𝒞(·) ⊆ H¹(Γ(N), ·)` is the literal cuspidal subspace
(classes with zero restriction to the stabilizer of every cusp), perfect in both arguments, given on a class `[mTw Φ]` (`Φ` a normalized
twisted cusp function, i.e. a lift to compactly supported cohomology `H¹_c ∋ dΦ`) and a cochain `G` of `A'` with cuspidal class by the
Poincaré-Lefschetz duality pairing `⟨dΦ, G⟩`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol Module
open scoped Classical

/-- **Descent of a bilinear form along two surjections.** -/
theorem exists_descent {X Y U V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (π₁ : X →ₗ[ℂ] U) (π₂ : Y →ₗ[ℂ] V) (h1 : Function.Surjective π₁) (h2 : Function.Surjective π₂)
    (hl : ∀ x, π₁ x = 0 → ∀ y, B x y = 0) (hr : ∀ y, π₂ y = 0 → ∀ x, B x y = 0) :
    ∃ B' : U →ₗ[ℂ] V →ₗ[ℂ] ℂ, ∀ x y, B' (π₁ x) (π₂ y) = B x y := by
  let e₁ := LinearMap.quotKerEquivOfSurjective π₁ h1
  let e₂ := LinearMap.quotKerEquivOfSurjective π₂ h2
  -- descend in the second variable
  let B1 : (Y ⧸ LinearMap.ker π₂) →ₗ[ℂ] X →ₗ[ℂ] ℂ :=
    (LinearMap.ker π₂).liftQ B.flip (fun y hy => LinearMap.ext fun x => hr y (LinearMap.mem_ker.mp hy) x)
  -- descend in the first variable
  let B2 : (X ⧸ LinearMap.ker π₁) →ₗ[ℂ] (Y ⧸ LinearMap.ker π₂) →ₗ[ℂ] ℂ :=
    (LinearMap.ker π₁).liftQ B1.flip (fun x hx => LinearMap.ext fun v => by
      induction v using Submodule.Quotient.induction_on with
      | H y => exact hl x (LinearMap.mem_ker.mp hx) y)
  refine ⟨(B2.comp e₁.symm.toLinearMap).compl₂ e₂.symm.toLinearMap, fun x y => ?_⟩
  have hx : e₁.symm (π₁ x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hy : e₂.symm (π₂ y) = Submodule.Quotient.mk y := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, hy]
  rfl

section Main

variable {N : ℕ}

/-- **The Poincaré-Lefschetz pairing of cuspidal cohomology** of `Γ(N)` (`N ≥ 3`): perfect in both arguments, given by the duality
pairing `⟨dΦ, G⟩` of a lift `dΦ` to compactly supported cohomology with a cochain `G` of the dual module. -/
theorem cuspidal_pairing_exists (hN : 3 ≤ N) (A A' : Rep ℂ (gammaNGL N)) [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (C : Coupling A.ρ A'.ρ) :
    ∃ B : cuspidalSub A →ₗ[ℂ] cuspidalSub A' →ₗ[ℂ] ℂ,
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ (Φ : Tw A.ρ) (G : C1 A'.ρ) (_ : Φ.1 cusp1 = 0) (hG : cohMap A' G ∈ cuspidalSub A'),
        B ⟨mTw A Φ, mTw_mem_cuspidal A Φ⟩ ⟨cohMap A' G, hG⟩ = pV C (gammaNFareyData hN) (bdryTw A.ρ hN Φ) G := by
  have := c1_finite (ρ := A.ρ) (gammaNFareyData hN)
  have := c1_finite (ρ := A'.ρ) (gammaNFareyData hN)
  obtain ⟨-, hKA, hKA'⟩ := cuspidal_dims hN A A' C
  let π₁ : Tn A.ρ →ₗ[ℂ] cuspidalSub A :=
    LinearMap.codRestrict (cuspidalSub A) ((mTw A).comp (Tn A.ρ).subtype) (fun Φ => mTw_mem_cuspidal A Φ.1)
  let π₂ : Pperp hN C →ₗ[ℂ] cuspidalSub A' :=
    LinearMap.codRestrict (cuspidalSub A') ((cohMap A').comp (Pperp hN C).subtype)
      (fun G => (cohMap_mem_cuspidal_iff hN A A' C).mpr G.2)
  have h1 : Function.Surjective π₁ := by
    rintro ⟨x, hx⟩
    obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN A hx
    exact ⟨⟨Φ, mem_Tn.mpr h0⟩, Subtype.ext hΦ⟩
  have h2 : Function.Surjective π₂ := by
    rintro ⟨x, hx⟩
    obtain ⟨G, rfl⟩ := cohMap_surjective A' (gammaNFareyData hN) x
    exact ⟨⟨G, (cohMap_mem_cuspidal_iff hN A A' C).mp hx⟩, rfl⟩
  let Bt : Tn A.ρ →ₗ[ℂ] Pperp hN C →ₗ[ℂ] ℂ :=
    (pV C (gammaNFareyData hN)).compl₁₂ (hT hN A.ρ) (Pperp hN C).subtype
  have hBt : ∀ Φ G, Bt Φ G = pV C (gammaNFareyData hN) (hT hN A.ρ Φ) G.1 := fun _ _ => rfl
  have hker : ∀ Φ : Tn A.ρ, π₁ Φ = 0 → hT hN A.ρ Φ ∈ LinearMap.range (bdryEq hN A.ρ) := by
    intro Φ hΦ
    rw [← map_hT_ker_gq hN A]
    refine ⟨Φ, ?_, rfl⟩
    have hm : mTw A Φ.1 = 0 := congrArg Subtype.val hΦ
    change (cohIso A (gammaNFareyData hN)).symm (mTw A Φ.1) = 0
    rw [hm, map_zero]
  have hl : ∀ Φ, π₁ Φ = 0 → ∀ G, Bt Φ G = 0 := by
    intro Φ hΦ G
    rw [hBt]
    exact (mem_perp _).mp G.2 _ (hker Φ hΦ)
  have hr : ∀ G, π₂ G = 0 → ∀ Φ, Bt Φ G = 0 := by
    intro G hG Φ
    rw [hBt]
    have hc : cohMap A' G.1 = 0 := congrArg Subtype.val hG
    obtain ⟨H, hH⟩ := (cohMap_eq_zero_iff A' _).mp hc
    rw [← hH, pV_delta, LinearMap.mem_ker.mp (range_hT_le hN A ⟨Φ, rfl⟩)]
    simp [pW]
  obtain ⟨B', hB'⟩ := exists_descent (X := Tn A.ρ) (Y := Pperp hN C) (U := cuspidalSub A) (V := cuspidalSub A')
    Bt π₁ π₂ h1 h2 hl hr
  refine ⟨B', ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨Φ, rfl⟩ := h1 x
    have hv : ∀ v' ∈ perp (pV C (gammaNFareyData hN)) (LinearMap.range (bdryEq hN A.ρ)),
        pV C (gammaNFareyData hN) (hT hN A.ρ Φ) v' = 0 := by
      intro v' hv'
      have := hB' Φ ⟨v', hv'⟩
      rw [hBt] at this
      rw [← this]
      exact hx _
    have hmem := mem_of_perp_perp (pV C (gammaNFareyData hN)) (pV_perfect_left hN A A' C) (pV_perfect_right hN A A' C)
      (LinearMap.range (bdryEq hN A.ρ)) hv
    rw [← map_hT_ker_gq hN A] at hmem
    obtain ⟨Φ', hΦ', he⟩ := hmem
    have : Φ' = Φ := hT_inj hN A he
    subst this
    have : (cohIso A (gammaNFareyData hN)).symm (mTw A Φ'.1) = 0 := hΦ'
    have hm : mTw A Φ'.1 = 0 := by simpa using this
    exact Subtype.ext hm
  · intro y hy
    obtain ⟨G, rfl⟩ := h2 y
    have hG : ∀ F ∈ LinearMap.ker (dc A.ρ), pV C (gammaNFareyData hN) F G.1 = 0 := by
      intro F hF
      rw [← hKA] at hF
      obtain ⟨Φ, rfl⟩ := hF
      have := hB' Φ G
      rw [hBt] at this
      rw [← this]
      exact hy _
    have hG' : G.1 ∈ LinearMap.range (delta A'.ρ) := by
      rw [← perp_ker_dc hN A A' C, mem_perp]
      exact hG
    apply Subtype.ext
    exact (cohMap_eq_zero_iff A' _).mpr hG'
  · intro Φ G h0 hG
    have := hB' ⟨Φ, mem_Tn.mpr h0⟩ ⟨G, (cohMap_mem_cuspidal_iff hN A A' C).mp hG⟩
    exact this

end Main

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
