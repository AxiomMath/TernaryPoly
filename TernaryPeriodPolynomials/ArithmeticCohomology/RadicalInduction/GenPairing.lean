module

public import TernaryPeriodPolynomials.ArithmeticCohomology.RadicalInduction.GenTheta
public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.Main

@[expose] public section


/-!
# Compatibility of the cup-form normalised cuspidal pairing with a comparison of coefficient modules over a finite-index subgroup

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

**`cuspidal_pairing_phi`**: let `Γ(M) ≤ Γ(N)`, `V₁, V₁'` finite-dimensional `Γ(N)`-modules, `V, V'` finite-dimensional `Γ(M)`-modules, `φ : Res V₁ ⟶ V`, `φ' : Res V₁' ⟶ V'` morphisms of
`Γ(M)`-modules, and suppose the pairing `e₁` of `V₁ × V₁'` is `c` times the sum over `x ∈ Γ(N)/Γ(M)` of the pulled-back pairings
`e(φ(u_x⁻¹ a), φ'(u_x⁻¹ b))`.  If `B_N`, `B_M` have the cup-form property (`IsCupPairing`) for `e₁`, `e` then `B_N(x, y) = c · B_M(φ_* x, φ'_* y)` on cuspidal classes.
`cuspidal_pairing_ind` is the case `V₁ = Fun(Γ(N)/Γ(M), V)`, `φ = ev`, `c = 1`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.RadicalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N M : ℕ} [hN : Fact (3 ≤ N)] (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) {V₁ : Rep ℂ (Gamma N)} {V : Rep ℂ (Gamma M)}
  (φ : Rep.res (Subgroup.inclusion hle) V₁ ⟶ V)

include hM in
theorem mapH1_mem (x : cuspidalSubspace (Gamma N) V₁) : mapH1 hle φ x.1 ∈ cuspidalSubspace (Gamma M) V := by
  obtain ⟨Φ, -, hΦ⟩ := exists_norm_rep hN.out V₁ x
  have hx : (thetaIso hN.out V₁).hom.hom x.1 = mTw (transRep hN.out V₁) Φ := by
    rw [← hΦ, ← cuspEquiv_val]
    simp
  rw [theta_mem_cuspidal_iff hM, mapH1_theta hM hle φ Φ x.1 hx]
  exact mTw_mem_cuspidal _ _

/-- The map on the cuspidal subspaces. -/
def mapCusp : cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma M) V :=
  ((mapH1 hle φ).comp (cuspidalSubspace (Gamma N) V₁).subtype).codRestrict _ (mapH1_mem hM hle φ)

theorem mapCusp_eq (Φ : Tw (transRep hN.out V₁).ρ) :
    mapCusp hM hle φ ((cuspEquiv hN.out V₁).symm ⟨mTw (transRep hN.out V₁) Φ, mTw_mem_cuspidal _ Φ⟩) =
      (cuspEquiv hM V).symm ⟨mTw (transRep hM V) (phiTw hM hle φ Φ), mTw_mem_cuspidal _ _⟩ := by
  apply (cuspEquiv hM V).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [cuspEquiv_val]
  refine mapH1_theta hM hle φ Φ _ ?_
  have h := cuspEquiv_val hN.out V₁ ((cuspEquiv hN.out V₁).symm ⟨mTw (transRep hN.out V₁) Φ, mTw_mem_cuspidal _ Φ⟩)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

section Main

variable [Fintype (Gamma N ⧸ subM N M)] {V₁' : Rep ℂ (Gamma N)} {V' : Rep ℂ (Gamma M)}
  (φ' : Rep.res (Subgroup.inclusion hle) V₁' ⟶ V') (e₁ : V₁ →ₗ[ℂ] V₁' →ₗ[ℂ] ℂ) (e : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (c : ℂ)

/-- The pulled-back summed pairing. -/
def eSum : V₁ →ₗ[ℂ] V₁' →ₗ[ℂ] ℂ :=
  ∑ x : Gamma N ⧸ subM N M, (e.comp (φ.hom.toLinearMap ∘ₗ (V₁.ρ (Quotient.out x)⁻¹))).compl₂
    (φ'.hom.toLinearMap ∘ₗ (V₁'.ρ (Quotient.out x)⁻¹))

omit hN in
theorem eSum_apply (a : V₁) (b : V₁') :
    eSum hle φ φ' e a b = ∑ x : Gamma N ⧸ subM N M, e (φ.hom (V₁.ρ (Quotient.out x)⁻¹ a)) (φ'.hom (V₁'.ρ (Quotient.out x)⁻¹ b)) := by
  simp [eSum, LinearMap.sum_apply]

omit hN in
theorem integ_smul' (e₂ : V₁ →ₗ[ℂ] V₁' →ₗ[ℂ] ℂ) (hc : e₁ = c • e₂) (Φ : RationalLine2 → V₁) (Φ' : RationalLine2 → V₁') (y : Tri) :
    integ e₁ Φ Φ' y = c * integ e₂ Φ Φ' y := by
  subst hc
  unfold integ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

variable [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₁'] [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']

omit [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₁'] [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
include hM in
/-- The cup form of a pairing which is `c` times a sum of pulled-back pairings. -/
theorem cupForm_eq_phi
    (hinv₁ : ∀ (γ : Gamma N) v w, e₁ (V₁.ρ γ v) (V₁'.ρ γ w) = e₁ v w) (hL₁ : ∀ v, (∀ w, e₁ v w = 0) → v = 0)
    (hR₁ : ∀ w, (∀ v, e₁ v w = 0) → w = 0)
    (hinv : ∀ (γ : Gamma M) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0)
    (hE : ∀ a b, e₁ a b = c * ∑ x : Gamma N ⧸ subM N M, e (φ.hom (V₁.ρ (Quotient.out x)⁻¹ a)) (φ'.hom (V₁'.ρ (Quotient.out x)⁻¹ b)))
    (Φ : Tw (transRep hN.out V₁).ρ) (Φ' : Tw (transRep hN.out V₁').ρ) :
    cupForm hN.out (couplingOf hN.out e₁ hinv₁ hL₁ hR₁) Φ.1 Φ'.1 =
      c * cupForm hM (couplingOf hM e hinv hL hR) (phiTw hM hle φ Φ).1 (phiTw hM hle φ' Φ').1 := by
  have he2 : e₁ = c • eSum hle φ φ' e := by
    ext a b
    simp [hE, eSum_apply]
  rw [cupForm_eq_sum, cupForm_eq_sum, Finset.mul_sum]
  have key : ∑ y ∈ (gammaNFareyData hN.out).RT.R, integ e₁ Φ.1 Φ'.1 y =
      c * ∑ y ∈ (gammaNFareyData hN.out).RT.R, integ (eSum hle φ φ' e) Φ.1 Φ'.1 y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => integ_smul' e₁ c _ he2 _ _ y)
  refine key.trans ?_
  rw [← Finset.mul_sum]
  congr 1
  obtain ⟨f, -, htw⟩ := Φ.2
  obtain ⟨f', -, htw'⟩ := Φ'.2
  refine cupForm_phi hN.out hM (gammaNGL_le hM hle) (transRep hN.out V₁).ρ (transRep hN.out V₁').ρ
    (transRep hM V).ρ (transRep hM V').ρ (eSum hle φ φ' e) e φ.hom.toLinearMap φ'.hom.toLinearMap
    (fun g a => phi_incl hM hle φ g a) (fun g a => phi_incl hM hle φ' g a)
    (fun γ v w => hinv ((gammaEquiv hM).symm γ) v w) (base N M) uLift uLift_base smul_base_iff ?_
    Φ.1 Φ'.1 f f' htw htw'
  intro a b
  rw [eSum_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rfl

include hM in
/-- **Compatibility of the cup-form normalised cuspidal pairing with a comparison over a finite-index subgroup.** -/
theorem cuspidal_pairing_phi
    (hinv₁ : ∀ (γ : Gamma N) v w, e₁ (V₁.ρ γ v) (V₁'.ρ γ w) = e₁ v w) (hL₁ : ∀ v, (∀ w, e₁ v w = 0) → v = 0)
    (hR₁ : ∀ w, (∀ v, e₁ v w = 0) → w = 0)
    (hinv : ∀ (γ : Gamma M) v w, e (V.ρ γ v) (V'.ρ γ w) = e v w) (hL : ∀ v, (∀ w, e v w = 0) → v = 0)
    (hR : ∀ w, (∀ v, e v w = 0) → w = 0)
    (hE : ∀ a b, e₁ a b = c * ∑ x : Gamma N ⧸ subM N M, e (φ.hom (V₁.ρ (Quotient.out x)⁻¹ a)) (φ'.hom (V₁'.ρ (Quotient.out x)⁻¹ b)))
    (BN : cuspidalSubspace (Gamma N) V₁ →ₗ[ℂ] cuspidalSubspace (Gamma N) V₁' →ₗ[ℂ] ℂ)
    (BM : cuspidalSubspace (Gamma M) V →ₗ[ℂ] cuspidalSubspace (Gamma M) V' →ₗ[ℂ] ℂ)
    (hBN : IsCupPairing hN.out V₁ V₁' e₁ hinv₁ hL₁ hR₁ BN) (hBM : IsCupPairing hM V V' e hinv hL hR BM)
    (x : cuspidalSubspace (Gamma N) V₁) (y : cuspidalSubspace (Gamma N) V₁') :
    BN x y = c * BM (mapCusp hM hle φ x) (mapCusp hM hle φ' y) := by
  obtain ⟨Φ, h0, rfl⟩ := exists_norm_rep hN.out _ x
  obtain ⟨Φ', h0', rfl⟩ := exists_norm_rep hN.out _ y
  rw [hBN Φ Φ' h0 h0', mapCusp_eq hM hle φ Φ, mapCusp_eq hM hle φ' Φ',
    hBM (phiTw hM hle φ Φ) (phiTw hM hle φ' Φ') (by
      show φ.hom (Φ.1 cusp1) = 0
      rw [h0]; exact map_zero _) (by
      show φ'.hom (Φ'.1 cusp1) = 0
      rw [h0']; exact map_zero _),
    cupForm_eq_phi hM hle φ φ' e₁ e c hinv₁ hL₁ hR₁ hinv hL hR hE Φ Φ']

end Main

end TernaryPeriodPolynomials.Argument.RadicalInduction
