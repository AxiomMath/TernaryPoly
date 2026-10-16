module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.CuspConjStmt
public import TernaryPeriodPolynomials.ArithmeticCohomology.FrameInvariance.Orientation

@[expose] public section


/-!
# Conjugation naturality of the cup-form pairing: `cuspConjNat`

Formalized by Claude Sonnet 5.5.

A cuspidal class of `Γ(N)` is represented by a normalised twisted cusp function `Φ`; transporting it by `Ξ`, `α = conj A` gives the twisted cusp function `Ξ ∘ Φ ∘ A` (minus its value at `cusp₁`)
for the transported class (`transport_data`).  The cup form is a sum over representative triangles of the integrand `integ`; pulling back along `A` multiplies the integrand by `det A` (`integ_comp`, the `integ_comp_neg`) and
the sum over the `Γ(N)`-invariant integrand does not depend on the representatives (`sum_tri_normalizer`), so `B₂ (Ξ̃ x) (Ξ̃' y) = ε · det A · B₁ x y`.
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FrameInvariance

open CongruenceSubgroup
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.CuspidalInduction
open TernaryPeriodPolynomials.Argument.SeedC3S4c (cuspidalSubspace)
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
  TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open scoped Classical

variable {N : ℕ}

section Shape

/-- A cuspidal crossed homomorphism is `fTw Φ + (v - ρ v)` for a normalised twisted cusp function (copy of S7's `exists_cusp_function`). -/
theorem exists_cusp_fn (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (C : groupCohomology.cocycles₁ V)
    (hC : groupCohomology.H1π V C ∈ cuspidalSubspace (Gamma N) V) :
    ∃ (Φ : Tw (transRep hN V).ρ) (v : V), Φ.1 cusp1 = 0 ∧
      ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v) := by
  obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN V C
  have hmem := (theta_mem_cuspidal_iff hN V _).1 hC
  rw [hθ] at hmem
  obtain ⟨Φ, h0, hΦ⟩ := exists_Tn_of_cuspidal hN (transRep hN V) hmem
  rw [mTw_apply, groupCohomology.H1π_eq_iff] at hΦ
  obtain ⟨v, hv⟩ := hΦ
  refine ⟨Φ, v, h0, fun g => ?_⟩
  have := congrFun hv (gammaEquiv hN g)
  simp only [groupCohomology.d₀₁_hom_apply] at this
  have e1 := hc' (gammaEquiv hN g)
  rw [MulEquiv.symm_apply_apply] at e1
  change (transRep hN V).ρ (gammaEquiv hN g) v - v = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) - c'.1 (gammaEquiv hN g) at this
  rw [transRep_ρ, MulEquiv.symm_apply_apply] at this
  rw [← e1]
  linear_combination (norm := abel) this

/-- If `C = fTw Φ + (v - ρ v)` then `θ [C] = mTw Φ` (copy of S7's `theta_class_of_shape`). -/
theorem theta_shape (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (C : groupCohomology.cocycles₁ V)
    (Φ : Tw (transRep hN V).ρ) (v : V)
    (hC : ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v)) :
    (thetaIso hN V).hom.hom (groupCohomology.H1π V C) = mTw (transRep hN V) Φ := by
  obtain ⟨c', hc', hθ⟩ := thetaIso_hom_π hN V C
  rw [hθ, mTw_apply, groupCohomology.H1π_eq_iff]
  refine ⟨-v, ?_⟩
  funext g'
  simp only [groupCohomology.d₀₁_hom_apply]
  have e1 := hC ((gammaEquiv hN).symm g')
  rw [MulEquiv.apply_symm_apply] at e1
  have e2 := hc' g'
  change (transRep hN V).ρ g' (-v) - -v = c'.1 g' - fTw (transRep hN V) Φ.1 g'
  rw [e2, e1, transRep_ρ, map_neg]
  abel

/-- The class of a normalised twisted cusp function is its own `cuspEquiv`-preimage. -/
theorem symm_of_shape (hN : 3 ≤ N) (V : Rep ℂ (Gamma N)) (x : cuspidalSubspace (Gamma N) V)
    (C : groupCohomology.cocycles₁ V) (hx : x.1 = groupCohomology.H1π V C)
    (Φ : Tw (transRep hN V).ρ) (v : V)
    (hC : ∀ g : Gamma N, C.1 g = fTw (transRep hN V) Φ.1 (gammaEquiv hN g) + (v - V.ρ g v)) :
    (cuspEquiv hN V).symm ⟨mTw (transRep hN V) Φ, mTw_mem_cuspidal _ Φ⟩ = x := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [cuspEquiv_val, hx, theta_shape hN V C Φ v hC]

end Shape

section Transport

theorem tw_of_equation {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (gammaNGL N) E)
    (Φ : RationalLine2 → E) (f : gammaNGL N → E)
    (h : ∀ (γ : gammaNGL N) (x : RationalLine2), Φ ((γ : IntegralGL) • x) = ρ γ (Φ x) + f γ) : Φ ∈ Tw ρ := by
  refine ⟨f, fun g k => ?_, h⟩
  have e1 := h (g * k) cusp1
  have e2 := h g ((k : IntegralGL) • cusp1)
  have e3 := h k cusp1
  have : ((g * k : gammaNGL N) : IntegralGL) • cusp1 = (g : IntegralGL) • (k : IntegralGL) • cusp1 := by
    change ((g : IntegralGL) * (k : IntegralGL)) • cusp1 = _
    rw [mul_smul]
  rw [this, e2, e3, map_mul, Module.End.mul_apply, map_add] at e1
  linear_combination (norm := abel) -e1

variable (hN : 3 ≤ N) (α : Gamma N ≃* Gamma N) (A : IntegralGL) (hα : GLConj hN α A) (V₁ V₂ : Rep ℂ (Gamma N))
  (Ξ : V₁ →ₗ[ℂ] V₂) (hΞ : ∀ l v, Ξ (V₁.ρ (α l) v) = V₂.ρ l (Ξ v))

include hα in
theorem conj_smul (l : Gamma N) (x : RationalLine2) :
    A • (((gammaEquiv hN l : gammaNGL N) : IntegralGL) • x) =
      ((gammaEquiv hN (α l) : gammaNGL N) : IntegralGL) • (A • x) := by
  rw [← mul_smul, ← mul_smul, hα l]
  congr 1
  group

include hα hΞ in
/-- **Transport of the normalised twisted cusp function**: `Ψ = Ξ ∘ Φ ∘ A - Ξ Φ(A cusp₁)` is a normalised twisted cusp function of the transported module representing the transported class. -/
theorem transport_data (c : groupCohomology.cocycles₁ V₁) (Φ : Tw (transRep hN V₁).ρ) (v : V₁)
    (hC : ∀ g : Gamma N, c.1 g = fTw (transRep hN V₁) Φ.1 (gammaEquiv hN g) + (v - V₁.ρ g v)) :
    ∃ (Φ₂ : Tw (transRep hN V₂).ρ) (v₂ : V₂), (∀ x, Φ₂.1 x = Ξ (Φ.1 (A • x)) - Ξ (Φ.1 (A • cusp1))) ∧
      Φ₂.1 cusp1 = 0 ∧ ∀ g : Gamma N,
        (oneCocyclePullback V₁ V₂ α.toMonoidHom Ξ (cuspInter α V₁ V₂ Ξ hΞ) c).1 g =
          fTw (transRep hN V₂) Φ₂.1 (gammaEquiv hN g) + (v₂ - V₂.ρ g v₂) := by
  set k := Φ.1 (A • cusp1) with hk
  let Ψ : RationalLine2 → V₂ := fun x => Ξ (Φ.1 (A • x)) - Ξ k
  have key : ∀ (l : Gamma N) (x : RationalLine2), Ψ (((gammaEquiv hN l : gammaNGL N) : IntegralGL) • x) =
      V₂.ρ l (Ψ x) + (V₂.ρ l (Ξ k) - Ξ k + Ξ (fTw (transRep hN V₁) Φ.1 (gammaEquiv hN (α l)))) := by
    intro l x
    have e := fTw_twisted (transRep hN V₁) Φ.2 (gammaEquiv hN (α l)) (A • x)
    simp only [Ψ]
    rw [conj_smul hN α A hα l x, e, transRep_ρ, MulEquiv.symm_apply_apply, map_add, hΞ]
    simp only [map_sub]
    abel
  have hTw : Ψ ∈ Tw (transRep hN V₂).ρ := by
    refine tw_of_equation _ Ψ (fun γ => V₂.ρ ((gammaEquiv hN).symm γ) (Ξ k) - Ξ k +
      Ξ (fTw (transRep hN V₁) Φ.1 (gammaEquiv hN (α ((gammaEquiv hN).symm γ))))) ?_
    intro γ x
    obtain ⟨l, rfl⟩ := (gammaEquiv hN).surjective γ
    rw [key, transRep_ρ, MulEquiv.symm_apply_apply]
  have h0 : Ψ cusp1 = 0 := by simp [Ψ, hk]
  refine ⟨⟨Ψ, hTw⟩, Ξ v + Ξ k, fun x => rfl, h0, fun g => ?_⟩
  have hf : fTw (transRep hN V₂) Ψ (gammaEquiv hN g) =
      V₂.ρ g (Ξ k) - Ξ k + Ξ (fTw (transRep hN V₁) Φ.1 (gammaEquiv hN (α g))) := by
    show Ψ (((gammaEquiv hN g : gammaNGL N) : IntegralGL) • cusp1) -
      (transRep hN V₂).ρ (gammaEquiv hN g) (Ψ cusp1) = _
    rw [key g cusp1, h0]
    simp only [map_zero, zero_add, sub_zero]
  show Ξ (c.1 (α g)) = _
  rw [hC (α g), hf]
  simp only [map_add, map_sub, hΞ]
  abel

end Transport

section Analytic

variable {A₁ A₁' A₂ A₂' : Type} [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₁'] [Module ℂ A₁']
  [AddCommGroup A₂] [Module ℂ A₂] [AddCommGroup A₂'] [Module ℂ A₂']

theorem integ_transport (e₁ : A₁ →ₗ[ℂ] A₁' →ₗ[ℂ] ℂ) (e₂ : A₂ →ₗ[ℂ] A₂' →ₗ[ℂ] ℂ) (Ξ : A₁ →ₗ[ℂ] A₂) (Ξ' : A₁' →ₗ[ℂ] A₂')
    (ε : ℂ) (he : ∀ v w, e₂ (Ξ v) (Ξ' w) = ε * e₁ v w) (Φ : RationalLine2 → A₁) (Φ' : RationalLine2 → A₁')
    (κ : A₂) (κ' : A₂') (A : IntegralGL) (y : Tri) :
    integ e₂ (fun x => Ξ (Φ (A • x)) + κ) (fun x => Ξ' (Φ' (A • x)) + κ') y =
      ε * ((A.val.det : ℤ) : ℂ) * integ e₁ Φ Φ' (A • y) := by
  rw [integ_add_const]
  have h1 : integ e₂ (fun x => Ξ (Φ (A • x))) (fun x => Ξ' (Φ' (A • x))) y =
      ε * integ e₁ (fun x => Φ (A • x)) (fun x => Φ' (A • x)) y := by
    unfold integ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [he, he]; ring
  rw [h1]
  rcases det_cases A with hd | hd
  · rw [integ_comp e₁ Φ Φ' (show IsSL A from hd) y, hd]; simp
  · rw [integ_comp_neg e₁ Φ Φ' hd y, hd]; simp

end Analytic

section Main

/-- **`CuspConjNat`**: the cup-form pairing is natural under conjugation by `A ∈ GL₂(ℤ)`, up to the orientation sign `det A`. -/
theorem cuspConjNat (N : ℕ) (hN : 3 ≤ N) : CuspConjNat N hN := by
  intro α A hα V₁ V₁' V₂ V₂' _ _ _ _ e₁ hinv₁ hL₁ hR₁ e₂ hinv₂ hL₂ hR₂ B₁ B₂ hB₁ hB₂ Ξ Ξ' hΞ hΞ' ε he x y
  have surj : ∀ (V : Rep ℂ (Gamma N)) (z : groupCohomology.H1 V), ∃ c, groupCohomology.H1π V c = z := fun V z => by
    induction z using groupCohomology.H1_induction_on with
    | h c => exact ⟨c, rfl⟩
  obtain ⟨c, hxc⟩ := surj V₁ x.1
  obtain ⟨c', hyc⟩ := surj V₁' y.1
  obtain ⟨Φ, v, h0, hsh⟩ := exists_cusp_fn hN V₁ c (hxc ▸ x.2)
  obtain ⟨Φ', v', h0', hsh'⟩ := exists_cusp_fn hN V₁' c' (hyc ▸ y.2)
  have hx := symm_of_shape hN V₁ x c hxc.symm Φ v hsh
  have hy := symm_of_shape hN V₁' y c' hyc.symm Φ' v' hsh'
  have hB1 := hB₁ Φ Φ' h0 h0'
  rw [hx, hy] at hB1
  obtain ⟨Φ₂, v₂, hΦ₂, h0₂, hsh₂⟩ := transport_data hN α A hα V₁ V₂ Ξ hΞ c Φ v hsh
  obtain ⟨Φ₂', v₂', hΦ₂', h0₂', hsh₂'⟩ := transport_data hN α A hα V₁' V₂' Ξ' hΞ' c' Φ' v' hsh'
  have hx2 := symm_of_shape hN V₂ (cuspXi hN α A hα V₁ V₂ Ξ hΞ x)
    (oneCocyclePullback V₁ V₂ α.toMonoidHom Ξ (cuspInter α V₁ V₂ Ξ hΞ) c)
    (by rw [cuspXi_val, ← hxc, cuspXiH1_π]) Φ₂ v₂ hsh₂
  have hy2 := symm_of_shape hN V₂' (cuspXi hN α A hα V₁' V₂' Ξ' hΞ' y)
    (oneCocyclePullback V₁' V₂' α.toMonoidHom Ξ' (cuspInter α V₁' V₂' Ξ' hΞ') c')
    (by rw [cuspXi_val, ← hyc, cuspXiH1_π]) Φ₂' v₂' hsh₂'
  have hB2 := hB₂ Φ₂ Φ₂' h0₂ h0₂'
  rw [hx2, hy2] at hB2
  rw [hB2, hB1, cupForm_eq_sum, cupForm_eq_sum]
  have hΦ₂f : Φ₂.1 = fun x => Ξ (Φ.1 (A • x)) + (-Ξ (Φ.1 (A • cusp1))) :=
    funext fun x => by rw [hΦ₂ x, sub_eq_add_neg]
  have hΦ₂f' : Φ₂'.1 = fun x => Ξ' (Φ'.1 (A • x)) + (-Ξ' (Φ'.1 (A • cusp1))) :=
    funext fun x => by rw [hΦ₂' x, sub_eq_add_neg]
  rw [hΦ₂f, hΦ₂f']
  change ∑ y ∈ (gammaNFareyData hN).RT.R, integ e₂ _ _ y = _ * ∑ y ∈ (gammaNFareyData hN).RT.R, integ e₁ Φ.1 Φ'.1 y
  simp only [integ_transport e₁ e₂ Ξ Ξ' ε he]
  rw [← Finset.mul_sum]
  congr 1
  obtain ⟨f, -, hf⟩ := Φ.2
  obtain ⟨f', -, hf'⟩ := Φ'.2
  have hconj : ∀ (B : IntegralGL) (γ : gammaNGL N), B * (γ : IntegralGL) * B⁻¹ ∈ gammaNGL N := fun B γ => by
    have := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) :
      IntegralGL →* GL (Fin 2) (ZMod N))).conj_mem _ γ.2 B
    simpa [gammaNGL] using this
  refine sum_tri_normalizer hN A (hconj A) (fun γ => by simpa using hconj A⁻¹ γ) _ (fun γ y => ?_)
  refine integ_invariant (fun g hg => gammaN_isSL hN hg) (ρ := (transRep hN V₁).ρ) (ρ' := (transRep hN V₁').ρ) e₁
    (fun γ v w => hinv₁ ((gammaEquiv hN).symm γ) v w) Φ.1 Φ'.1 f f' hf hf' γ y

end Main

end TernaryPeriodPolynomials.Argument.FrameInvariance
