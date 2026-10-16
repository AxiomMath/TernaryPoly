module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Values

@[expose] public section


open scoped MatrixGroups
open CategoryTheory

/-!
# The complex-coefficient mirror of the dual constant-term transport

Formalized by Claude Sonnet 5.5.
`EisensteinDual/Cusps` transports the constant terms of real classes; here the same
for complex classes `H²(Γ(N), E_ℂ)` and `ℂ`-linear maps `T`.

* `facePullC_bijective` (complex analogue of `facePull_bijective`), `pullQPC_bijective`, `pullPQC_bijective`;
* `ConstantTermsAtC`, `dual_constant_terms_transport_C`;
* `dualTC` (`T^∨_h = ȷ^* ∘ T_{ȷ(h)} ∘ (ȷ^*)⁻¹`) and `dual_constant_terms_T_C`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

variable {N n : ℕ}

/-- **The complex face pullback is bijective** when `ȷ(S) = S'`. -/
theorem facePullC_bijective {S S' : Subgroup SL(3, ℤ)} (hS : S ≤ gammaN N) (hS' : S' ≤ gammaN N)
    (hSS' : ∀ s : SL(3, ℤ), jmath s ∈ S' ↔ s ∈ S) (n : ℕ) :
    Function.Bijective (facePullC hS hS' (fun s => (hSS' s.1).2 s.2) n) := by
  let e : S' ≃* S := (jEquivFace hSS').symm
  let e' : (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS'))).V ≃ₗ[ℂ]
      (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))).V := LinearEquiv.refl ℂ _
  have he : ∀ g, e' ∘ₗ (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion hS'))).ρ g =
      (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion hS))).ρ (e g) ∘ₗ e' := by
    intro g
    apply LinearMap.ext
    intro q
    have h1 : jN N (Subgroup.inclusion hS (e g)) = Subgroup.inclusion hS' g :=
      Subtype.ext (by
        change jmath (jmath g.1) = g.1
        exact jmath_jmath _)
    change (gammaRhoC (gammaN N) n (Subgroup.inclusion hS' g)) q = (dualRhoC N n (Subgroup.inclusion hS (e g))) q
    change _ = (gammaRhoC (gammaN N) n (jN N (Subgroup.inclusion hS (e g)))) q
    rw [h1]
  have h := CategoryTheory.ConcreteCategory.bijective_of_isIso (groupCohomology.mapIso e e' he 2).hom
  have hfun : (facePullC hS hS' (fun s => (hSS' s.1).2 s.2) n) = (groupCohomology.mapIso e e' he 2).hom.hom := by
    unfold facePullC
    congr 1
  rw [hfun]
  exact h

theorem pullQPC_bijective (h : SL(3, ℤ)) :
    Function.Bijective (facePullC (N := N) (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n) :=
  facePullC_bijective (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (fun _ => jmath_mem_gammaNPAt_iff) n

theorem pullPQC_bijective (h : SL(3, ℤ)) :
    Function.Bijective (facePullC (N := N) (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n) :=
  facePullC_bijective (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (fun _ => jmath_mem_gammaNQAt_iff) n



/-- **The constant-term statements for a complex class**: prescribed plane-cusp values `ξ h`, line-cusp values `ζ h`, zero flag restrictions. -/
def ConstantTermsAtC (N n : ℕ) (ρ : Representation ℂ (gammaN N) (GeneralEisenstein.HomogeneousPoly n))
    (c : groupCohomology.H2 (Rep.of ρ))
    (ξ : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion (gammaNPAt_le N h)))))
    (ζ : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of (ρ.comp (Subgroup.inclusion (gammaNQAt_le_N N h))))) : Prop :=
  (∀ h, resToC N n (ρ := ρ) (gammaNPAt N h) (gammaNPAt_le N h) c = ξ h) ∧
  (∀ h, resToC N n (ρ := ρ) (gammaNQAt N h) (gammaNQAt_le_N N h) c = ζ h) ∧
  (∀ h, resToC N n (ρ := ρ) (gammaNBAt N h) (gammaNBAt_le_N N h) c = 0)

/-- **Transport of the constant terms, complex coefficients** (unconditional in the dual statement). -/
theorem dual_constant_terms_transport_C
    (c' : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n)))
    (ξ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp
      (Subgroup.inclusion (gammaNPAt_le N h)))))
    (ζ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp
      (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (H : ConstantTermsAtC N n (gammaRhoC (gammaN N) n) c' ξ' ζ') :
    ConstantTermsAtC N n (dualRhoC N n) (jPullC N n c')
      (fun h => facePullC (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n (ζ' (jmath h)))
      (fun h => facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n (ξ' (jmath h))) := by
  obtain ⟨hP, hQ, hB⟩ := H
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [jPullC_res N n (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h), hQ]
  · rw [jPullC_res N n (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h), hP]
  · rw [jPullC_res N n (gammaNBAt_le_N N h) (gammaNBAt_le_N N (jmath h)) (jmath_B_to_B h), hB, map_zero]

/-- **The second constant-term map `T^∨` at the cusp `h`, complex coefficients**: `T^∨_h = ȷ^* ∘ T_{ȷ(h)} ∘ (ȷ^*)⁻¹`; no invertibility or adjoint
normalization of `T` is assumed. -/
def dualTC (T : ∀ h : SL(3, ℤ),
      groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) →ₗ[ℂ]
        groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (h : SL(3, ℤ)) :
    groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))) →ₗ[ℂ]
      groupCohomology.H2 (Rep.of ((dualRhoC N n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) :=
  facePullC (gammaNPAt_le N h) (gammaNQAt_le_N N (jmath h)) (jmath_P_to_Q h) n ∘ₗ T (jmath h) ∘ₗ
    (LinearEquiv.ofBijective (facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n)
      (pullQPC_bijective h)).symm.toLinearMap

/-- **`r_Q ℰ^∨ = η`, `r_P ℰ^∨ = T^∨ η`, `r_B ℰ^∨ = 0` for a complex class from the plane statements** `r_P c' = ξ'`, `r_Q c' = Tξ'`, `r_B c' = 0`
at every cusp, with `ℂ`-linear `T` (`η_h = ȷ^* ξ'(ȷ h)`).  The hypothesis `H` (the constant terms of `c'` for a fixed family `T`) is the only input. -/
theorem dual_constant_terms_T_C
    (c' : groupCohomology.H2 (Rep.of (gammaRhoC (gammaN N) n)))
    (T : ∀ h : SL(3, ℤ),
      groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNPAt_le N h)))) →ₗ[ℂ]
        groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp (Subgroup.inclusion (gammaNQAt_le_N N h)))))
    (ξ' : ∀ h : SL(3, ℤ), groupCohomology.H2 (Rep.of ((gammaRhoC (gammaN N) n).comp
      (Subgroup.inclusion (gammaNPAt_le N h)))))
    (H : ConstantTermsAtC N n (gammaRhoC (gammaN N) n) c' ξ' (fun h => T h (ξ' h))) :
    ∀ h : SL(3, ℤ),
      resToC N n (ρ := dualRhoC N n) (gammaNQAt N h) (gammaNQAt_le_N N h) (jPullC N n c') =
          facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n (ξ' (jmath h)) ∧
      resToC N n (ρ := dualRhoC N n) (gammaNPAt N h) (gammaNPAt_le N h) (jPullC N n c') =
        dualTC T h (facePullC (gammaNQAt_le_N N h) (gammaNPAt_le N (jmath h)) (jmath_Q_to_P h) n (ξ' (jmath h))) ∧
      resToC N n (ρ := dualRhoC N n) (gammaNBAt N h) (gammaNBAt_le_N N h) (jPullC N n c') = 0 := by
  obtain ⟨hP, hQ, hB⟩ := dual_constant_terms_transport_C c' ξ' _ H
  intro h
  refine ⟨hQ h, ?_, hB h⟩
  rw [hP h]
  unfold dualTC
  simp only [LinearMap.comp_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply]

end TernaryPeriodPolynomials.Argument.EisensteinDual
