module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Gram

@[expose] public section


/-!
# The form-to-cochain bridge (OB5): triangle cochains of closed equivariant forms represent their de Rham classes

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

* `triangleCochain A ω x₀ (y₀,y₁,y₂) = ∫_{[y₀x₀, y₁x₀, y₂x₀]} ω` (`FormCochainBridge.triangleCochain`), for a group acting by affine
  maps on an open convex set.
* `triangleCochain_isCocycle`: it is a homogeneous `2`-cocycle for every closed form (Stokes on the affine triangle with a primitive
  from the Poincare lemma; no tetrahedron Stokes is needed).
* `triangleCochain_equivariant`: `F(g y) = ρ(g) F(y)` for equivariant forms.
* `bridge_triangleCochain_eq_deRhamClass`: the inhomogeneous cocycle `(a,b) ↦ F(1,a,ab)` has the class `ZigZag.deRhamClass ω`.
* `bridge_pullback`: the same for the pullback `φ^*ω` along an equivariant smooth map `φ : s → t`, with the class of the *original* form `ω`
  (composition with the naturality `EisensteinClass.deRhamClass_natural`).
* `bridge_gram`, `bridge_eisenstein`: for `Γ ⊂ SL₃(ℤ)` acting on the open convex Gram cone by `G ↦ γ G γᵀ`, with the equivariant
  unimodular normalization `conePoint : Gram cone → Ω`, the Gram-triangle cocycle `(a,b) ↦ ∫_{[1, a aᵀ, (ab)(ab)ᵀ]} φ^*ω` has the
  class `eisensteinClass` of the literal class of `𝓔_P(ω_h)`.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FormCochainBridge

open TernaryPeriodPolynomials.Argument.FormCochainBridge TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.ConvergenceC4

alias triangleCochain_isCocycle := TernaryPeriodPolynomials.Argument.FormCochainBridge.triangleCochain_isCocycle
alias triangleCochain_equivariant := TernaryPeriodPolynomials.Argument.FormCochainBridge.triangleCochain_equivariant
alias bridge_triangleCochain_eq_deRhamClass := TernaryPeriodPolynomials.Argument.FormCochainBridge.bridge_triangleCochain_eq_deRhamClass
alias bridge_pullback := TernaryPeriodPolynomials.Argument.FormCochainBridge.bridge_pullback
alias bridge_eisenstein := TernaryPeriodPolynomials.Argument.FormCochainBridge.bridge_eisenstein

/-- **The Gram-triangle cochain of a closed `Γ`-equivariant form on `Ω`**: equivariant, a homogeneous cocycle, and representing the
de Rham class of the form. -/
theorem form_cochain_bridge (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] (ρ : Representation ℝ Γ F)
    (om : SeedC3.ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) :
    (∀ (g : Γ) (y : Fin 3 → Γ), triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 (fun i => g * y i) =
        ρ g (triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 y)) ∧
      (∀ x : Fin 4 → Γ,
        triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 ![x 1, x 2, x 3] -
          triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 ![x 0, x 2, x 3] +
          triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 ![x 0, x 1, x 3] -
          triangleCochain (coneAction Γ) (gramForm Γ ρ om) 1 ![x 0, x 1, x 2] = 0) ∧
      (groupCohomology.H2π (Rep.of ρ)).hom
          ⟨_, isCocycle_inhomTriangle isOpen_gramCone (coneAction Γ) ρ convex_gramCone ⟨1, one_mem_gramCone⟩
            (coneAffine Γ) (pullInv (coneEquiv Γ) (fun _ => rfl) om) one_mem_gramCone⟩ =
        SeedC3.ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) ρ om :=
  ⟨gramTriangle_equivariant Γ ρ om, gramTriangle_isCocycle Γ ρ om, bridge_gram Γ ρ om⟩

end TernaryPeriodPolynomials.Argument.Statements.FormCochainBridge
