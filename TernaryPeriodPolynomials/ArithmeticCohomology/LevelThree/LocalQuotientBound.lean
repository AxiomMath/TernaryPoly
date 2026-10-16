module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LocalAssembly

@[expose] public section


/-!
# Joint eigenspaces on a space with a Hecke-stable submodule that is a Hecke module of forms

Let `H` be a complex vector space with a family `S i` of endomorphisms (the Hecke operators on
`H¹(Γ₁'(3), Sym^m ⊗ det^e)`), and let `Φ : V → H` be an injective linear map from a space `V`
carrying operators `T i` (the Hecke operators on `S_k(Γ₁(3))`; `Φ` is the Eichler–Shimura period
map onto the parabolic classes) with `S i (Φ v) = γ i • Φ (T i v)`. If `S i₀` acts on `H ⧸ range Φ`
by a scalar `λ ≠ c i₀` (the Eisenstein eigenvalue differs from the cuspidal one), then the joint
generalized eigenspace of the `S i` for the character `c` embeds into that of the `T i` for the
character `c i / γ i`. This is the abstract dimension step turning "multiplicity at most two for
cusp forms" into "multiplicity at most two for `H¹`".

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.LevelThree.LocalQuotientBound

open Module

variable {ι V H : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup H] [Module ℂ H]

/-- The range of `Φ` is `S`-stable, and the inverse of `Φ` on it intertwines `S i` with
`0 + γ i • T i`. -/
theorem period_setup (S : ι → Module.End ℂ H) (T : ι → Module.End ℂ V) (Φ : V →ₗ[ℂ] H)
    (hΦ : Function.Injective Φ) (γ : ι → ℂ) (hint : ∀ i v, S i (Φ v) = γ i • Φ (T i v)) :
    ∃ stable : ∀ i, ∀ y ∈ LinearMap.range Φ, S i y ∈ LinearMap.range Φ,
      ∀ i (y : LinearMap.range Φ),
        (LinearEquiv.ofInjective Φ hΦ).symm.toLinearMap ⟨S i y.1, stable i y.1 y.2⟩ =
          (fun _ => (0 : ℂ)) i • (LinearEquiv.ofInjective Φ hΦ).symm.toLinearMap y +
            γ i • T i ((LinearEquiv.ofInjective Φ hΦ).symm.toLinearMap y) := by
  have stable : ∀ i, ∀ y ∈ LinearMap.range Φ, S i y ∈ LinearMap.range Φ := by
    rintro i _ ⟨v, rfl⟩
    rw [hint]
    exact ⟨γ i • T i v, by rw [map_smul]⟩
  refine ⟨stable, fun i y => ?_⟩
  set e : V ≃ₗ[ℂ] LinearMap.range Φ := LinearEquiv.ofInjective Φ hΦ
  obtain ⟨v, hv⟩ := y.2
  have hy : y = e v := Subtype.ext hv.symm
  subst hy
  have h1 : (⟨S i (e v).1, stable i (e v).1 (e v).2⟩ : LinearMap.range Φ) =
      e (γ i • T i v) := by
    apply Subtype.ext
    change S i (Φ v) = Φ (γ i • T i v)
    rw [hint, map_smul]
  rw [h1]
  simp

/-- **Dimension step.** The joint generalized `c`-eigenspace of the `S i` on `H` has dimension at
most that of the joint generalized `(c i / γ i)`-eigenspace of the `T i` on `V`. -/
theorem finrank_joint_le_of_period [FiniteDimensional ℂ V] (S : ι → Module.End ℂ H)
    (T : ι → Module.End ℂ V) (Φ : V →ₗ[ℂ] H) (hΦ : Function.Injective Φ) (γ lam c : ι → ℂ)
    (hγ : ∀ i, γ i ≠ 0) (hint : ∀ i v, S i (Φ v) = γ i • Φ (T i v)) (i₀ : ι)
    (hsub : ∀ y, S i₀ y - lam i₀ • y ∈ LinearMap.range Φ) (hne : c i₀ ≠ lam i₀) :
    finrank ℂ (⨅ i, (S i).maxGenEigenspace (c i) : Submodule ℂ H) ≤
      finrank ℂ (⨅ i, (T i).maxGenEigenspace (c i / γ i) : Submodule ℂ V) := by
  obtain ⟨stable, intertwine⟩ := period_setup S T Φ hΦ γ hint
  have := LocalAssembly.finrank_iInf_le (M := H) (H := V) S (LinearMap.range Φ) T
    (LinearEquiv.ofInjective Φ hΦ).symm.toLinearMap (fun _ => (0 : ℂ)) γ lam c stable intertwine
    hγ (LinearEquiv.ofInjective Φ hΦ).symm.injective i₀ hsub hne
  have e : (⨅ i, (T i).maxGenEigenspace (c i / γ i) : Submodule ℂ V) =
      ⨅ i, (T i).maxGenEigenspace ((c i - 0) / γ i) := by simp
  rw [e]
  exact this

/-- The joint generalized eigenspace of the `S i` on `H` is finite-dimensional. -/
theorem finite_joint_of_period [FiniteDimensional ℂ V] (S : ι → Module.End ℂ H)
    (T : ι → Module.End ℂ V) (Φ : V →ₗ[ℂ] H) (hΦ : Function.Injective Φ) (γ lam c : ι → ℂ)
    (hγ : ∀ i, γ i ≠ 0) (hint : ∀ i v, S i (Φ v) = γ i • Φ (T i v)) (i₀ : ι)
    (hsub : ∀ y, S i₀ y - lam i₀ • y ∈ LinearMap.range Φ) (hne : c i₀ ≠ lam i₀) :
    Module.Finite ℂ (⨅ i, (S i).maxGenEigenspace (c i) : Submodule ℂ H) := by
  obtain ⟨stable, intertwine⟩ := period_setup S T Φ hΦ γ hint
  exact LocalAssembly.finite_iInf (M := H) (H := V) S (LinearMap.range Φ) T
    (LinearEquiv.ofInjective Φ hΦ).symm.toLinearMap (fun _ => (0 : ℂ)) γ lam c stable intertwine
    hγ (LinearEquiv.ofInjective Φ hΦ).symm.injective i₀ hsub hne

end TernaryPeriodPolynomials.LevelThree.LocalQuotientBound
