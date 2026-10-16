module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.LocalQuotientBound

@[expose] public section


/-!
# The chain `local H² ⊇ K → H¹(Γ₁'(3)) ⊇ period image ≅ S_k(Γ₁(3))`

Abstract assembly of the level-three local upper bound. Let `M` be the local cohomology at a
level-three cusp with the local Hecke operators `T i`, `K ⊆ M` the classes with vanishing radical
restriction, `E : K → H` the injective edge map into `H = H¹(Γ₁'(3), Sym^m ⊗ det^e)`, where it
intertwines `T i` with `α i + β i S i` (`S i` the Hecke operators of `H`), and
`Φ : V → H` the (injective) period map from cusp forms with Hecke operators `U i`, such that `S i`
acts on `H ⧸ range Φ` by scalars. If, for one index each, the complement scalars differ from the
character, then every joint generalized eigenspace of the `T i` lies in the preimage and its
dimension is at most that of the joint generalized eigenspace of the `U i` on cusp forms.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.LevelThree.LocalChain

open Module

variable {ι M H V : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]
  [AddCommGroup V] [Module ℂ V]

/-- **Local upper bound from the chain.** Any submodule `J` of the joint generalized eigenspace
of the `T i` (for the character `c`) is finite-dimensional of dimension at most `m`, provided the
joint generalized eigenspace of the `U i` on `V` for the character `(c i - α i) / β i / γ i` has
dimension at most `m`. -/
theorem local_bound [FiniteDimensional ℂ H] [FiniteDimensional ℂ V]
    (T : ι → Module.End ℂ M) (K : Submodule ℂ M) (S : ι → Module.End ℂ H)
    (U : ι → Module.End ℂ V) (E : K →ₗ[ℂ] H) (Φ : V →ₗ[ℂ] H) (α β γ lam lam' c : ι → ℂ)
    (stable : ∀ i, ∀ y ∈ K, T i y ∈ K)
    (intertwine : ∀ i (y : K),
      E ⟨T i y, stable i y y.property⟩ = α i • E y + β i • S i (E y))
    (hβ : ∀ i, β i ≠ 0) (hE : Function.Injective E) (i₀ : ι)
    (sub_mem : ∀ y, T i₀ y - lam i₀ • y ∈ K) (hne : c i₀ ≠ lam i₀)
    (hγ : ∀ i, γ i ≠ 0) (hΦ : Function.Injective Φ)
    (hint : ∀ i v, S i (Φ v) = γ i • Φ (U i v)) (i₁ : ι)
    (hsub : ∀ y, S i₁ y - lam' i₁ • y ∈ LinearMap.range Φ)
    (hne' : (c i₁ - α i₁) / β i₁ ≠ lam' i₁) (m : ℕ)
    (hbound : finrank ℂ (⨅ i, (U i).maxGenEigenspace ((c i - α i) / β i / γ i) : Submodule ℂ V)
      ≤ m)
    (J : Submodule ℂ M) (hJ : J ≤ ⨅ i, (T i).maxGenEigenspace (c i)) :
    FiniteDimensional ℂ J ∧ finrank ℂ J ≤ m := by
  have hfin : Module.Finite ℂ (⨅ i, (T i).maxGenEigenspace (c i) : Submodule ℂ M) :=
    LocalAssembly.finite_iInf T K S E α β lam c stable intertwine hβ hE i₀ sub_mem hne
  have h1 := LocalAssembly.finrank_iInf_le T K S E α β lam c stable intertwine hβ hE i₀
    sub_mem hne
  have h2 := LocalQuotientBound.finrank_joint_le_of_period S U Φ hΦ γ lam'
    (fun i => (c i - α i) / β i) hγ hint i₁ hsub hne'
  have hJfin : FiniteDimensional ℂ J := Submodule.finiteDimensional_of_le hJ
  refine ⟨hJfin, ?_⟩
  exact (Submodule.finrank_mono hJ).trans (h1.trans (h2.trans hbound))

end TernaryPeriodPolynomials.LevelThree.LocalChain
