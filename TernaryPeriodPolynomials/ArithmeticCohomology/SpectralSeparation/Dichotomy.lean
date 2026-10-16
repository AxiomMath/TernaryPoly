module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SpectralSeparation.Simultaneous

@[expose] public section


/-!
# Single generalized eigencharacter and the equal-or-independent dichotomy

`SingleCharacter 𝒜 A`: any two nonzero vectors of `A` share a simultaneous
generalized eigenvalue for every element of `𝒜`. Together with
`EigenSeparated 𝒜 A`, this says `A` is zero or one full simultaneous generalized
eigenspace of `𝒜`. Two such subspaces are equal or independent.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SpectralSeparation

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- All nonzero vectors of `A` have one common simultaneous generalized eigencharacter. -/
def SingleCharacter (𝒜 : Subalgebra ℂ (Module.End ℂ W)) (A : Submodule ℂ W) : Prop :=
  ∀ a ∈ A, ∀ w ∈ A, a ≠ 0 → w ≠ 0 →
    ∀ f ∈ 𝒜, ∃ μ : ℂ, (∃ k : ℕ, ((f - μ • 1) ^ k) a = 0) ∧ ∃ k : ℕ, ((f - μ • 1) ^ k) w = 0

theorem le_of_separated_single (𝒜 : Subalgebra ℂ (Module.End ℂ W)) {A A' : Submodule ℂ W}
    (hs : SingleCharacter 𝒜 A) (hA' : EigenSeparated 𝒜 A') {v : W} (hvA : v ∈ A)
    (hvA' : v ∈ A') (hv : v ≠ 0) : A ≤ A' := by
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0]; exact A'.zero_mem
  · exact hA' v w hvA' hv (hs v hvA w hw hv hw0)

theorem dichotomy_of_separated (𝒜 : Subalgebra ℂ (Module.End ℂ W)) {A A' : Submodule ℂ W}
    (hA : EigenSeparated 𝒜 A) (hA' : EigenSeparated 𝒜 A')
    (hs : SingleCharacter 𝒜 A) (hs' : SingleCharacter 𝒜 A') :
    A ⊓ A' = ⊥ ∨ A = A' := by
  by_cases h : A ⊓ A' = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact le_antisymm (le_of_separated_single 𝒜 hs hA' hv.1 hv.2 hv0)
      (le_of_separated_single 𝒜 hs' hA hv.2 hv.1 hv0)

end TernaryPeriodPolynomials.SpectralSeparation
