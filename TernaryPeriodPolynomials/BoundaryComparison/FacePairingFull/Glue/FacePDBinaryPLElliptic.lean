module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Glue.FacePDBinaryPLModel

@[expose] public section


/-!
# The ignored subspace at the elliptic special elements

Formalized by Claude Sonnet 5.5.

The cusp-relative cohomology `Hc` of `FacePDBinaryPLModel` is the compactly supported cohomology of the orbifold of the binary Levi
group: the special elements of finite order (the elliptic points `S`, `S T⁻¹` of `SL₂(ℤ)`, the cone point `T L⁻¹` of `Γ₁(3)`)
are not cusps, so their primitives are determined by the crossed homomorphism up to the fixed vectors and these fixed vectors are
divided out (the ignored subspace `F`).  This file proves that the fixed vectors of a special element of finite order pair to zero
with the value at that element of every crossed homomorphism of the dual system (`slot_torsion`), which is the condition
`IgnoredFor` required of `F`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL

open TernaryPeriodPolynomials.BoundaryDuality
open TripleModel LinearDuality CocycleBridge EpsilonSplit ParabolicDuality

section Elliptic

variable {Γ N V W : Type} [Group Γ] [Group N] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- The zero subspace is ignored. -/
theorem slot_bot (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (w : W) : ∀ f ∈ (⊥ : Submodule ℂ V), B f w = 0 := by
  intro f hf
  rw [Submodule.mem_bot] at hf
  rw [hf, map_zero, LinearMap.zero_apply]

/-- **The fixed vectors of a special element of finite order are orthogonal to the values of crossed homomorphisms** of the
dual system at that element (averaging over the finite cyclic group). -/
theorem slot_torsion (ι : N →* Γ) (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hinv : ∀ n v w, B (ρ (ι n) v) (ρ' (ι n) w) = B v w) (g : N) {k : ℕ}
    (hk : 0 < k) (hg : g ^ k = 1) {Z' : Γ → W} (hZ' : IsCocycle ρ' Z') :
    ∀ f ∈ fixedBy (ρ.comp ι) g, B f (Z' (ι g)) = 0 := by
  intro f hf
  have hZN : IsCocycle (ρ'.comp ι) (fun n => Z' (ι n)) := isCocycle_comp hZ' ι
  obtain ⟨t, ht⟩ := exists_sub_of_pow hZN hk hg
  have ht' : Z' (ι g) = ρ' (ι g) t - t := by
    simpa [LinearMap.sub_apply, Module.End.one_apply] using ht
  have hf' : ρ (ι g) f = f := mem_fixedBy.1 hf
  have e := hinv g f t
  rw [hf'] at e
  rw [ht', map_sub, e, sub_self]

/-- A product of ignored slots is ignored. -/
theorem ignoredFor_prod (ι : N →* Γ) (ρ' : Representation ℂ Γ W) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (a g₂ : N)
    (P₁ P₂ P₃ : Submodule ℂ V)
    (h₁ : ∀ Z' : Γ → W, IsCocycle ρ' Z' → ∀ f ∈ P₁, B f (Z' (ι a)) = 0)
    (h₂ : ∀ Z' : Γ → W, IsCocycle ρ' Z' → ∀ f ∈ P₂, B f (Z' (ι g₂)) = 0)
    (h₃ : ∀ Z' : Γ → W, IsCocycle ρ' Z' → ∀ f ∈ P₃, B f (Z' (ι (a * g₂)⁻¹)) = 0) :
    IgnoredFor ι ρ' B a g₂ (P₁.prod (P₂.prod P₃)) := by
  intro f hf Z' hZ'
  rw [Submodule.mem_prod, Submodule.mem_prod] at hf
  obtain ⟨hf1, hf2, hf3⟩ := hf
  rw [h₁ Z' hZ' f.1 hf1, h₂ Z' hZ' f.2.1 hf2, h₃ Z' hZ' f.2.2 hf3]
  ring

end Elliptic

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD.BinaryPL
