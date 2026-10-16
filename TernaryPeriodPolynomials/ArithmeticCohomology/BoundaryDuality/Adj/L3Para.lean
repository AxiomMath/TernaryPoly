module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.L3Cusp

@[expose] public section


/-!
# Crossed homomorphisms with coboundary values at an element

`CobAt ρ z g` says that the crossed homomorphism `z` takes a coboundary value at `g`:
`z g = (ρ g - 1) u` for some `u`.  This property passes to inverses, powers and conjugates
(`CobAt.inv`, `CobAt.zpow`, `CobAt.conj`): the parabolic crossed homomorphisms of `Γ₁'(3)` take
coboundary values at every conjugate of every power of `T` and of `L`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore

section Cob

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {z : G → V}

/-- A crossed homomorphism takes a coboundary value at `g`. -/
def CobAt (ρ : Representation ℂ G V) (z : G → V) (g : G) : Prop :=
  ∃ u : V, z g = (ρ g - 1) u

theorem CobAt.of_eq {g : G} {u : V} (h : z g = ρ g u - u) : CobAt ρ z g :=
  ⟨u, by rw [h]; simp⟩

theorem CobAt.inv (hz : IsCocycle ρ z) {g : G} (h : CobAt ρ z g) : CobAt ρ z g⁻¹ := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, primitive_inv hz hu⟩

theorem CobAt.pow (hz : IsCocycle ρ z) {g : G} (h : CobAt ρ z g) (n : ℕ) : CobAt ρ z (g ^ n) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, cocycle_pow_primitive hz hu n⟩

theorem CobAt.zpow (hz : IsCocycle ρ z) {g : G} (h : CobAt ρ z g) (n : ℤ) : CobAt ρ z (g ^ n) := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact h.pow hz n
  · rw [zpow_negSucc]
    exact (h.pow hz (n + 1)).inv hz

theorem CobAt.conj (hz : IsCocycle ρ z) {g : G} (h : CobAt ρ z g) (k : G) :
    CobAt ρ z (k * g * k⁻¹) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨ρ k u - z k, ?_⟩
  rw [cocycle_conj hz k g, hu]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← rep_mul_apply ρ (k * g * k⁻¹) k u, ← rep_mul_apply ρ k g u]
  have : k * g * k⁻¹ * k = k * g := by group
  rw [this]
  abel

/-- The explicit primitive at a conjugate. -/
theorem primitive_conj (hz : IsCocycle ρ z) {g : G} {u : V} (hu : z g = (ρ g - 1) u) (k : G) :
    z (k * g * k⁻¹) = (ρ (k * g * k⁻¹) - 1) (ρ k u - z k) := by
  rw [cocycle_conj hz k g, hu]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [← rep_mul_apply ρ (k * g * k⁻¹) k u, ← rep_mul_apply ρ k g u]
  have : k * g * k⁻¹ * k = k * g := by group
  rw [this]
  abel

end Cob

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
