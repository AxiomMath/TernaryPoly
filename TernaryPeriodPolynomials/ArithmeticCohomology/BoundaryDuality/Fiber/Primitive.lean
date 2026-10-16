module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.Kostant
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CocycleBridge

@[expose] public section


/-!
# Torsion primitives of the Levi cocycles and transfer of the cup formula

* The `U`-equivariant one-cocycles form a submodule (`uCocycles`).
* **Torsion primitives**: the Levi cocycle `A(h) = h ⋆ ω − ω` is a right crossed homomorphism,
  and for an element `f` of order dividing `N` the average `v = −(1/N) Σ_{j<N} A(f^j)` satisfies
  `A(f⁻¹) = f · v − v` for the left action `g · u = g⁻¹ ⋆ u`
  (`leviCocycle_torsion_primitive`). So the crossed homomorphism `α(g) = A(g⁻¹)` has a primitive
  at every torsion element.
* **Transfer**: the cup formula of `CocycleBridge` is natural for linear maps of the coefficients
  that intertwine the relevant values and actions and relate the coefficient pairings
  (`cupFormula_transfer`), and primitive triples are transported along such maps
  (`isPrimitive_transfer`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.FiberPrimitive

open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.CocycleBridge
  (cupFormula IsPrimitive)
open TernaryPeriodPolynomials.BoundaryDuality.FiberCochains
open TernaryPeriodPolynomials.BoundaryDuality.FiberKostant

theorem differentialOneRaw_add {G V : Type} [AddCommGroup V] (f g : (Fin 2 → G) → V)
    (x : Fin 3 → G) :
    differentialOneRaw (f + g) x = differentialOneRaw f x + differentialOneRaw g x := by
  simp only [differentialOneRaw, Pi.add_apply]
  abel

theorem differentialOneRaw_smul {G V : Type} [AddCommGroup V] [Module ℂ V] (c : ℂ)
    (f : (Fin 2 → G) → V) (x : Fin 3 → G) :
    differentialOneRaw (c • f) x = c • differentialOneRaw f x := by
  simp only [differentialOneRaw, Pi.smul_apply, smul_add, smul_sub]

section Submodule

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- The `U`-equivariant one-cocycles. -/
def uCocycles (ρ : Representation ℂ G V) (U : Subgroup G) : Submodule ℂ ((Fin 2 → G) → V) where
  carrier := {f | UCocycle ρ U f}
  zero_mem' := by
    show UCocycle ρ U 0
    refine ⟨fun γ _ a b => ?_, fun x => ?_⟩
    · exact (map_zero (ρ γ)).symm
    · simp only [differentialOneRaw, Pi.zero_apply, sub_zero, add_zero]
  add_mem' := by
    intro f g hf hg
    have hf' : UCocycle ρ U f := hf
    have hg' : UCocycle ρ U g := hg
    show UCocycle ρ U (f + g)
    refine ⟨fun γ hγ a b => ?_, fun x => ?_⟩
    · change f ![γ * a, γ * b] + g ![γ * a, γ * b] = ρ γ (f ![a, b] + g ![a, b])
      rw [hf'.1 γ hγ, hg'.1 γ hγ, map_add]
    · rw [differentialOneRaw_add, hf'.2, hg'.2, add_zero]
  smul_mem' := by
    intro c f hf
    have hf' : UCocycle ρ U f := hf
    show UCocycle ρ U (c • f)
    refine ⟨fun γ hγ a b => ?_, fun x => ?_⟩
    · change c • f ![γ * a, γ * b] = ρ γ (c • f ![a, b])
      rw [hf'.1 γ hγ, map_smul]
    · rw [differentialOneRaw_smul, hf'.2, smul_zero]

theorem mem_uCocycles {ρ : Representation ℂ G V} {U : Subgroup G} {f : (Fin 2 → G) → V} :
    f ∈ uCocycles ρ U ↔ UCocycle ρ U f := Iff.rfl

end Submodule

section Torsion

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- **Torsion primitive of the Levi cocycle**: if `f^{N+1} = 1` and `(N + 1) c = −1`, then
`A(f⁻¹) = f · v − v` for `v = c Σ_{j ≤ N} A(f^j)`. -/
theorem leviCocycle_torsion_primitive (ρ : Representation ℂ G V) (ω : (Fin 2 → G) → V)
    {f : G} {N : ℕ} (hf : f ^ (N + 1) = 1) {c : ℂ} (hc : ((N + 1 : ℕ) : ℂ) * c = -1) :
    leviCocycle ρ ω f⁻¹ =
      cochainRep ρ f (c • ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j)) -
        c • ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j) := by
  have hinv : f⁻¹ = f ^ N := (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hf)).symm
  have hterm : ∀ j, cochainRep ρ f (leviCocycle ρ ω (f ^ j)) =
      leviCocycle ρ ω (f ^ j * f⁻¹) - leviCocycle ρ ω f⁻¹ := by
    intro j
    rw [cochainRep_apply, leviCocycle_mul]
    abel
  have hshift : ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j * f⁻¹) =
      ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j) := by
    have e1 : ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j * f⁻¹) =
        ∑ i ∈ Finset.range N, leviCocycle ρ ω (f ^ (i + 1) * f⁻¹) +
          leviCocycle ρ ω (f ^ 0 * f⁻¹) :=
      Finset.sum_range_succ' _ _
    have e2 : ∑ j ∈ Finset.range (N + 1), leviCocycle ρ ω (f ^ j) =
        ∑ i ∈ Finset.range N, leviCocycle ρ ω (f ^ i) + leviCocycle ρ ω (f ^ N) :=
      Finset.sum_range_succ _ _
    have h1 : ∑ i ∈ Finset.range N, leviCocycle ρ ω (f ^ (i + 1) * f⁻¹) =
        ∑ i ∈ Finset.range N, leviCocycle ρ ω (f ^ i) :=
      Finset.sum_congr rfl fun i _ => by rw [pow_succ, mul_inv_cancel_right]
    rw [e1, e2, h1, pow_zero, one_mul, hinv]
  rw [map_smul, map_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
    hshift, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub,
    smul_smul, mul_comm c, hc, neg_one_smul]
  abel

end Torsion

section Transfer

variable {G₁ G₂ V₁ W₁ V₂ W₂ : Type} [Group G₁] [Group G₂] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂]
  [Module ℂ W₂]

/-- **Naturality of the cup formula** along linear maps `Φ`, `Ψ` of the coefficients which carry
the relevant values and actions to the second model and relate the pairings by `c`. -/
theorem cupFormula_transfer (B₁ : V₁ →ₗ[ℂ] W₁ →ₗ[ℂ] ℂ) (B₂ : V₂ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ)
    (ρ₁ : Representation ℂ G₁ W₁) (ρ₂ : Representation ℂ G₂ W₂) (a₁ b₁ : G₁) (a₂ b₂ : G₂)
    (z₁ : G₁ → V₁) (y₁ : G₁ → W₁) (z₂ : G₂ → V₂) (y₂ : G₂ → W₂) (v : V₁ × V₁ × V₁)
    (Φ : V₁ →ₗ[ℂ] V₂) (Ψ : W₁ →ₗ[ℂ] W₂) (c : ℂ)
    (k1 : B₁ (z₁ a₁) (ρ₁ a₁ (y₁ b₁)) = c * B₂ (Φ (z₁ a₁)) (Ψ (ρ₁ a₁ (y₁ b₁))))
    (k2 : B₁ (z₁ (a₁ * b₁)) (ρ₁ (a₁ * b₁) (y₁ (a₁ * b₁)⁻¹)) =
      c * B₂ (Φ (z₁ (a₁ * b₁))) (Ψ (ρ₁ (a₁ * b₁) (y₁ (a₁ * b₁)⁻¹))))
    (k3 : B₁ v.1 (y₁ a₁) = c * B₂ (Φ v.1) (Ψ (y₁ a₁)))
    (k4 : B₁ v.2.1 (y₁ b₁) = c * B₂ (Φ v.2.1) (Ψ (y₁ b₁)))
    (k5 : B₁ v.2.2 (y₁ (a₁ * b₁)⁻¹) = c * B₂ (Φ v.2.2) (Ψ (y₁ (a₁ * b₁)⁻¹)))
    (ez1 : Φ (z₁ a₁) = z₂ a₂) (ez2 : Φ (z₁ (a₁ * b₁)) = z₂ (a₂ * b₂))
    (ey1 : Ψ (ρ₁ a₁ (y₁ b₁)) = ρ₂ a₂ (y₂ b₂))
    (ey2 : Ψ (ρ₁ (a₁ * b₁) (y₁ (a₁ * b₁)⁻¹)) = ρ₂ (a₂ * b₂) (y₂ (a₂ * b₂)⁻¹))
    (ey3 : Ψ (y₁ a₁) = y₂ a₂) (ey4 : Ψ (y₁ b₁) = y₂ b₂)
    (ey5 : Ψ (y₁ (a₁ * b₁)⁻¹) = y₂ (a₂ * b₂)⁻¹) :
    cupFormula B₁ ρ₁ a₁ b₁ z₁ y₁ v =
      c * cupFormula B₂ ρ₂ a₂ b₂ z₂ y₂ (Φ v.1, Φ v.2.1, Φ v.2.2) := by
  unfold cupFormula
  dsimp only
  rw [k1, k2, k3, k4, k5, ez1, ez2, ey1, ey2, ey3, ey4, ey5]
  ring

/-- **Transport of primitive triples** along a linear map intertwining the values and the
actions at the three special elements. -/
theorem isPrimitive_transfer (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂)
    (a₁ b₁ : G₁) (a₂ b₂ : G₂) (z₁ : G₁ → V₁) (z₂ : G₂ → V₂) (v : V₁ × V₁ × V₁)
    (Φ : V₁ →ₗ[ℂ] V₂) (h : IsPrimitive ρ₁ a₁ b₁ z₁ v)
    (e1 : Φ (z₁ a₁) = z₂ a₂) (e2 : Φ (z₁ b₁) = z₂ b₂) (e3 : Φ (z₁ (a₁ * b₁)⁻¹) = z₂ (a₂ * b₂)⁻¹)
    (q1 : Φ (ρ₁ a₁ v.1) = ρ₂ a₂ (Φ v.1)) (q2 : Φ (ρ₁ b₁ v.2.1) = ρ₂ b₂ (Φ v.2.1))
    (q3 : Φ (ρ₁ (a₁ * b₁)⁻¹ v.2.2) = ρ₂ (a₂ * b₂)⁻¹ (Φ v.2.2)) :
    IsPrimitive ρ₂ a₂ b₂ z₂ (Φ v.1, Φ v.2.1, Φ v.2.2) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← e1, h1]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, q1]
  · rw [← e2, h2]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, q2]
  · rw [← e3, h3]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, q3]

end Transfer

end TernaryPeriodPolynomials.BoundaryDuality.FiberPrimitive
