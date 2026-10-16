module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Adj.CoreLocal

@[expose] public section


/-!
# Transport of cup primitives and local terms along an endomorphism of the stabilizer

Let `H` be a group with two representations `ρ`, `ρ'` and an invariant pairing `B`, and let
`Ω : H →* H` be an endomorphism (conjugation by the Fricke element) with linear maps `F`, `F'` and a
constant `κ` such that

  `F (ρ (Ω a) v) = ρ a (F v)`, `F' (ρ' (Ω a) w) = ρ' a (F' w)`,
  `B (F v, ρ' a (F' w)) = κ B (v, ρ' (Ω a) w)`.

If `θ₁` is a cup primitive of `(X₁, Y₁)` and `(X₂, Y₂)` are crossed homomorphisms with
`X₂ = F ∘ X₁ ∘ Ω + (ρ · u₁ - u₁)` and `F' ∘ Y₁ ∘ Ω = Y₂ + (ρ' · u₂ - u₂)` then

  `θ₂ h = κ θ₁ (Ω h) + B (u₁, Y₂ h + (ρ' h u₂ - u₂)) + B (X₂ h, ρ' h u₂)`

is a cup primitive of `(X₂, Y₂)` (`transport_isCupPrimitive`) and the local terms correspond:
`localTerm θ₂ Y₂ h (F v + u₁) = κ localTerm θ₁ Y₁ (Ω h) v` (`transport_localTerm`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjL3

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.BoundaryDuality.AdjCore

section Transport

variable {H V W : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {ρ' : Representation ℂ H W} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- The transported cup primitive. -/
def transportPrim (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (ρ' : Representation ℂ H W) (Ω : H →* H) (κ : ℂ)
    (θ₁ : H → ℂ) (X₂ : H → V) (Y₂ : H → W) (u₁ : V) (u₂ : W) (h : H) : ℂ :=
  κ * θ₁ (Ω h) + B u₁ (Y₂ h + (ρ' h u₂ - u₂)) + B (X₂ h) (ρ' h u₂)

variable (hinv : ∀ h v w, B (ρ h v) (ρ' h w) = B v w) (Ω : H →* H) (F : V →ₗ[ℂ] V)
  (F' : W →ₗ[ℂ] W) (κ : ℂ)

include hinv in
/-- **Transport of a cup primitive.** -/
theorem transport_isCupPrimitive
    (hF' : ∀ a w, F' (ρ' (Ω a) w) = ρ' a (F' w))
    (hcomp : ∀ a v w, B (F v) (ρ' a (F' w)) = κ * B v (ρ' (Ω a) w))
    {X₁ X₂ : H → V} {Y₁ Y₂ : H → W} {θ₁ : H → ℂ}
    (hY₁ : IsCocycle ρ' Y₁) (hX₂ : IsCocycle ρ X₂) (hθ₁ : IsCupPrimitive B ρ' X₁ Y₁ θ₁)
    (u₁ : V) (u₂ : W) (hX : ∀ h, F (X₁ (Ω h)) + (ρ h u₁ - u₁) = X₂ h)
    (hY : ∀ h, F' (Y₁ (Ω h)) = Y₂ h + (ρ' h u₂ - u₂)) :
    IsCupPrimitive B ρ' X₂ Y₂ (transportPrim B ρ' Ω κ θ₁ X₂ Y₂ u₁ u₂) := by
  have h1 := isCupPrimitive_pullback Ω F F' κ hcomp hθ₁
  have hYa : IsCocycle ρ' (fun a => F' (Y₁ (Ω a))) := isCocycle_pullback Ω F' hF' hY₁
  have h2 := isCupPrimitive_add_boundary_left hinv hYa h1 u₁
  have hXeq : (fun g => F (X₁ (Ω g)) + (ρ g u₁ - u₁)) = X₂ := funext hX
  rw [hXeq] at h2
  have h3 := isCupPrimitive_add_boundary_right hinv hX₂ h2 (-u₂)
  have hYeq : (fun g => F' (Y₁ (Ω g)) + (ρ' g (-u₂) - -u₂)) = Y₂ := by
    funext g
    rw [hY g, map_neg]
    abel
  have hθeq : (fun g => (κ * θ₁ (Ω g) + B u₁ (F' (Y₁ (Ω g)))) - B (X₂ g) (ρ' g (-u₂))) =
      transportPrim B ρ' Ω κ θ₁ X₂ Y₂ u₁ u₂ := by
    funext g
    rw [transportPrim, hY g, map_neg, map_neg]
    ring
  rw [hYeq] at h3
  have h3' : IsCupPrimitive B ρ' X₂ Y₂
      (fun g => (κ * θ₁ (Ω g) + B u₁ (F' (Y₁ (Ω g)))) - B (X₂ g) (ρ' g (-u₂))) := h3
  rw [hθeq] at h3'
  exact h3'

include hinv in
/-- **Transport of a local term.** -/
theorem transport_localTerm
    (hF : ∀ a v, F (ρ (Ω a) v) = ρ a (F v))
    (hcomp : ∀ a v w, B (F v) (ρ' a (F' w)) = κ * B v (ρ' (Ω a) w))
    {X₁ X₂ : H → V} {Y₁ Y₂ : H → W} {θ₁ : H → ℂ}
    (u₁ : V) (u₂ : W) (hX : ∀ h, F (X₁ (Ω h)) + (ρ h u₁ - u₁) = X₂ h)
    (hY : ∀ h, F' (Y₁ (Ω h)) = Y₂ h + (ρ' h u₂ - u₂)) (h : H) {v : V}
    (hv : X₁ (Ω h) = (ρ (Ω h) - 1) v) :
    localTerm B (transportPrim B ρ' Ω κ θ₁ X₂ Y₂ u₁ u₂) Y₂ h (F v + u₁) =
      κ * localTerm B θ₁ Y₁ (Ω h) v := by
  have hh : X₂ h = (ρ h - 1) (F v + u₁) := by
    rw [← hX h, hv]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hF, map_add]
  have e1 := localTerm_pullback (B := B) (B₁ := B) (ρ' := ρ') (ρ₁' := ρ') (θ := θ₁) (Y := Y₁)
    Ω F F' κ hcomp h v
  have e2 := localTerm_add_boundary_left (B := B) (θ := fun a => κ * θ₁ (Ω a))
    (Y := fun a => F' (Y₁ (Ω a))) u₁ h (F v)
  have e3 := localTerm_add_boundary_right (B := B) (ρ := ρ) (ρ' := ρ')
    (θ := fun g => (κ * θ₁ (Ω g)) + B u₁ (F' (Y₁ (Ω g)))) (Y := fun a => F' (Y₁ (Ω a)))
    (X := X₂) hinv (-u₂) hh
  have hYeq : (fun g => F' (Y₁ (Ω g)) + (ρ' g (-u₂) - -u₂)) = Y₂ := by
    funext g
    rw [hY g, map_neg]
    abel
  have hθeq : (fun g => (κ * θ₁ (Ω g) + B u₁ (F' (Y₁ (Ω g)))) - B (X₂ g) (ρ' g (-u₂))) =
      transportPrim B ρ' Ω κ θ₁ X₂ Y₂ u₁ u₂ := by
    funext g
    rw [transportPrim, hY g, map_neg, map_neg]
    ring
  rw [hYeq, hθeq] at e3
  rw [e3, e2, e1]

end Transport

end TernaryPeriodPolynomials.BoundaryDuality.AdjL3
