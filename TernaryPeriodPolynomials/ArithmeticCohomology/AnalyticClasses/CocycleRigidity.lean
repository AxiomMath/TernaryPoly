module

public import Mathlib

@[expose] public section


/-!
# Rigidity of cocycles with vanishing derivatives along one-parameter subgroups

Let a group `G` act on functions `X → V` by maps of the pointwise form `F ↦ (x ↦ L (F (r x)))`
with `L` a continuous linear map of the normed space `V`. A cocycle `E` (`E (g h) = E g + g • E h`)
whose values along a one-parameter subgroup `γ` have derivative zero at `0` at every point is zero
along all of `γ`: by the cocycle law the derivative vanishes at every time. Consequently a cocycle
with this property for a family of one-parameter subgroups vanishes on the subgroup they generate.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.AnalyticClasses

section Rigidity

variable {G : Type*} [Group G] {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An action of `G` on functions `X → V` of pointwise linear form. -/
structure PointwiseAction (G X V : Type*) [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The action on functions. -/
  act : G → (X → V) → (X → V)
  act_one : ∀ F, act 1 F = F
  pointwise : ∀ g, ∃ (L : V →L[ℝ] V) (r : X → X), ∀ F x, act g F x = L (F (r x))

variable (A : PointwiseAction G X V)

theorem PointwiseAction.act_zero (g : G) : A.act g 0 = 0 := by
  obtain ⟨L, r, hL⟩ := A.pointwise g
  funext x
  rw [hL]
  simp

/-- A cocycle for a pointwise action. -/
def IsActionCocycle (E : G → X → V) : Prop := ∀ g h, E (g * h) = E g + A.act g (E h)

variable {A}

theorem IsActionCocycle.map_one {E : G → X → V} (hE : IsActionCocycle A E) : E 1 = 0 := by
  have h := hE 1 1
  rw [mul_one, A.act_one] at h
  have : E 1 + E 1 = E 1 + 0 := by rw [← h, add_zero]
  exact (add_left_cancel this)

theorem IsActionCocycle.map_inv {E : G → X → V} (hE : IsActionCocycle A E) (g : G) :
    E g⁻¹ = -A.act g⁻¹ (E g) := by
  have h := hE g⁻¹ g
  rw [inv_mul_cancel, hE.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **One-parameter rigidity.** -/
theorem IsActionCocycle.eq_zero_of_hasDerivAt {E : G → X → V} (hE : IsActionCocycle A E)
    (γ : ℝ → G) (hom : ∀ s t, γ (s + t) = γ s * γ t) (zero : γ 0 = 1)
    (deriv0 : ∀ x, HasDerivAt (fun s => E (γ s) x) 0 0) (t : ℝ) : E (γ t) = 0 := by
  funext x
  -- the derivative vanishes at every time
  have everywhere : ∀ (y : X) (t₀ : ℝ), HasDerivAt (fun s => E (γ s) y) 0 t₀ := by
    intro y t₀
    obtain ⟨L, r, hL⟩ := A.pointwise (γ t₀)
    have shift : (fun s => E (γ s) y) = fun s => E (γ t₀) y + L (E (γ (s - t₀)) (r y)) := by
      funext s
      have hs : γ s = γ t₀ * γ (s - t₀) := by rw [← hom]; congr 1; ring
      rw [hs, hE, Pi.add_apply, hL]
    rw [shift]
    have inner : HasDerivAt (fun s => E (γ (s - t₀)) (r y)) 0 t₀ := by
      have h0 : HasDerivAt (fun s => E (γ s) (r y)) 0 (t₀ - t₀) := by
        rw [sub_self]; exact deriv0 (r y)
      exact h0.comp_sub_const t₀ t₀
    have := (L.hasFDerivAt.comp_hasDerivAt t₀ inner).const_add (E (γ t₀) y)
    simpa using this
  have differentiable : Differentiable ℝ (fun s => E (γ s) x) :=
    fun s => (everywhere x s).differentiableAt
  have const := is_const_of_deriv_eq_zero differentiable (fun s => (everywhere x s).deriv) t 0
  rw [const, zero, hE.map_one]

/-- **Rigidity on a generated subgroup.** -/
theorem IsActionCocycle.eq_zero_of_closure {E : G → X → V} (hE : IsActionCocycle A E)
    {ι : Type*} (γ : ι → ℝ → G) (hom : ∀ i s t, γ i (s + t) = γ i s * γ i t)
    (zero : ∀ i, γ i 0 = 1) (deriv0 : ∀ i x, HasDerivAt (fun s => E (γ i s) x) 0 0)
    {g : G} (hg : g ∈ Subgroup.closure (Set.range fun p : ι × ℝ => γ p.1 p.2)) : E g = 0 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    exact hE.eq_zero_of_hasDerivAt (γ i) (hom i) (zero i) (deriv0 i) t
  | one => exact hE.map_one
  | mul x y _ _ hx hy => rw [hE, hx, hy, A.act_zero, add_zero]
  | inv x _ hx => rw [hE.map_inv, hx, A.act_zero, neg_zero]

/-- Two cocycles with equal derivatives along the generating one-parameter subgroups agree on
the generated subgroup. -/
theorem IsActionCocycle.eq_of_closure {E E' : G → X → V} (hE : IsActionCocycle A E)
    (hE' : IsActionCocycle A E')
    {ι : Type*} (γ : ι → ℝ → G) (hom : ∀ i s t, γ i (s + t) = γ i s * γ i t)
    (zero : ∀ i, γ i 0 = 1) (D : ι → X → V)
    (deriv : ∀ i x, HasDerivAt (fun s => E (γ i s) x) (D i x) 0)
    (deriv' : ∀ i x, HasDerivAt (fun s => E' (γ i s) x) (D i x) 0)
    {g : G} (hg : g ∈ Subgroup.closure (Set.range fun p : ι × ℝ => γ p.1 p.2)) : E g = E' g := by
  have hsub : IsActionCocycle A (E - E') := by
    intro g h
    simp only [Pi.sub_apply]
    rw [hE, hE']
    obtain ⟨L, r, hL⟩ := A.pointwise g
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, hL, map_sub]
    abel
  have zero' := hsub.eq_zero_of_closure γ hom zero (fun i x => by
    have := (deriv i x).sub (deriv' i x)
    rw [sub_self] at this
    exact this) hg
  exact sub_eq_zero.mp zero'

end Rigidity

end TernaryPeriodPolynomials.AnalyticClasses
