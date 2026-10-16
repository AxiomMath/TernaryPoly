module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedEdgeBij
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Terms

@[expose] public section


/-!
# The face pairing against a class in the image of an idempotent

Formalized by Claude Sonnet 5.5.

`lineFacePairM_component`: for an `S`-equivariant idempotent `e` of the coefficients and a mixed class `x` with `h2E e x = x`, `B(x, y) = B(x, h2E eᵀ y)` (the decomposition along the
complementary idempotents `e`, `1 - e`).
-/

open scoped MatrixGroups DirectSum
noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.ConvergenceC4

section Component

variable {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
  (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6)

omit [Module ℚ V] [IsScalarTower ℚ ℂ V] in
theorem h2E_complement_zero (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (h2 : ∀ (t : gammaNQAt 6 i.rep) (v : V), (LinearMap.id - e : V →ₗ[ℂ] V) (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) ((LinearMap.id - e : V →ₗ[ℂ] V) v))
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (hfix : h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (fun k v => he k v) x = x) :
    h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) (LinearMap.id - e : V →ₗ[ℂ] V)
      (fun k v => h2 k v) x = 0 := by
  have hsum : ∀ (k : gammaNQAt 6 i.rep) (v : V), (e + (LinearMap.id - e : V →ₗ[ℂ] V)) (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) k) ((e + (LinearMap.id - e : V →ₗ[ℂ] V)) v) := fun k v => by
    simp only [add_sub_cancel]; rfl
  have h1 := h2E_add (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (LinearMap.id - e : V →ₗ[ℂ] V)
    (fun k v => he k v) (fun k v => h2 k v) (fun k v => hsum k v) x
  rw [h2E_congr _ (e' := LinearMap.id) (by simp) _ (fun k v => rfl), h2E_id, hfix] at h1
  exact left_eq_add.mp h1

theorem lineFacePairM_component (e : V →ₗ[ℂ] V)
    (he : ∀ (t : gammaNQAt 6 i.rep) (v : V), e (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) (e v))
    (hidem : ∀ v, e (e v) = e v)
    (x : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)))
    (y : groupCohomology.H2 (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)))
    (hx : x ∈ lineMixedSub ρ i) (hy : y ∈ lineMixedSub ρ.dual i)
    (hfix : h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ)) e (fun k v => he k v) x = x) :
    lineFacePairM ρ i x y = lineFacePairM ρ i x
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) e.dualMap
        (fun k v => lineHeD ρ i e he k v) y) := by
  have h₂ : ∀ (t : gammaNQAt 6 i.rep) (v : V), (LinearMap.id - e : V →ₗ[ℂ] V) (ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) v) =
      ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp) t) ((LinearMap.id - e : V →ₗ[ℂ] V) v) := fun t v => by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, he t v]
  have hdec := lineFacePairM_decomp ρ i e (LinearMap.id - e : V →ₗ[ℂ] V) he h₂
    (fun v => by simp) (fun v => by simp [hidem]) (fun v => by simp [hidem]) x y hx hy
  have hz := h2E_complement_zero ρ i e he h₂ x hfix
  rw [hfix, hz] at hdec
  have hy2 := lineMixedSub_h2E_dual ρ i (LinearMap.id - e : V →ₗ[ℂ] V) h₂ y hy
  have h0 : lineFacePairM ρ i 0
      (h2E (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) (Rep.of ρ.dual)) (LinearMap.id - e : V →ₗ[ℂ] V).dualMap
        (fun k v => lineHeD ρ i (LinearMap.id - e : V →ₗ[ℂ] V) h₂ k v) y) = 0 := by
    have h00 : lineFacePairBil ρ i 0 ⟨_, hy2⟩ = 0 := by rw [map_zero]; rfl
    exact h00
  rw [h0, add_zero] at hdec
  exact hdec

end Component

end TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange
