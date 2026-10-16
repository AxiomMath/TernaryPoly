module

public import Mathlib

@[expose] public section


/-!
# Completing a pre-unitary representation

If a group `G` acts by norm-preserving linear maps on a complex inner product space `V` (not
necessarily complete), the action extends uniquely to the Hilbert space completion
`UniformSpace.Completion V`, again by norm-preserving maps (`completionRep`).  If the orbit maps
of vectors of `V` are continuous on a topological group `G`, so are all orbit maps of the
completion (`continuous_completionRep`).  This is the abstract step that turns the span of right
translates of an automorphic form, with its Petersson inner product, into a Hilbert space with a
strongly continuous unitary representation.
-/

noncomputable section

open UniformSpace

namespace TernaryPeriodPolynomials.Automorphic.CompletionRepresentation

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (ρ : Representation ℂ G V) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖)

/-- The action of `g` on `V` as a linear isometry. -/
def isom (g : G) : V →ₗᵢ[ℂ] V where
  toLinearMap := ρ g
  norm_map' := hρ g

/-- The extension of the action to the completion, one group element at a time. -/
def extension (g : G) : Completion V →L[ℂ] Completion V :=
  (isom ρ hρ g).toContinuousLinearMap.completion

theorem extension_coe (g : G) (v : V) :
    extension ρ hρ g (v : Completion V) = ((ρ g v : V) : Completion V) :=
  ContinuousLinearMap.completion_apply_coe (isom ρ hρ g).toContinuousLinearMap v

theorem continuous_extension (g : G) : Continuous (extension ρ hρ g) :=
  (extension ρ hρ g).continuous

/-- The representation on the completion. -/
def completionRep : Representation ℂ G (Completion V) where
  toFun g := (extension ρ hρ g).toLinearMap
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_extension ρ hρ 1) continuous_id
    | ih v =>
      change extension ρ hρ 1 (v : Completion V) = (v : Completion V)
      rw [extension_coe, map_one]
      rfl
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_extension ρ hρ (g * h))
        ((continuous_extension ρ hρ g).comp (continuous_extension ρ hρ h))
    | ih v =>
      change extension ρ hρ (g * h) (v : Completion V) =
        extension ρ hρ g (extension ρ hρ h (v : Completion V))
      rw [extension_coe, extension_coe, extension_coe, map_mul]
      rfl

theorem completionRep_coe (g : G) (v : V) :
    completionRep ρ hρ g (v : Completion V) = ((ρ g v : V) : Completion V) :=
  extension_coe ρ hρ g v

/-- The extended representation is unitary. -/
theorem completionRep_norm (g : G) (x : Completion V) : ‖completionRep ρ hρ g x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_extension ρ hρ g).norm) continuous_norm
  | ih v =>
    rw [completionRep_coe, Completion.norm_coe, Completion.norm_coe, hρ]

/-- If the orbit maps of vectors of `V` are continuous, so are all orbit maps of the
completion. -/
theorem continuous_completionRep [TopologicalSpace G]
    (hc : ∀ v : V, Continuous fun g => ρ g v) (x : Completion V) :
    Continuous fun g => completionRep ρ hρ g x := by
  rw [Metric.continuous_iff']
  intro g₀ ε hε
  obtain ⟨v, hv⟩ := Metric.denseRange_iff.mp (Completion.denseRange_coe : DenseRange ((↑) : V → Completion V)) x (ε / 3)
    (by positivity)
  have hcv : Continuous fun g => completionRep ρ hρ g (v : Completion V) := by
    simp only [completionRep_coe]
    exact Completion.continuous_coe V |>.comp (hc v)
  have hnear : ∀ᶠ g in nhds g₀, dist (completionRep ρ hρ g (v : Completion V))
      (completionRep ρ hρ g₀ (v : Completion V)) < ε / 3 :=
    (Metric.continuous_iff'.mp hcv) g₀ (ε / 3) (by positivity)
  filter_upwards [hnear] with g hg
  have h1 : dist (completionRep ρ hρ g x) (completionRep ρ hρ g (v : Completion V)) < ε / 3 := by
    rw [dist_eq_norm, ← map_sub, completionRep_norm, ← dist_eq_norm]
    exact hv
  have h2 : dist (completionRep ρ hρ g₀ (v : Completion V)) (completionRep ρ hρ g₀ x) < ε / 3 := by
    rw [dist_eq_norm, ← map_sub, completionRep_norm, ← dist_eq_norm, dist_comm]
    exact hv
  calc dist (completionRep ρ hρ g x) (completionRep ρ hρ g₀ x)
      ≤ dist (completionRep ρ hρ g x) (completionRep ρ hρ g (v : Completion V)) +
        dist (completionRep ρ hρ g (v : Completion V))
          (completionRep ρ hρ g₀ (v : Completion V)) +
        dist (completionRep ρ hρ g₀ (v : Completion V)) (completionRep ρ hρ g₀ x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

end TernaryPeriodPolynomials.Automorphic.CompletionRepresentation
