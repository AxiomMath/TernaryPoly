module

public import TernaryPeriodPolynomials.Analysis.HilbertComplex.ClosedOperatorAdjointTest

@[expose] public section


/-! Projection to a closed cycle space preserves the domain and value of the incoming adjoint. -/
namespace TernaryPoly.HilbertClosedOperator

open scoped InnerProductSpace LinearPMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
variable [CompleteSpace E]

/-- If the range lies in K, orthogonal projection to K does not change the
incoming adjoint. All operator-domain memberships are asserted explicitly. -/
theorem adjoint_projection (S : E →ₗ.[ℝ] F) (hd : Dense (S.domain : Set E))
    (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (hr : ∀ u : S.domain, S u ∈ K) (y : S†.domain) :
    ∃ hp : K.starProjection (y : F) ∈ S†.domain,
      S† ⟨K.starProjection (y : F), hp⟩ = S† y := by
  have hrepr (u : S.domain) : inner ℝ (S† y) (u : E) =
      inner ℝ (K.starProjection (y : F)) (S u) := by
    rw [LinearPMap.adjoint_isFormalAdjoint hd y u]
    have h := K.starProjection_inner_eq_zero (y : F) (S u) (hr u)
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have hp := S.mem_adjoint_domain_of_exists (K.starProjection (y : F)) ⟨S† y, hrepr⟩
  exact ⟨hp, LinearPMap.adjoint_apply_eq hd _ hrepr⟩

/-- Pairing a cycle with a test vector depends only on its projection to the cycle space. -/
theorem inner_projection (K : Submodule ℝ F) [K.HasOrthogonalProjection]
    (z y : F) (hz : z ∈ K) : inner ℝ z y = inner ℝ z (K.starProjection y) := by
  have h := K.starProjection_inner_eq_zero y z hz
  rw [inner_sub_left, sub_eq_zero] at h
  simpa only [real_inner_comm z] using h

end TernaryPoly.HilbertClosedOperator
