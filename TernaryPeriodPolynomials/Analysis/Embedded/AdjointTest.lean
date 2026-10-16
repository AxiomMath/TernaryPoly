module

public import TernaryPeriodPolynomials.Analysis.Embedded.LinearOperator

@[expose] public section

/-! Exact compact-core tests for the graph of an embedded operator's adjoint. -/
noncomputable section
namespace TernaryPoly.EmbeddedLinearOperator
open scoped LinearPMap
variable {V E F : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Every adjoint graph value is characterized by the original algebraic core tests. -/
theorem mem_adjoint_graph_iff (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (hd : DenseRange i) (D : V →ₗ[ℝ] F) (x : F) (z : E) :
    (x, z) ∈ (operator i hi D)†.graph ↔
      ∀ v, inner ℝ z (i v) = inner ℝ x (D v) := by
  let S := operator i hi D
  have hS : Dense (S.domain : Set E) := domain_dense i hi D hd
  constructor
  · intro h v
    obtain ⟨y, hy, hz⟩ := S†.mem_graph_iff.mp h
    change (y : F) = x at hy
    change S† y = z at hz
    have ht := LinearPMap.adjoint_isFormalAdjoint hS y ⟨i v, ⟨v, rfl⟩⟩
    simpa only [S, operator_apply, hy, hz] using ht
  · intro h
    have ht (v : S.domain) : inner ℝ z (v : E) = inner ℝ x (S v) := by
      obtain ⟨w, hw⟩ := v.property
      have hv : v = ⟨i w, ⟨w, rfl⟩⟩ := Subtype.ext hw.symm
      subst v
      simpa only [S, operator_apply] using h w
    have hx : x ∈ S†.domain := S.mem_adjoint_domain_of_exists x ⟨z, ht⟩
    have hz : S† ⟨x, hx⟩ = z := LinearPMap.adjoint_apply_eq hS _ ht
    exact hz ▸ S†.mem_graph ⟨x, hx⟩

end TernaryPoly.EmbeddedLinearOperator
