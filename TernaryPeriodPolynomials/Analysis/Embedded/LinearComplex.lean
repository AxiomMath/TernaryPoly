module

public import TernaryPeriodPolynomials.Analysis.Embedded.LinearOperator

@[expose] public section

/-! The actual core complex law transports to the literal densely defined operators. -/
noncomputable section
namespace TernaryPoly.EmbeddedLinearOperator
open scoped LinearPMap
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Z] [Module ℝ Z]
  {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- This uses the original differential maps and the actual completion embeddings. -/
theorem complex (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (j : W →ₗ[ℝ] F) (hj : Function.Injective j) (k : Z →ₗ[ℝ] G)
    (D : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] Z) (h : ∀ v, T (D v) = 0) :
    ∀ u : (operator i hi (j.comp D)).domain,
      operator i hi (j.comp D) u ∈ HilbertClosedOperator.kernel (operator j hj (k.comp T)) := by
  intro u
  obtain ⟨v, hv⟩ := u.property
  have hu : u = ⟨i v, ⟨v, rfl⟩⟩ := Subtype.ext hv.symm
  subst u
  rw [operator_apply, LinearMap.comp_apply]
  let w : (operator j hj (k.comp T)).domain := ⟨j (D v), ⟨D v, rfl⟩⟩
  have hz : operator j hj (k.comp T) w = 0 := by
    rw [operator_apply, LinearMap.comp_apply, h v, map_zero]
  change (j (D v), (0 : G)) ∈ (operator j hj (k.comp T)).graph
  rw [← hz]
  exact (operator j hj (k.comp T)).mem_graph w

end TernaryPoly.EmbeddedLinearOperator
