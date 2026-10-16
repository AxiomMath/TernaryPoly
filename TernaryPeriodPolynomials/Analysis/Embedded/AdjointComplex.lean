module

public import TernaryPeriodPolynomials.Analysis.Embedded.LinearComplex

@[expose] public section


/-! The algebraic reverse-complex law for actual embedded mutually adjoint cores. -/
noncomputable section
namespace TernaryPoly.EmbeddedLinearOperator
open scoped InnerProductSpace
variable {V W Z : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Z] [Module ℝ Z]
  {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Formal adjoints of an embedded algebraic complex form the reversed algebraic complex. -/
theorem adjoint_comp_eq_zero (i : V →ₗ[ℝ] E) (hi : Function.Injective i)
    (j : W →ₗ[ℝ] F) (l : Z →ₗ[ℝ] G)
    (D : V →ₗ[ℝ] W) (T : W →ₗ[ℝ] Z) (A : W →ₗ[ℝ] V) (B : Z →ₗ[ℝ] W)
    (hD : ∀ v w, inner ℝ (j (D v)) (j w) = inner ℝ (i v) (i (A w)))
    (hT : ∀ w z, inner ℝ (l (T w)) (l z) = inner ℝ (j w) (j (B z)))
    (hC : ∀ v, T (D v) = 0) (z : Z) : A (B z) = 0 := by
  have hz : inner ℝ (i (A (B z))) (i (A (B z))) = 0 := by
    calc
      _ = inner ℝ (j (D (A (B z)))) (j (B z)) := (hD _ _).symm
      _ = inner ℝ (l (T (D (A (B z))))) (l z) := (hT _ _).symm
      _ = 0 := by rw [hC, map_zero, inner_zero_left]
  exact hi ((inner_self_eq_zero.mp hz).trans (map_zero i).symm)

end TernaryPoly.EmbeddedLinearOperator
