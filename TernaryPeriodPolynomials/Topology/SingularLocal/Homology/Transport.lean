module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Lifts

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits
open scoped Classical

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

/-- Reversing a path homotopy class twice returns the original class. -/
theorem reverse_reverse {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path.Homotopic.Quotient x y) : γ.symm.symm = γ := by
  induction γ using Quotient.inductionOn with
  | _ γ => exact congrArg Path.Homotopic.Quotient.mk (Path.symm_symm γ)

/-- The actual reparametrized lift belongs to the actual reparametrized base simplex. -/
def pullLift {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1))))
    {σ : SingularSimplex B n} (τ : Lifts p σ) : Lifts p (pullSimplex θ σ) :=
  ⟨pullSimplex θ τ.val, (projection_pullSimplex p θ τ.val).trans
    (congrArg (pullSimplex θ) τ.property)⟩

omit [ContinuousConstSMul G E] in
/-- For homology the coefficient travels BACK along simplexPullPath: the path itself points
from the face first vertex to the original first vertex. Reverse transport evaluates at the
original lifted vertex when tested at the actual lifted face vertex. -/
theorem backwardTransport_projected {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1))))
    (τ : SingularSimplex E n)
    (c : FiberCoefficient p hp V (atVertex (projection p n τ))) :
    (coefficientTransportLinear p hp (simplexPullPath θ (projection p n τ)).symm c).val
      ⟨atVertex (pullSimplex θ τ), by rw [← atVertex_projection, projection_pullSimplex]⟩ =
        c.val ⟨atVertex τ, rfl⟩ := by
  change c.val (fiberTransport p hp (simplexPullPath θ (projection p n τ)).symm.symm _) = _
  rw [reverse_reverse, SingularLocalCoefficient.simplexTransport_projected]

omit [ContinuousConstSMul G E] in
/-- The backward-transport coefficient formula holds for any actual lift of a fixed base simplex. -/
theorem backwardTransport_lift {m n : ℕ}
    (θ : C(Convexity.StdSimplex ℝ (Fin (m+1)), Convexity.StdSimplex ℝ (Fin (n+1))))
    {σ : SingularSimplex B n} (τ : Lifts p σ)
    (c : FiberCoefficient p hp V (atVertex σ)) :
    (coefficientTransportLinear p hp (simplexPullPath θ σ).symm c).val
      (liftVertexEquiv p hp (pullSimplex θ σ) (pullLift p θ τ)) =
        c.val (liftVertexEquiv p hp σ τ) := by
  rcases τ with ⟨τ, hτ⟩
  cases hτ
  exact backwardTransport_projected p hp V θ τ c

end TernaryPoly.SingularLocalHomology
