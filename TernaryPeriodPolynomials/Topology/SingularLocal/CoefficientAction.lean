module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.CohomologyComplex
public import TernaryPeriodPolynomials.Topology.Covering.CoefficientCochainModule
public import TernaryPeriodPolynomials.Topology.Covering.CoefficientEvaluation

@[expose] public section


noncomputable section
open CategoryTheory
namespace TernaryPoly.SingularLocalCoefficient
open FreeActionLinearization CoveringSingularOrbits EquivariantSingularResolution
open EquivariantSingularCohomology

variable {G : Type} [Group G]

/-- The coefficient action is exactly the given representation action. -/
instance representationDistribMulAction (V : Rep ℚ G) : DistribMulAction G V where
  smul g v := V.ρ g v
  one_smul v := by change V.ρ 1 v=v; rw [map_one]; rfl
  mul_smul g h v := by change V.ρ (g*h) v=V.ρ g (V.ρ h v); rw [map_mul]; rfl
  smul_zero g := map_zero _
  smul_add g v w := map_add _ _ _

/-- The representation action commutes with rational scalar multiplication. -/
instance representationSMulCommClass (V : Rep ℚ G) : SMulCommClass G ℚ V where
  smul_comm g r v := (V.ρ g).map_smul r v

@[simp] theorem representation_smul (V : Rep ℚ G) (g : G) (v : V) : g • v=V.ρ g v := rfl

variable {E B : TopCat} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep ℚ G)

/-- The representation-equivariant and action-equivariant actual simplex functions coincide linearly. -/
def cochainActionEquiv (n : ℕ) :
    equivariantFunctions G E V n ≃ₗ[ℚ] EquivariantCochain G E V n :=
  LinearEquiv.refl ℚ _

/-- Actual singular Hom cochains identify with the actual covering-fiber coefficients downstairs. -/
def homVertexEquiv (n : ℕ) :
    (chainRep G E n ⟶ V) ≃ₗ[ℚ] VertexCochain p hp V n :=
  cochainFunctionEquiv G E V n ≪≫ₗ cochainActionEquiv (G := G) (E := E) V n ≪≫ₗ
    cochainVertexLinearEquiv p hp n

/-- The geometric coefficient assignment recovers literal generator evaluation on each lift. -/
theorem vertexToFunction_homVertexEquiv (n : ℕ) (f : chainRep G E n ⟶ V)
    (τ : SingularSimplex E n) :
    vertexToFunction p hp (homVertexEquiv p hp V n f) τ=cochainFunctionEquiv G E V n f τ := by
  exact congrArg (fun c : EquivariantCochain G E V n => c.val τ)
    ((cochainVertexLinearEquiv (V := V) p hp n).symm_apply_apply
      (cochainActionEquiv (G := G) (E := E) V n (cochainFunctionEquiv G E V n f)))

/-- Evaluation at an arbitrary actual lift agrees with its actual singular-chain generator. -/
theorem homVertexEquiv_lift (n : ℕ) (f : chainRep G E n ⟶ V)
    {σ : SingularSimplex B n} (τ : Lifts p σ) :
    (homVertexEquiv p hp V n f σ).val (liftVertexEquiv p hp σ τ)=
      cochainFunctionEquiv G E V n f τ.val :=
  (vertexToFunction_lift p hp (homVertexEquiv p hp V n f) τ).symm.trans
    (vertexToFunction_homVertexEquiv p hp V n f τ.val)

end TernaryPoly.SingularLocalCoefficient
