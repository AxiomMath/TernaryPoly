module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientModule

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E] [ContinuousConstSMul G E]
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [DistribMulAction G V]
    [SMulCommClass G ℚ V]

/-- The actual cover equivariant cochains form a rational submodule. -/
def equivariantCochainSubmodule (n : ℕ) : Submodule ℚ (SingularSimplex E n → V) where
  carrier := {c | ∀ (g : G) τ, c (g • τ)=g • c τ}
  zero_mem' := by intro g τ; simp
  add_mem' := by
    intro c d hc hd g τ
    exact (congrArg₂ (·+·) (hc g τ) (hd g τ)).trans (smul_add g (c τ) (d τ)).symm
  smul_mem' := by
    intro r c hc g τ
    exact (congrArg (r • ·) (hc g τ)).trans (smul_comm r g (c τ))

instance equivariantCochainAddCommGroup (n : ℕ) : AddCommGroup (EquivariantCochain G E V n) :=
  inferInstanceAs (AddCommGroup (equivariantCochainSubmodule (G := G) (E := E) (V := V) n))

instance equivariantCochainModule (n : ℕ) : Module ℚ (EquivariantCochain G E V n) :=
  inferInstanceAs (Module ℚ (equivariantCochainSubmodule (G := G) (E := E) (V := V) n))

/-- The actual cover/vertex-coefficient cochain bijection is rational-linear. -/
def cochainVertexLinearEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (n : ℕ) :
    EquivariantCochain G E V n ≃ₗ[ℚ] VertexCochain p hp V n where
  toEquiv := cochainVertexEquiv p hp n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TernaryPoly.CoveringSingularOrbits
