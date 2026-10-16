module

public import TernaryPeriodPolynomials.Topology.Covering.SingularFibers

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E] [ContinuousConstSMul G E]
variable {V : Type*} [MulAction G V]

/-- Actual equivariant cochains on cover singular simplices, before imposing a differential. -/
abbrev EquivariantCochain (G : Type) [Group G] (E : TopCat) [MulAction G E]
    [ContinuousConstSMul G E] (V : Type*) [MulAction G V] (n : ℕ) :=
  {c : SingularSimplex E n → V // ∀ (g : G) τ, c (g • τ)=g • c τ}

/-- Coefficients at a base point are equivariant functions on its actual covering fiber. -/
abbrev FiberCoefficient (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Type*)
    [MulAction G V] (b : B) :=
  {c : Fiber p b → V // ∀ g e, c (fiberSmul p hp g e)=g • c e}

/-- Actual vertex coefficient assignments, one for each singular simplex downstairs. -/
abbrev VertexCochain (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Type*)
    [MulAction G V] (n : ℕ) :=
  (σ : SingularSimplex B n) → FiberCoefficient p hp V (atVertex σ)

/-- Evaluate an equivariant cover cochain on the unique lift at a specified fiber point. -/
def cochainToVertex (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {n : ℕ}
    (c : EquivariantCochain G E V n) : VertexCochain p hp V n :=
  fun σ => ⟨fun e => c.val ((liftVertexEquiv p hp σ).symm e).val,by
    intro g e
    exact (congrArg (fun τ : Lifts p σ => c.val τ.val)
      (liftVertexEquiv_symm_smul p hp σ g e)).trans (c.property g _)⟩

/-- Evaluate a vertex coefficient assignment at the vertex of the actual cover simplex. -/
def vertexToFunction (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {n : ℕ}
    (c : VertexCochain p hp V n) (τ : SingularSimplex E n) : V :=
  (c (projection p n τ)).val ⟨atVertex τ,rfl⟩

omit [ContinuousConstSMul G E] in
/-- The preceding evaluation is independent of how the fixed base simplex is displayed. -/
theorem vertexToFunction_lift (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {n : ℕ}
    (c : VertexCochain p hp V n) {σ : SingularSimplex B n} (τ : Lifts p σ) :
    vertexToFunction p hp c τ.val=(c σ).val (liftVertexEquiv p hp σ τ) := by
  rcases τ with ⟨τ,hτ⟩
  cases hτ
  rfl

/-- The actual deck action on vertices proves equivariance of reconstructed cochains. -/
def vertexToCochain (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {n : ℕ}
    (c : VertexCochain p hp V n) : EquivariantCochain G E V n :=
  ⟨vertexToFunction p hp c,by
    intro g τ
    let τ' : Lifts p (projection p n τ) := ⟨τ,rfl⟩
    calc
      vertexToFunction p hp c (g • τ) =
          (c (projection p n τ)).val
            (liftVertexEquiv p hp _ (liftsSmul p hp g τ')) :=
        vertexToFunction_lift p hp c (liftsSmul p hp g τ')
      _ = (c (projection p n τ)).val
          (fiberSmul p hp g (liftVertexEquiv p hp _ τ')) := by rw [liftVertexEquiv_smul]
      _ = g • (c (projection p n τ)).val (liftVertexEquiv p hp _ τ') :=
        (c (projection p n τ)).property g _
      _ = g • vertexToFunction p hp c τ := rfl⟩

/-- Cover equivariant cochains and actual base-simplex vertex coefficients agree bijectively. -/
def cochainVertexEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (n : ℕ) :
    EquivariantCochain G E V n ≃ VertexCochain p hp V n where
  toFun := cochainToVertex p hp
  invFun := vertexToCochain p hp
  left_inv c := by
    apply Subtype.ext
    funext τ
    change c.val (((liftVertexEquiv p hp (projection p n τ)).symm
      (liftVertexEquiv p hp (projection p n τ) ⟨τ,rfl⟩)).val)=c.val τ
    exact congrArg (fun υ : Lifts p (projection p n τ) => c.val υ.val)
      ((liftVertexEquiv p hp (projection p n τ)).symm_apply_apply ⟨τ,rfl⟩)
  right_inv c := by
    funext σ
    apply Subtype.ext
    funext e
    change vertexToFunction p hp c ((liftVertexEquiv p hp σ).symm e).val=(c σ).val e
    rw [vertexToFunction_lift,Equiv.apply_symm_apply]

end TernaryPoly.CoveringSingularOrbits
