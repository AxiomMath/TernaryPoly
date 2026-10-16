module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientModule

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
variable {V : Type*}

/-- The unique deck coordinate of a point in an actual covering fiber. -/
def fiberCoordinate (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {b : B}
    (e₀ : Fiber p b) : Fiber p b ≃ G := hp.fiberEquivGroup e₀

@[simp] theorem fiberCoordinate_self (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (e₀ : Fiber p b) : fiberCoordinate p hp e₀ e₀=1 := hp.fiberEquivGroup_self e₀

/-- The coordinate is an actual torsor coordinate, with left deck multiplication. -/
theorem fiberCoordinate_smul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (e₀ e : Fiber p b) (g : G) :
    fiberCoordinate p hp e₀ (fiberSmul p hp g e)=g*fiberCoordinate p hp e₀ e := by
  apply (hp.fiberEquivGroup_eq_iff e₀ (fiberSmul p hp g e) _).mpr
  change g • e.val=(g*fiberCoordinate p hp e₀ e) • e₀.val
  rw [mul_smul]
  exact congrArg (g • ·) (hp.fiberEquivGroup_smul_self e₀).symm

section Action
variable [MulAction G V]

/-- The unique equivariant fiber coefficient with a prescribed value at the chosen lift. -/
def coefficientFromValue (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (e₀ : Fiber p b) (v : V) : FiberCoefficient p hp V b :=
  ⟨fun e => fiberCoordinate p hp e₀ e • v,by
    intro g e
    exact (congrArg (· • v) (fiberCoordinate_smul p hp e₀ e g)).trans (mul_smul g _ v)⟩

/-- A coefficient at a base point is determined by its value at one lift. -/
def coefficientEvaluationEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (e₀ : Fiber p b) : FiberCoefficient p hp V b ≃ V where
  toFun c := c.val e₀
  invFun := coefficientFromValue p hp e₀
  left_inv c := by
    apply Subtype.ext
    funext e
    change fiberCoordinate p hp e₀ e • c.val e₀=c.val e
    have he : fiberSmul p hp (fiberCoordinate p hp e₀ e) e₀=e :=
      Subtype.ext (hp.fiberEquivGroup_smul_self e₀)
    exact (c.property _ _).symm.trans (congrArg c.val he)
  right_inv v := by
    change fiberCoordinate p hp e₀ e₀ • v=v
    rw [fiberCoordinate_self,one_smul]

end Action

section Linear
variable [AddCommGroup V] [Module ℚ V] [DistribMulAction G V] [SMulCommClass G ℚ V]

/-- Fiber evaluation is an isomorphism of the actual rational coefficient modules. -/
def coefficientEvaluationLinearEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (e₀ : Fiber p b) : FiberCoefficient p hp V b ≃ₗ[ℚ] V where
  toEquiv := coefficientEvaluationEquiv p hp e₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Linear
end TernaryPoly.CoveringSingularOrbits
