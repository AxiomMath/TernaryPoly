module

public import TernaryPeriodPolynomials.Topology.SingularLocal.CoefficientComplex
public import Mathlib.RepresentationTheory.Rep.Res

@[expose] public section


/-! Honest group reindexing of the actual covering-fiber local coefficients. -/
noncomputable section
namespace TernaryPoly.CoverGroupReindex
open CategoryTheory CoveringSingularOrbits SingularLocalCoefficient

variable {G H : Type} [Group G] [Group H] (e : H ≃* G)
  {E B : TopCat.{0}} [MulAction H E] [MulAction G E]
  (p : E ⟶ B) (hH : IsQuotientCoveringMap p H) (hG : IsQuotientCoveringMap p G)
  (hact : ∀ (h : H) (x : E), h • x = e h • x) (V : Rep.{0} ℚ G)

/-- The underlying fiber function is unchanged; equivariance is reindexed by the group equivalence. -/
def coefficientEquiv (b : B) :
    FiberCoefficient p hG V b ≃ₗ[ℚ] FiberCoefficient p hH (Rep.res e.toMonoidHom V) b where
  toFun c := ⟨c.val, fun h z =>
    (congrArg c.val (Subtype.ext (hact h z.val))).trans (c.property (e h) z)⟩
  invFun c := ⟨c.val, by
    intro g z
    obtain ⟨h, rfl⟩ := e.surjective g
    exact (congrArg c.val (Subtype.ext (hact h z.val).symm)).trans (c.property h z)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coefficientEquiv_apply (b : B) (c : FiberCoefficient p hG V b)
    (z : Fiber p b) : (coefficientEquiv e p hH hG hact V b c).val z = c.val z := rfl

/-- The actual covering monodromy uses the same covering map and does not depend on its group label. -/
theorem fiberTransport_eq {x y : B} (γ : Path.Homotopic.Quotient x y) :
    fiberTransport p hH γ = fiberTransport p hG γ := rfl

/-- The coefficient identity commutes with literal inverse-path fiber transport. -/
theorem coefficientEquiv_transport {x y : B} (γ : Path.Homotopic.Quotient x y)
    (c : FiberCoefficient p hG V x) :
    coefficientEquiv e p hH hG hact V y (coefficientTransport p hG γ c) =
      coefficientTransport p hH γ (coefficientEquiv e p hH hG hact V x c) := rfl

/-- Group reindexing is an actual isomorphism of the fiber-valued local systems. -/
def localSystemIso : coefficientLocalSystem (V := V) p hG ≅
    coefficientLocalSystem (V := Rep.res e.toMonoidHom V) p hH :=
  NatIso.ofComponents (fun b => (coefficientEquiv e p hH hG hact V b.as).toModuleIso)
    (fun _ => by ext c; rfl)

end TernaryPoly.CoverGroupReindex
