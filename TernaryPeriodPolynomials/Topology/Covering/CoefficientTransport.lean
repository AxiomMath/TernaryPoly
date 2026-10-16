module

public import TernaryPeriodPolynomials.Topology.Covering.SingularCoefficients
public import Mathlib.Topology.Covering.Quotient

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
variable {V : Type*} [MulAction G V]

/-- Actual covering monodromy transports a point of a covering fiber along a path class. -/
def fiberTransport (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) : Fiber p x → Fiber p y :=
  hp.isCoveringMap.monodromy γ

/-- The path transport is a bijection of the actual fibers. -/
def fiberTransportEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) : Fiber p x ≃ Fiber p y :=
  Equiv.ofBijective (fiberTransport p hp γ) (hp.isCoveringMap.monodromy_bijective γ)

/-- Covering transport commutes with each actual deck transformation. -/
theorem fiberTransport_smul (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (g : G) (e : Fiber p x) :
    fiberTransport p hp γ (fiberSmul p hp g e)=
      fiberSmul p hp g (fiberTransport p hp γ e) :=
  hp.monodromy_toPermFiber

/-- Constant path transport fixes every actual fiber point. -/
@[simp] theorem fiberTransport_refl (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (x : B) (e : Fiber p x) :
    fiberTransport p hp (Path.Homotopic.Quotient.refl x) e=e :=
  congrFun hp.isCoveringMap.monodromy_refl e

/-- Concatenation gives the actual order of successive fiber transports. -/
theorem fiberTransport_trans (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y z : B}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) (e : Fiber p x) :
    fiberTransport p hp (γ.trans δ) e=fiberTransport p hp δ (fiberTransport p hp γ e) :=
  hp.isCoveringMap.monodromy_trans_apply γ δ e

/-- Transport followed by the reversed path is the identity on the actual fiber. -/
@[simp] theorem fiberTransport_symm_apply (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {x y : B} (γ : Path.Homotopic.Quotient x y) (e : Fiber p x) :
    fiberTransport p hp γ.symm (fiberTransport p hp γ e)=e := by
  rw [← fiberTransport_trans,Path.Homotopic.Quotient.trans_symm,fiberTransport_refl]

/-- Reversed-path transport followed by the original path is the identity. -/
@[simp] theorem fiberTransport_apply_symm (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {x y : B} (γ : Path.Homotopic.Quotient x y) (e : Fiber p y) :
    fiberTransport p hp γ (fiberTransport p hp γ.symm e)=e := by
  rw [← fiberTransport_trans,Path.Homotopic.Quotient.symm_trans,fiberTransport_refl]

/-- The actual vertex coefficient system transports by the inverse path on covering fibers. -/
def coefficientTransport (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) : FiberCoefficient p hp V x → FiberCoefficient p hp V y :=
  fun c => ⟨fun e => c.val (fiberTransport p hp γ.symm e),by
    intro g e
    exact (congrArg c.val (fiberTransport_smul p hp γ.symm g e)).trans (c.property g _)⟩

/-- Parallel transport preserves the value at the transported lift. -/
@[simp] theorem coefficientTransport_apply_transport (p : E ⟶ B)
    (hp : IsQuotientCoveringMap p G) {x y : B} (γ : Path.Homotopic.Quotient x y)
    (c : FiberCoefficient p hp V x) (e : Fiber p x) :
    (coefficientTransport p hp γ c).val (fiberTransport p hp γ e)=c.val e :=
  congrArg c.val (fiberTransport_symm_apply p hp γ e)

/-- Actual coefficient transport along a constant path is the identity. -/
@[simp] theorem coefficientTransport_refl (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (x : B) (c : FiberCoefficient p hp V x) :
    coefficientTransport p hp (Path.Homotopic.Quotient.refl x) c=c := by
  apply Subtype.ext
  funext e
  simpa only [fiberTransport_refl] using
    coefficientTransport_apply_transport p hp (Path.Homotopic.Quotient.refl x) c e

/-- Actual coefficient transport obeys the path-groupoid composition law. -/
theorem coefficientTransport_trans (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {x y z : B} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z)
    (c : FiberCoefficient p hp V x) :
    coefficientTransport p hp (γ.trans δ) c=
      coefficientTransport p hp δ (coefficientTransport p hp γ c) := by
  apply Subtype.ext
  funext e
  obtain ⟨e,rfl⟩ := (fiberTransportEquiv p hp (γ.trans δ)).surjective e
  change (coefficientTransport p hp (γ.trans δ) c).val
      (fiberTransport p hp (γ.trans δ) e)=
    (coefficientTransport p hp δ (coefficientTransport p hp γ c)).val
      (fiberTransport p hp (γ.trans δ) e)
  rw [coefficientTransport_apply_transport,fiberTransport_trans,
    coefficientTransport_apply_transport,coefficientTransport_apply_transport]

end TernaryPoly.CoveringSingularOrbits
