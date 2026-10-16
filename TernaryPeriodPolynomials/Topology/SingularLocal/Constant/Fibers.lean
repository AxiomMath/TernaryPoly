module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalConstant
open CategoryTheory Limits Topology
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology

/-- The one-element group acts trivially on the identity covering space. -/
instance identityAction (X : TopCat.{0}) : MulAction Unit X where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every deck transformation of the identity covering is continuous. -/
instance identityContinuousAction (X : TopCat.{0}) : ContinuousConstSMul Unit X where
  continuous_const_smul _ := continuous_id

/-- The one-element deck group acts freely. -/
instance identityFreeAction (X : TopCat.{0}) : IsCancelSMul Unit X where
  right_cancel' _ _ _ _ := Subsingleton.elim _ _

/-- The literal identity map is a genuine quotient covering by the one-element group. -/
theorem identityCover (X : TopCat.{0}) : IsQuotientCoveringMap (𝟙 X) Unit where
  toIsQuotientMap := IsQuotientMap.id
  toContinuousConstSMul := identityContinuousAction X
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro h
      exact ⟨1, h.symm⟩
    · rintro ⟨g, h⟩
      exact h.symm
  disjoint x := ⟨Set.univ, Filter.univ_mem, fun _ _ => Subsingleton.elim _ _⟩

/-- The arbitrary rational coefficient module, viewed as a constant representation. -/
abbrev constantRep (V : ModuleCat.{0} ℚ) : Rep.{0} ℚ Unit := Rep.trivial ℚ Unit V

/-- The identity covering fiber consists of its specified point. -/
theorem identityFiber_eq (X : TopCat.{0}) (x : X) (z : Fiber (𝟙 X) x) : z = ⟨x, rfl⟩ :=
  Subtype.ext z.property

/-- Actual identity-cover coefficient fibers identify canonically with the given module. -/
def fiberEquiv (X : TopCat.{0}) (V : ModuleCat.{0} ℚ) (x : X) :
    FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) x ≃ₗ[ℚ] V :=
  coefficientEvaluationLinearEquiv (𝟙 X) (identityCover X) ⟨x, rfl⟩

/-- The fiber identification is literal evaluation at the unique covering point. -/
theorem fiberEquiv_apply (X : TopCat.{0}) (V : ModuleCat.{0} ℚ) (x : X)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) x) :
    fiberEquiv X V x c = c.val ⟨x, rfl⟩ := rfl

/-- Every actual path transport preserves the value under canonical fiber identification. -/
theorem fiberEquiv_transport (X : TopCat.{0}) (V : ModuleCat.{0} ℚ) {x y : X}
    (γ : Path.Homotopic.Quotient x y)
    (c : FiberCoefficient (𝟙 X) (identityCover X) (constantRep V) x) :
    fiberEquiv X V y (coefficientTransportLinear (𝟙 X) (identityCover X) γ c) =
      fiberEquiv X V x c := by
  have h := coefficientTransport_apply_transport (𝟙 X) (identityCover X) γ c ⟨x, rfl⟩
  rw [identityFiber_eq X y (fiberTransport (𝟙 X) (identityCover X) γ ⟨x, rfl⟩)] at h
  exact h

end TernaryPoly.SingularLocalConstant
