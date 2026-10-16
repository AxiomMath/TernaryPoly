module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL2Free.Basic
public import TernaryPeriodPolynomials.GroupCohomology.VirtuallyFreeSecondCohomology
public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

@[expose] public section

noncomputable section
namespace TernaryPoly.RelativeLeviCohomology
open CategoryTheory CategoryTheory.Limits RelativeStabilizerParameters IntegralGL2Free

/-- The two literal descriptions of an intersection subgroup are canonically isomorphic. -/
def intersectionEquiv {G : Type} [Group G] (H S : Subgroup G) : H.subgroupOf S ≃* S.subgroupOf H where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Actual subgroups of integral GL2 inherit finite-index free subgroups. -/
instance intersection_isFree (H : Subgroup GL2) : IsFreeGroup (generated.subgroupOf H) :=
  ((IsFreeGroup.basis (H.subgroupOf generated)).map (intersectionEquiv generated H).symm).isFreeGroup

theorem subgroup_H2_zero (H : Subgroup GL2) (A : Rep ℚ H) :
    IsZero (groupCohomology A 2) :=
  VirtuallyFreeSecondCohomology.isZero_H2_of_isFreeGroup (generated.subgroupOf H) A

/-- Rational degree-two cohomology of the actual plane Levi vanishes for all coefficients. -/
theorem plane_H2_zero (A : Rep ℚ GL2) : IsZero (groupCohomology A 2) :=
  VirtuallyFreeSecondCohomology.isZero_H2_of_isFreeGroup generated A

/-- Remove the finite first sign factor and intersect the actual lower-block Gamma. -/
def lineFree : Subgroup (ℤˣ × Gamma) :=
  (⊥ : Subgroup ℤˣ).prod (generated.subgroupOf Gamma)

instance lineFree_finiteIndex : lineFree.FiniteIndex := by
  constructor
  change ((⊥ : Subgroup ℤˣ).prod (generated.subgroupOf Gamma)).index ≠ 0
  rw [Subgroup.index_prod]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := (⊥ : Subgroup ℤˣ)))
    (Subgroup.FiniteIndex.index_ne_zero (H := generated.subgroupOf Gamma))

def lineFreeEquiv : generated.subgroupOf Gamma ≃* lineFree where
  toFun x := ⟨(1,x.val),⟨by simp,x.property⟩⟩
  invFun x := ⟨x.val.2,x.property.2⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    have hx : x.val.1=1 := x.property.1
    exact Prod.ext hx.symm rfl
  map_mul' _ _ := by
    apply Subtype.ext
    exact Prod.ext (one_mul 1).symm rfl

instance lineFree_isFree : IsFreeGroup lineFree :=
  ((IsFreeGroup.basis (generated.subgroupOf Gamma)).map lineFreeEquiv).isFreeGroup

/-- Rational degree-two cohomology of the actual line Levi vanishes for all coefficients. -/
theorem line_H2_zero (A : Rep ℚ (ℤˣ × Gamma)) : IsZero (groupCohomology A 2) :=
  VirtuallyFreeSecondCohomology.isZero_H2_of_isFreeGroup lineFree A

end TernaryPoly.RelativeLeviCohomology
