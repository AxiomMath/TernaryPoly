module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientTransport
public import Mathlib.Algebra.Category.ModuleCat.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory FreeActionLinearization
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [DistribMulAction G V]
    [SMulCommClass G ℚ V]

/-- The actual equivariant fiber functions form a rational submodule. -/
def coefficientSubmodule (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (b : B) :
    Submodule ℚ (Fiber p b → V) where
  carrier := {c | ∀ g e, c (fiberSmul p hp g e)=g • c e}
  zero_mem' := by intro g e; simp
  add_mem' := by
    intro c d hc hd g e
    exact (congrArg₂ (·+·) (hc g e) (hd g e)).trans (smul_add g (c e) (d e)).symm
  smul_mem' := by
    intro r c hc g e
    exact (congrArg (r • ·) (hc g e)).trans (smul_comm r g (c e))

/-- The coefficient fiber carries its actual pointwise additive group. -/
instance coefficientAddCommGroup (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (b : B) :
    AddCommGroup (FiberCoefficient p hp V b) :=
  inferInstanceAs (AddCommGroup (coefficientSubmodule (V := V) p hp b))

/-- The coefficient fiber carries its actual pointwise rational module. -/
instance coefficientModule (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (b : B) :
    Module ℚ (FiberCoefficient p hp V b) :=
  inferInstanceAs (Module ℚ (coefficientSubmodule (V := V) p hp b))

/-- Literal path-lift transport is rational-linear. -/
def coefficientTransportLinear (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) {x y : B}
    (γ : Path.Homotopic.Quotient x y) : FiberCoefficient p hp V x →ₗ[ℚ] FiberCoefficient p hp V y where
  toFun := coefficientTransport p hp γ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The genuine rational local system associated to the covering and coefficient action. -/
def coefficientLocalSystem (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) :
    FundamentalGroupoid B ⥤ ModuleCat ℚ where
  obj x := ModuleCat.of ℚ (FiberCoefficient p hp V x.as)
  map γ := ModuleCat.ofHom (coefficientTransportLinear p hp γ)
  map_id x := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact coefficientTransport_refl p hp x.as c
  map_comp γ δ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact coefficientTransport_trans p hp γ δ c

/-- Every transport map of this actual local system is invertible. -/
instance coefficientLocalSystem_map_isIso (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {x y : FundamentalGroupoid B} (γ : x ⟶ y) :
    IsIso ((coefficientLocalSystem (V := V) p hp).map γ) :=
  Functor.map_isIso _ _

end TernaryPoly.CoveringSingularOrbits
