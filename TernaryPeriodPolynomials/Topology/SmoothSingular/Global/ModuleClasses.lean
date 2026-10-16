module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits

variable {R : Type*} [Ring R] (S : ShortComplex (ModuleCat.{0} R))

/-- The genuine abstract homology class of a specified module cocycle. -/
def moduleClass (x : S.X₂) (hx : S.g.hom x = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨x,hx⟩)

/-- The class has the expected image in the actual cokernel. -/
theorem moduleClass_ι (x : S.X₂) (hx : S.g.hom x = 0) :
    S.homologyι (moduleClass S x hx) = S.pOpcycles x := by
  have h := congrArg (fun f => f.hom (S.moduleCatCyclesIso.inv ⟨x,hx⟩)) S.homology_π_ι
  change S.homologyι (moduleClass S x hx) =
    S.pOpcycles (S.iCycles (S.moduleCatCyclesIso.inv ⟨x,hx⟩)) at h
  have hi := congrArg (fun f => f.hom ⟨x,hx⟩) S.moduleCatCyclesIso_inv_iCycles
  change S.iCycles (S.moduleCatCyclesIso.inv ⟨x,hx⟩) = x at hi
  exact h.trans (congrArg S.pOpcycles hi)

/-- Every abstract module homology class has an actual cocycle representative. -/
theorem moduleClass_surjective (h : S.homology) :
    ∃ x : S.X₂, ∃ hx : S.g.hom x = 0, moduleClass S x hx = h := by
  obtain ⟨k,hk⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance h
  have hx : S.g.hom (S.iCycles k) = 0 :=
    congrArg (fun f => f.hom k) S.iCycles_g
  refine ⟨S.iCycles k, hx, ?_⟩
  apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
  rw [moduleClass_ι, ← hk]
  exact (congrArg (fun f => f.hom k) S.homology_π_ι).symm

/-- Equality of actual homology classes is exactly a boundary difference. -/
theorem moduleClass_eq_iff (x y : S.X₂) (hx : S.g.hom x = 0) (hy : S.g.hom y = 0) :
    moduleClass S x hx = moduleClass S y hy ↔ x - y ∈ LinearMap.range S.f.hom := by
  rw [← S.moduleCat_pOpcycles_eq_iff]
  constructor
  · intro h
    simpa only [moduleClass_ι] using congrArg S.homologyι h
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    simpa only [moduleClass_ι] using h

/-- Vanishing of an actual homology class is exactly the boundary condition. -/
theorem moduleClass_eq_zero_iff (x : S.X₂) (hx : S.g.hom x = 0) :
    moduleClass S x hx = 0 ↔ x ∈ LinearMap.range S.f.hom := by
  rw [← S.moduleCat_pOpcycles_eq_zero_iff]
  constructor
  · intro h
    have hh := congrArg S.homologyι h
    simpa only [moduleClass_ι, map_zero] using hh
  · intro h
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    simpa only [moduleClass_ι, map_zero] using h

variable {S} {T : ShortComplex (ModuleCat.{0} R)} (f : S ⟶ T)

/-- The genuine chain map sends genuine cocycles to cocycles. -/
theorem moduleClass_map_closed (x : S.X₂) (hx : S.g.hom x = 0) :
    T.g.hom (f.τ₂.hom x) = 0 := by
  have h := congrArg (fun k => k.hom x) f.comm₂₃
  change T.g.hom (f.τ₂.hom x) = f.τ₃.hom (S.g.hom x) at h
  rw [hx, map_zero] at h
  exact h

/-- The abstract induced homology map agrees with actual cocycle evaluation. -/
theorem moduleClass_natural (x : S.X₂) (hx : S.g.hom x = 0) :
    ShortComplex.homologyMap f (moduleClass S x hx) =
      moduleClass T (f.τ₂.hom x) (moduleClass_map_closed f x hx) := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [moduleClass_ι]
  have h := congrArg (fun k => k.hom (moduleClass S x hx))
    (ShortComplex.homologyι_naturality f)
  change T.homologyι (ShortComplex.homologyMap f (moduleClass S x hx)) =
    ShortComplex.opcyclesMap f (S.homologyι (moduleClass S x hx)) at h
  rw [moduleClass_ι] at h
  exact h.trans (congrArg (fun k => k.hom x) (ShortComplex.p_opcyclesMap f))

end TernaryPoly.SmoothSingularGlobal
