module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.List.Enum
public import Mathlib.Data.String.Defs
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.ExtraRecognizers
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.Meta.Tactic.Rewrite
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Ordinal.FundamentalSequence
public import Mathlib.Tactic.Basify.Attr

@[expose] public section


/-!
# A homogeneous arithmetic cochain model in degree two

For a subgroup `Γ ≤ G`, the free simplicial `Γ`-set with vertices `G` is a
contractible free resolution. Its equivariant homogeneous cochains compute
ordinary group cohomology of `Γ`. Using the ambient group as vertices makes
the finite Hecke sums literal formulas on cochains.
-/

noncomputable section

namespace GeneralEisenstein.Homogeneous

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/-- Homogeneous cochains on the ambient vertices with the actual subgroup equivariance. -/
def cochains (Γ : Subgroup G) (ρ : Representation ℂ G V) (k : ℕ) :
    Submodule ℂ ((Fin (k + 1) → G) → V) where
  carrier := {f | ∀ (γ : Γ) x, f (fun i => γ.val * x i) = ρ γ.val (f x)}
  zero_mem' := by simp
  add_mem' {f h} hf hh := by
    intro γ x
    simp only [Pi.add_apply, map_add, hf γ x, hh γ x]
  smul_mem' a f hf := by
    intro γ x
    simp only [Pi.smul_apply, map_smul, hf γ x]

/-- The incoming degree-zero differential. -/
def differentialZero (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    cochains Γ ρ 0 →ₗ[ℂ] cochains Γ ρ 1 where
  toFun f := ⟨fun x => f.val ![x 1] - f.val ![x 0], by
    intro γ x
    have h (a : G) : f.val ![γ.val * a] = ρ γ.val (f.val ![a]) := by
      have ht : (fun i => γ.val * ![a] i) = ![γ.val * a] := by
        funext i
        fin_cases i
        rfl
      simpa only [ht] using f.property γ ![a]
    change f.val ![γ.val * x 1] - f.val ![γ.val * x 0] = _
    rw [h, h, map_sub]⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    change (f.val _ + h.val _) - (f.val _ + h.val _) =
      (f.val _ - f.val _) + (h.val _ - h.val _)
    abel
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change a • f.val _ - a • f.val _ = a • (f.val _ - f.val _)
    exact (smul_sub a _ _).symm

/-- The usual alternating differential from degree one to degree two. -/
def differentialOne (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    cochains Γ ρ 1 →ₗ[ℂ] cochains Γ ρ 2 where
  toFun f := ⟨fun x => f.val ![x 1, x 2] - f.val ![x 0, x 2] + f.val ![x 0, x 1], by
    intro γ x
    have h (a b : G) : f.val ![γ.val * a, γ.val * b] = ρ γ.val (f.val ![a, b]) := by
      have ht : (fun i => γ.val * ![a,b] i) = ![γ.val * a, γ.val * b] := by
        funext i
        fin_cases i <;> rfl
      change f.val ![γ.val * a, γ.val * b] = ρ γ.val (f.val ![a,b])
      simpa only [ht] using f.property γ ![a,b]
    change f.val ![γ.val * x 1, γ.val * x 2] - f.val ![γ.val * x 0, γ.val * x 2] +
      f.val ![γ.val * x 0, γ.val * x 1] = _
    rw [h, h, h, map_add, map_sub]⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    change (f.val _ + h.val _) - (f.val _ + h.val _) + (f.val _ + h.val _) =
      (f.val _ - f.val _ + f.val _) + (h.val _ - h.val _ + h.val _)
    abel
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change a • f.val _ - a • f.val _ + a • f.val _ = a • (f.val _ - f.val _ + f.val _)
    simp only [smul_add, smul_sub]

/-- The alternating degree-two differential, with no representative discarded. -/
def differentialTwo (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    cochains Γ ρ 2 →ₗ[ℂ] ((Fin 4 → G) → V) where
  toFun f x := f.val ![x 1, x 2, x 3] - f.val ![x 0, x 2, x 3] +
    f.val ![x 0, x 1, x 3] - f.val ![x 0, x 1, x 2]
  map_add' f h := by
    funext x
    change (f.val _ + h.val _) - (f.val _ + h.val _) + (f.val _ + h.val _) - (f.val _ + h.val _) =
      (f.val _ - f.val _ + f.val _ - f.val _) + (h.val _ - h.val _ + h.val _ - h.val _)
    abel
  map_smul' a f := by
    funext x
    change a • f.val _ - a • f.val _ + a • f.val _ - a • f.val _ =
      a • (f.val _ - f.val _ + f.val _ - f.val _)
    simp only [smul_add, smul_sub]

theorem differential_squared (Γ : Subgroup G) (ρ : Representation ℂ G V)
    (f : cochains Γ ρ 1) : differentialTwo Γ ρ (differentialOne Γ ρ f) = 0 := by
  funext x
  change (f.val ![x 2, x 3] - f.val ![x 1, x 3] + f.val ![x 1, x 2]) -
    (f.val ![x 2, x 3] - f.val ![x 0, x 3] + f.val ![x 0, x 2]) +
    (f.val ![x 1, x 3] - f.val ![x 0, x 3] + f.val ![x 0, x 1]) -
    (f.val ![x 1, x 2] - f.val ![x 0, x 2] + f.val ![x 0, x 1]) = 0
  abel

/-- All degree-two cocycles. -/
def cocycles (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    Submodule ℂ (cochains Γ ρ 2) :=
  LinearMap.ker (differentialTwo Γ ρ)

instance cocyclesAddCommGroup (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    AddCommGroup (cocycles Γ ρ) :=
  @Submodule.addCommGroup ℂ (cochains Γ ρ 2) inferInstance inferInstance inferInstance (cocycles Γ ρ)

/-- The full incoming differential, with codomain restricted to cocycles. -/
def boundaryMap (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    cochains Γ ρ 1 →ₗ[ℂ] cocycles Γ ρ :=
  (differentialOne Γ ρ).codRestrict _ (differential_squared Γ ρ)

/-- Ordinary degree-two arithmetic cohomology in the ambient homogeneous resolution. -/
abbrev H2 (Γ : Subgroup G) (ρ : Representation ℂ G V) :=
  @HasQuotient.Quotient (cocycles Γ ρ) (Submodule ℂ (cocycles Γ ρ))
    (@Submodule.hasQuotient ℂ (cocycles Γ ρ) inferInstance inferInstance inferInstance)
    (LinearMap.range (boundaryMap Γ ρ))

/-- The quotient map keeps every actual coboundary. -/
def classOf (Γ : Subgroup G) (ρ : Representation ℂ G V) :
    cocycles Γ ρ →ₗ[ℂ] H2 Γ ρ :=
  @Submodule.mkQ ℂ (cocycles Γ ρ) inferInstance inferInstance inferInstance
    (LinearMap.range (boundaryMap Γ ρ))

end GeneralEisenstein.Homogeneous

end
