module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Abel
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
# Path defects in an equivariant chain complex

The paths are actual chains with a prescribed boundary. Their defects lie in
`ker boundary`; equivariant evaluation of these cycles gives a group 2-cocycle.
The construction also records the coboundary from changing the chosen paths.
-/

namespace TernaryPeriodPolynomial.PathCocycle

variable (G C₁ C₀ : Type*) [Group G]
  [AddCommGroup C₁] [Module ℚ C₁] [AddCommGroup C₀] [Module ℚ C₀]

/-- The degree-one and degree-zero part of an equivariant chain complex. -/
structure BoundaryData where
  chains : Representation ℚ G C₁
  vertices : Representation ℚ G C₀
  boundary : C₁ →ₗ[ℚ] C₀
  equivariant : ∀ (g : G) (c : C₁), boundary (chains g c) = vertices g (boundary c)

namespace BoundaryData

variable {G C₁ C₀}
variable (D : BoundaryData G C₁ C₀)

/-- Cycles are the actual kernel of the boundary map. -/
abbrev Cycles := LinearMap.ker D.boundary

/-- Boundary equivariance restricts the chain action to the cycle kernel. -/
def cyclesAction : Representation ℚ G D.Cycles :=
  D.chains.subrepresentation D.Cycles fun g c hc => by
    change D.boundary (D.chains g c) = 0
    rw [D.equivariant, LinearMap.mem_ker.mp hc, map_zero]

@[simp] theorem cyclesAction_coe (g : G) (c : D.Cycles) :
    ((D.cyclesAction g c : D.Cycles) : C₁) = D.chains g c := rfl

/-- A path family from a fixed vertex to each of its translates. -/
structure Paths (v : C₀) where
  path : G → C₁
  boundary_path : ∀ g, D.boundary (path g) = v - D.vertices g v

namespace Paths

variable {D} {v : C₀} (τ : D.Paths v)

/-- The failure of a path family to be a crossed homomorphism is a cycle. -/
def defect (g h : G) : D.Cycles :=
  ⟨τ.path g + D.chains g (τ.path h) - τ.path (g * h), by
    change D.boundary (τ.path g + D.chains g (τ.path h) - τ.path (g * h)) = 0
    rw [map_sub, map_add, D.equivariant, τ.boundary_path,
      τ.boundary_path, τ.boundary_path, map_sub, map_mul]
    change v - D.vertices g v + (D.vertices g v - D.vertices g (D.vertices h v)) -
      (v - D.vertices g (D.vertices h v)) = 0
    abel⟩

@[simp] theorem defect_coe (g h : G) :
    ((τ.defect g h : D.Cycles) : C₁) =
      τ.path g + D.chains g (τ.path h) - τ.path (g * h) := rfl

/-- The group 2-cocycle identity already holds in the cycle kernel. -/
theorem defect_cocycle (g h k : G) :
    D.cyclesAction g (τ.defect h k) - τ.defect (g * h) k +
      τ.defect g (h * k) - τ.defect g h = 0 := by
  apply Subtype.ext
  change D.chains g (τ.path h + D.chains h (τ.path k) - τ.path (h * k)) -
    (τ.path (g * h) + D.chains (g * h) (τ.path k) - τ.path ((g * h) * k)) +
    (τ.path g + D.chains g (τ.path (h * k)) - τ.path (g * (h * k))) -
    (τ.path g + D.chains g (τ.path h) - τ.path (g * h)) = 0
  simp only [map_sub, map_add, map_mul, Module.End.mul_apply, mul_assoc]
  abel

/-- Two choices with the same endpoints differ by an actual cycle. -/
def difference (σ : D.Paths v) (g : G) : D.Cycles :=
  ⟨σ.path g - τ.path g, by
    change D.boundary (σ.path g - τ.path g) = 0
    rw [map_sub, σ.boundary_path, τ.boundary_path, sub_self]⟩

@[simp] theorem difference_coe (σ : D.Paths v) (g : G) :
    ((τ.difference σ g : D.Cycles) : C₁) = σ.path g - τ.path g := rfl

/-- Changing paths changes the cycle-valued defect by the coboundary of their difference. -/
theorem defect_sub (σ : D.Paths v) (g h : G) :
    σ.defect g h - τ.defect g h =
      D.cyclesAction g (τ.difference σ h) - τ.difference σ (g * h) +
        τ.difference σ g := by
  apply Subtype.ext
  change (σ.path g + D.chains g (σ.path h) - σ.path (g * h)) -
    (τ.path g + D.chains g (τ.path h) - τ.path (g * h)) =
    D.chains g (σ.path h - τ.path h) - (σ.path (g * h) - τ.path (g * h)) +
      (σ.path g - τ.path g)
  rw [map_sub]
  abel

/-- A path family given by one chain and its translates has zero defect on the subgroup. -/
theorem defect_eq_zero_on_subgroup (H : Subgroup G) (s : C₁)
    (hpath : ∀ g ∈ H, τ.path g = s - D.chains g s)
    (g h : G) (hg : g ∈ H) (hh : h ∈ H) : τ.defect g h = 0 := by
  apply Subtype.ext
  change τ.path g + D.chains g (τ.path h) - τ.path (g * h) = 0
  rw [hpath g hg, hpath h hh, hpath (g * h) (H.mul_mem hg hh), map_sub, map_mul]
  change s - D.chains g s + (D.chains g s - D.chains g (D.chains h s)) -
    (s - D.chains g (D.chains h s)) = 0
  abel

end Paths

variable (E : Type*) [AddCommGroup E] [Module ℚ E]

/-- Equivariant linear evaluation is defined on the cycle kernel, not all chains. -/
structure CycleMap where
  action : Representation ℚ G E
  map : D.Cycles →ₗ[ℚ] E
  equivariant : ∀ (g : G) (c : D.Cycles), map (D.cyclesAction g c) = action g (map c)

namespace CycleMap

variable {D E} (F : D.CycleMap E) {v : C₀}

/-- The path-defect 2-cochain. -/
def cocycle (τ : D.Paths v) (g h : G) : E := F.map (τ.defect g h)

/-- The degree-one inhomogeneous group-cochain differential. -/
def coboundary (b : G → E) (g h : G) : E := F.action g (b h) - b (g * h) + b g

/-- Equivariant linear evaluation of path defects satisfies the 2-cocycle equation. -/
theorem cocycle_condition (τ : D.Paths v) (g h k : G) :
    F.action g (F.cocycle τ h k) - F.cocycle τ (g * h) k +
      F.cocycle τ g (h * k) - F.cocycle τ g h = 0 := by
  have hcycle := congrArg F.map (τ.defect_cocycle g h k)
  simpa only [map_sub, map_add, F.equivariant, map_zero, cocycle] using hcycle

/-- The 1-cochain witnessing independence of the path family. -/
def changeCochain (τ σ : D.Paths v) (g : G) : E := F.map (τ.difference σ g)

/-- The difference between the two constructed cocycles is an explicit coboundary. -/
theorem cocycle_sub (τ σ : D.Paths v) (g h : G) :
    F.cocycle σ g h - F.cocycle τ g h = F.coboundary (F.changeCochain τ σ) g h := by
  have hchange := congrArg F.map (τ.defect_sub σ g h)
  simpa only [map_sub, map_add, F.equivariant, cocycle, coboundary, changeCochain]
    using hchange

/-- A subgroup on which the paths are given by a single chain has zero cocycle. -/
theorem cocycle_eq_zero_on_subgroup (τ : D.Paths v) (H : Subgroup G) (s : C₁)
    (hpath : ∀ g ∈ H, τ.path g = s - D.chains g s)
    (g h : G) (hg : g ∈ H) (hh : h ∈ H) : F.cocycle τ g h = 0 := by
  rw [cocycle, τ.defect_eq_zero_on_subgroup H s hpath g h hg hh, map_zero]

end CycleMap
end BoundaryData
end TernaryPeriodPolynomial.PathCocycle
