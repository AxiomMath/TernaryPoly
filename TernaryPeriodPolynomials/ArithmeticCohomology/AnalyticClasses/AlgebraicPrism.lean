module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Control.Basic
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
public import Mathlib.Lean.Expr.Basic
public import Mathlib.Lean.Expr.Rat
public import Mathlib.Lean.GoalsLocation
public import Mathlib.Lean.MessageData.Trace
public import Mathlib.Lean.Meta
public import Mathlib.Lean.Meta.Basic
public import Mathlib.Lean.Meta.KAbstractPositions
public import Mathlib.Lean.PrettyPrinter.Delaborator
public import Mathlib.Tactic.Basify.Attr
public import Mathlib.Util.Qq

@[expose] public section


/-!
# The algebraic prism for homogeneous two-cocycles

For a homogeneous two-cochain satisfying the alternating cocycle identity on every four
vertices, moving every vertex along an arbitrary vertex map `φ` changes the cochain by the
coboundary of the explicit prism one-cochain `H(a, b) = c(a, φ a, φ b) - c(a, b, φ b)`.
No continuity of `φ` is involved; this is the identity used to compare a smooth cocycle with
its values on a measurable parabolic section.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.AnalyticClasses

variable {X V : Type*} [AddCommGroup V]

/-- The alternating cocycle identity on four vertices. -/
def IsHomogeneousTwoCocycle (c : X → X → X → V) : Prop :=
  ∀ y₀ y₁ y₂ y₃, c y₁ y₂ y₃ - c y₀ y₂ y₃ + c y₀ y₁ y₃ - c y₀ y₁ y₂ = 0

/-- The prism one-cochain attached to a vertex map. -/
def prismCochain (c : X → X → X → V) (φ : X → X) (a b : X) : V :=
  c a (φ a) (φ b) - c a b (φ b)

/-- **Algebraic prism identity.** -/
theorem prism_identity {c : X → X → X → V} (hc : IsHomogeneousTwoCocycle c) (φ : X → X)
    (y₀ y₁ y₂ : X) :
    c (φ y₀) (φ y₁) (φ y₂) = c y₀ y₁ y₂ +
      (prismCochain c φ y₁ y₂ - prismCochain c φ y₀ y₂ + prismCochain c φ y₀ y₁) := by
  have h₁ := hc y₀ (φ y₀) (φ y₁) (φ y₂)
  have h₂ := hc y₀ y₁ (φ y₁) (φ y₂)
  have h₃ := hc y₀ y₁ y₂ (φ y₂)
  simp only [prismCochain]
  have e₁ : c (φ y₀) (φ y₁) (φ y₂) = c y₀ (φ y₁) (φ y₂) - c y₀ (φ y₀) (φ y₂) +
      c y₀ (φ y₀) (φ y₁) := by
    rw [← sub_eq_zero]; rw [← h₁]; abel
  have e₂ : c y₁ (φ y₁) (φ y₂) = c y₀ (φ y₁) (φ y₂) - c y₀ y₁ (φ y₂) + c y₀ y₁ (φ y₁) := by
    rw [← sub_eq_zero]; rw [← h₂]; abel
  have e₃ : c y₁ y₂ (φ y₂) = c y₀ y₂ (φ y₂) - c y₀ y₁ (φ y₂) + c y₀ y₁ y₂ := by
    rw [← sub_eq_zero]; rw [← h₃]; abel
  rw [e₁, e₂, e₃]
  abel

end TernaryPeriodPolynomials.AnalyticClasses
