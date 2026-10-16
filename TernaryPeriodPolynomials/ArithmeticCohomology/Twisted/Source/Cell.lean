module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Ring.CharZero
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

@[expose] public section


/-!
# Cell functions on a group

Let `G` be a group, `P` and `K` subgroups, `q ∈ G` and `Φ : P → End H` a representation of `P`.  The
*cell function* of `(P, K, q, Φ)` is supported on the single double coset `P q K` and equals `Φ p`
at `p q k`.  It is well defined on a submodule `S` of `H` as soon as `Φ` fixes `S` on
`P ∩ q K q⁻¹` (`CellFixes`).  On `S` it is left `P`-equivariant, right `K`-invariant and equals the
identity at `q`.

This is the finite place of the induced section when the character is ramified: the induced section
of a character nontrivial on the compact units cannot be spherical, but it is supported on the cell
of the cusp, where the stabiliser is small enough for the character to be trivial.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

variable {G H : Type*} [Group G] [AddCommGroup H] [Module ℂ H]

/-- `g` lies in the double coset `P q K`. -/
def InCell (P K : Subgroup G) (q g : G) : Prop :=
  ∃ p : P, ∃ k ∈ K, g = (p : G) * q * k

open scoped Classical in
/-- The cell map: `Φ p` at `p q k`, and `0` outside the cell. -/
def cellMap (P K : Subgroup G) (q : G) (Φ : P →* Module.End ℂ H) (g : G) : Module.End ℂ H :=
  if h : InCell P K q g then Φ (Classical.choose h) else 0

/-- `Φ` fixes `S` on the stabiliser `P ∩ q K q⁻¹` of the cell. -/
def CellFixes (P K : Subgroup G) (q : G) (Φ : P →* Module.End ℂ H) (S : Submodule ℂ H) : Prop :=
  ∀ p : P, ∀ k ∈ K, (p : G) * q = q * k → ∀ w ∈ S, Φ p w = w

variable {P K : Subgroup G} {q : G} {Φ : P →* Module.End ℂ H} {S : Submodule ℂ H}

theorem inCell_mul_left (a : P) (g : G) : InCell P K q ((a : G) * g) ↔ InCell P K q g := by
  constructor
  · rintro ⟨p, k, hk, hg⟩
    refine ⟨a⁻¹ * p, k, hk, ?_⟩
    have h : g = (a : G)⁻¹ * ((p : G) * q * k) := by rw [← hg]; group
    rw [h]
    simp [mul_assoc]
  · rintro ⟨p, k, hk, hg⟩
    refine ⟨a * p, k, hk, ?_⟩
    rw [hg]
    simp [mul_assoc]

theorem inCell_mul_right (g : G) {k : G} (hk : k ∈ K) : InCell P K q (g * k) ↔ InCell P K q g := by
  constructor
  · rintro ⟨p, k', hk', hg⟩
    refine ⟨p, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), ?_⟩
    calc g = g * k * k⁻¹ := by group
      _ = (p : G) * q * (k' * k⁻¹) := by rw [hg]; exact mul_assoc _ _ _
  · rintro ⟨p, k', hk', hg⟩
    refine ⟨p, k' * k, K.mul_mem hk' hk, ?_⟩
    rw [hg]
    exact mul_assoc _ _ _

theorem cellMap_eq_zero {g : G} (h : ¬ InCell P K q g) : cellMap P K q Φ g = 0 := by
  unfold cellMap
  rw [dite_eq_right h]

/-- **Independence of the decomposition.** -/
theorem cellMap_apply_of_eq (hfix : CellFixes P K q Φ S) {g : G} (p : P) {k : G} (hk : k ∈ K)
    (hg : g = (p : G) * q * k) {w : H} (hw : w ∈ S) : cellMap P K q Φ g w = Φ p w := by
  have h : InCell P K q g := ⟨p, k, hk, hg⟩
  unfold cellMap
  rw [dite_eq_left h]
  obtain ⟨k', hk', hg'⟩ := Classical.choose_spec h
  have hprod : (p : G) * q = ((Classical.choose h : P) : G) * q * k' * k⁻¹ :=
    eq_mul_inv_of_mul_eq (by rw [← hg', ← hg])
  have key : (((Classical.choose h)⁻¹ * p : P) : G) * q = q * (k' * k⁻¹) := by
    calc (((Classical.choose h)⁻¹ * p : P) : G) * q = ((Classical.choose h : P) : G)⁻¹ * ((p : G) * q) := by
          simp [mul_assoc]
      _ = q * (k' * k⁻¹) := by rw [hprod]; group
  have hfixed := hfix ((Classical.choose h)⁻¹ * p) (k' * k⁻¹) (K.mul_mem hk' (K.inv_mem hk)) key w hw
  calc Φ (Classical.choose h) w = Φ (Classical.choose h) (Φ ((Classical.choose h)⁻¹ * p) w) := by rw [hfixed]
    _ = Φ p w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

/-- **Left equivariance.** -/
theorem cellMap_mul_left (hfix : CellFixes P K q Φ S) (a : P) (g : G) {w : H} (hw : w ∈ S) :
    cellMap P K q Φ ((a : G) * g) w = Φ a (cellMap P K q Φ g w) := by
  by_cases h : InCell P K q g
  · obtain ⟨p, k, hk, hg⟩ := h
    rw [cellMap_apply_of_eq hfix p hk hg hw,
      cellMap_apply_of_eq hfix (a * p) hk (by rw [hg]; simp [mul_assoc]) hw, map_mul,
      Module.End.mul_apply]
  · have h' : ¬ InCell P K q ((a : G) * g) := fun h2 => h ((inCell_mul_left a g).mp h2)
    rw [cellMap_eq_zero h', cellMap_eq_zero h]
    simp

/-- **Right invariance.** -/
theorem cellMap_mul_right (hfix : CellFixes P K q Φ S) (g : G) {k : G} (hk : k ∈ K) {w : H}
    (hw : w ∈ S) : cellMap P K q Φ (g * k) w = cellMap P K q Φ g w := by
  by_cases h : InCell P K q g
  · obtain ⟨p, k', hk', hg⟩ := h
    rw [cellMap_apply_of_eq hfix p hk' hg hw,
      cellMap_apply_of_eq hfix p (K.mul_mem hk' hk) (by rw [hg]; exact mul_assoc _ _ _) hw]
  · have h' : ¬ InCell P K q (g * k) := fun h2 => h ((inCell_mul_right g hk).mp h2)
    rw [cellMap_eq_zero h', cellMap_eq_zero h]

/-- The cell map is the identity at the cell point. -/
theorem cellMap_self (hfix : CellFixes P K q Φ S) {w : H} (hw : w ∈ S) :
    cellMap P K q Φ q w = w := by
  rw [cellMap_apply_of_eq hfix 1 K.one_mem (by simp) hw, map_one, Module.End.one_apply]

/-- At a point of the cell, the cell map is `Φ` of the parabolic factor. -/
theorem cellMap_apply_of_mem (hfix : CellFixes P K q Φ S) {g : G} (hg : InCell P K q g) {w : H}
    (hw : w ∈ S) : ∃ p : P, cellMap P K q Φ g w = Φ p w := by
  obtain ⟨p, k, hk, hgk⟩ := hg
  exact ⟨p, cellMap_apply_of_eq hfix p hk hgk hw⟩

end TernaryPeriodPolynomials.TwistedSource
