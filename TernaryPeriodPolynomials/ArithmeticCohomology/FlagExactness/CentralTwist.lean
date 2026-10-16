module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel
public import Mathlib.Control.Basic
public import Mathlib.Data.String.Defs
public import Mathlib.Lean.Elab.InfoTree
public import Mathlib.Lean.Elab.Tactic.Basic
public import Mathlib.Lean.Elab.Tactic.Meta
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
# Central twists act unipotently on trivial-coefficient 2-cocycles

Let `φ : G →* G` be an endomorphism of the form `φ a = a * ψ a`, where every value
`ψ a = a⁻¹ * φ a` is central and fixed by `φ`. (Conjugation by a unipotent element of
the Heisenberg group restricted to a subgroup of that group is of this form.) For
inhomogeneous 2-cocycles with trivial coefficients, pulling back along `φ` is
unipotent: if `Δ ω = ω ∘ (φ × φ) - ω`, then `Δ (Δ (Δ ω))` is the coboundary of an
explicit 1-cochain. The proof is an explicit cocycle computation:
* `Δ ω = θ - dτ` with `τ a = ω a (ψ a)` and `θ a b = ω (ψ a) (ψ b) - β_{ψ a} b`,
  where `β_z b = ω b z - ω z b` is additive in `b` for central `z`;
* `Δ θ` depends only on `(ψ a, ψ b)`, so `Δ (Δ θ) = 0`;
* `Δ` commutes with the coboundary.

Original work (AxiomDeep, Claude Opus 5.5).
-/

namespace TernaryPeriodPolynomials.FlagExactness.CentralTwist

variable {G W : Type*} [Group G] [AddCommGroup W]

/-- The trivial-coefficient inhomogeneous 2-cocycle condition. -/
def IsCocycle (ω : G → G → W) : Prop :=
  ∀ a b c, ω b c - ω (a * b) c + ω a (b * c) - ω a b = 0

/-- The trivial-coefficient coboundary of a 1-cochain. -/
def d1 (τ : G → W) : G → G → W := fun a b => τ b - τ (a * b) + τ a

section Lemmas

variable {ω : G → G → W} (hω : IsCocycle ω)
include hω

theorem shift_left_central {z : G} (hz : ∀ x, z * x = x * z) (x y : G) :
    ω (x * z) y = ω x y + ω (x * y) z - ω x z - (ω y z - ω z y) := by
  have h1 := hω x z y
  have h2 := hω x y z
  rw [hz y] at h1
  linear_combination (norm := abel) h2 - h1

theorem shift_right (x y w : G) : ω x (y * w) = ω x y + ω (x * y) w - ω y w := by
  have h := hω x y w
  linear_combination (norm := abel) h

theorem commutator_additive {z : G} (hz : ∀ x, z * x = x * z) (a b : G) :
    ω (a * b) z - ω z (a * b) = (ω a z - ω z a) + (ω b z - ω z b) := by
  have e1 := hω a b z
  have e2 := hω a z b
  have e3 := hω z a b
  rw [hz b] at e2
  rw [hz a] at e3
  linear_combination (norm := abel) e2 - e1 - e3

end Lemmas

section Twist

variable (φ : G →* G)

/-- The central defect `ψ a = a⁻¹ * φ a`. -/
def defect (a : G) : G := a⁻¹ * φ a

theorem phi_eq (a : G) : φ a = a * defect φ a := by
  simp [defect]

/-- Pull back minus identity, on 2-cochains. -/
def delta (ω : G → G → W) : G → G → W := fun a b => ω (φ a) (φ b) - ω a b

/-- Pull back minus identity, on 1-cochains. -/
def delta1 (σ : G → W) : G → W := fun a => σ (φ a) - σ a

variable {φ}
variable (hcen : ∀ a x, defect φ a * x = x * defect φ a)
  (hfix : ∀ a, φ (defect φ a) = defect φ a)

include hcen in
theorem defect_mul (a b : G) : defect φ (a * b) = defect φ a * defect φ b := by
  have h : a * b * defect φ (a * b) = a * b * (defect φ a * defect φ b) := by
    rw [← phi_eq, map_mul, phi_eq φ a, phi_eq φ b, mul_assoc a (defect φ a),
      ← mul_assoc (defect φ a) b, hcen a b]
    simp only [mul_assoc]
  exact mul_left_cancel h

include hfix in
theorem defect_phi (a : G) : defect φ (φ a) = defect φ a := by
  have h : φ a * defect φ (φ a) = φ a * defect φ a := by
    rw [← phi_eq, phi_eq φ a, map_mul, hfix, ← phi_eq]
  exact mul_left_cancel h

/-- The 1-cochain `τ a = ω a (ψ a)`. -/
def tau (ω : G → G → W) : G → W := fun a => ω a (defect φ a)

/-- The first correction cocycle. -/
def theta (ω : G → G → W) : G → G → W := fun a b =>
  ω (defect φ a) (defect φ b) - (ω b (defect φ a) - ω (defect φ a) b)

/-- The second correction cocycle. -/
def theta2 (ω : G → G → W) : G → G → W := fun a b =>
  -(ω (defect φ b) (defect φ a) - ω (defect φ a) (defect φ b))

variable {ω : G → G → W} (hω : IsCocycle ω)

include hcen hω in
theorem delta_eq (a b : G) :
    delta φ ω a b = theta (φ := φ) ω a b - d1 (tau (φ := φ) ω) a b := by
  have e1 := shift_left_central hω (hcen a) a (b * defect φ b)
  have e2 := shift_right hω a b (defect φ b)
  have e3 := commutator_additive hω (hcen a) b (defect φ b)
  have e4 := hω (a * b) (defect φ b) (defect φ a)
  rw [hcen b (defect φ a)] at e4
  rw [← mul_assoc a b (defect φ b)] at e1
  simp only [delta, theta, d1, tau]
  rw [phi_eq φ a, phi_eq φ b, defect_mul hcen a b]
  linear_combination (norm := abel) e1 + e2 - e3 - e4

include hcen hfix hω in
theorem delta_theta (a b : G) : delta φ (theta (φ := φ) ω) a b = theta2 (φ := φ) ω a b := by
  have e := commutator_additive hω (hcen a) b (defect φ b)
  simp only [delta, theta, theta2]
  rw [defect_phi hfix a, defect_phi hfix b, phi_eq φ b]
  linear_combination (norm := abel) -e

include hfix in
theorem delta_theta2 (a b : G) : delta φ (theta2 (φ := φ) ω) a b = 0 := by
  simp only [delta, theta2]
  rw [defect_phi hfix a, defect_phi hfix b, sub_self]

omit [AddCommGroup W] in
theorem delta_d1 {W : Type*} [AddCommGroup W] (σ : G → W) (a b : G) :
    delta φ (d1 σ) a b = d1 (delta1 φ σ) a b := by
  simp only [delta, d1, delta1, map_mul]
  abel

theorem delta_sub (f g : G → G → W) (a b : G) :
    delta φ (fun x y => f x y - g x y) a b = delta φ f a b - delta φ g a b := by
  simp only [delta]
  abel

/-- The explicit primitive of `Δ³ ω`. -/
def cubePrimitive (ω : G → G → W) : G → W :=
  fun a => -(delta1 φ (delta1 φ (tau (φ := φ) ω)) a)

include hcen hfix hω in
/-- **Unipotence of a central twist.** `Δ (Δ (Δ ω))` is the coboundary of
`cubePrimitive ω`. -/
theorem delta_cube (a b : G) :
    delta φ (delta φ (delta φ ω)) a b = d1 (cubePrimitive (φ := φ) ω) a b := by
  have h1 : delta φ ω = fun x y => theta (φ := φ) ω x y - d1 (tau (φ := φ) ω) x y := by
    funext x y; exact delta_eq hcen hω x y
  have h2 : delta φ (delta φ ω) = fun x y => theta2 (φ := φ) ω x y -
      d1 (delta1 φ (tau (φ := φ) ω)) x y := by
    funext x y
    rw [h1, delta_sub, delta_theta hcen hfix hω, delta_d1]
  rw [h2, delta_sub, delta_theta2 hfix, delta_d1]
  simp only [d1, cubePrimitive]
  abel

end Twist

end TernaryPeriodPolynomials.FlagExactness.CentralTwist
