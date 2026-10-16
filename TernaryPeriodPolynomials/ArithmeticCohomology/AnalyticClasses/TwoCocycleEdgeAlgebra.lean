module

public import Mathlib

@[expose] public section


/-!
# Algebra of homogeneous two-cocycles and of the mixed edge function

Let a group `G` act on an additive group `V` (by a `DistribMulAction`).

* A homogeneous two-cochain `C` on vertex triples which is `G`-equivariant and closed (the four-face
  alternating sum vanishes) gives an inhomogeneous two-cocycle `t (a, b) := C (1, a, a b)`.
* For an inhomogeneous two-cocycle `t` and elements `m, r` put
  `f m r := t (m, m⁻¹ r m) - t (r, m)`. Then, for all `m₁ m₂ r`,
  `f (m₁ m₂) r = f m₁ r + m₁ • f m₂ (m₁⁻¹ r m₁) + (r • t (m₁, m₂) - t (m₁, m₂))`.
  No relativity of `t` on any subgroup is needed. This is the algebraic core of the derivative
  edge map of the good-line transfer.
* The homogeneous cochain `ρ (Q₀) c (Q₀⁻¹ Q₁, Q₁⁻¹ Q₂)` built from an inhomogeneous cocycle `c` is
  closed and equivariant.

Original work by Claude Opus 5.5 (AxiomCode).
-/

namespace TernaryPeriodPolynomials.AnalyticClasses

section EdgeAlgebra

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

/-- Inhomogeneous two-cocycles for a distributive action. -/
def IsTwoCocycle (t : G → G → V) : Prop :=
  ∀ a b c : G, a • t b c - t (a * b) c + t a (b * c) - t a b = 0

/-- The mixed edge function of a two-cochain. -/
def mixedEdgeFunction (t : G → G → V) (m r : G) : V := t m (m⁻¹ * r * m) - t r m

/-- **Cocycle law of the mixed edge function.** -/
theorem mixedEdgeFunction_mul {t : G → G → V} (ht : IsTwoCocycle t) (m₁ m₂ r : G) :
    mixedEdgeFunction t (m₁ * m₂) r =
      mixedEdgeFunction t m₁ r + m₁ • mixedEdgeFunction t m₂ (m₁⁻¹ * r * m₁) +
        (r • t m₁ m₂ - t m₁ m₂) := by
  unfold mixedEdgeFunction
  set r' := m₁⁻¹ * r * m₁
  set r'' := m₂⁻¹ * r' * m₂
  have e1 := ht m₁ m₂ r''
  have e2 := ht m₁ r' m₂
  have e3 := ht r m₁ m₂
  have h1 : m₂ * r'' = r' * m₂ := by simp [r'', mul_assoc]
  have h2 : m₁ * r' = r * m₁ := by simp [r', mul_assoc]
  have h3 : (m₁ * m₂)⁻¹ * r * (m₁ * m₂) = r'' := by simp [r'', r', mul_assoc]
  rw [h1] at e1
  rw [h2] at e2
  rw [h3, smul_sub]
  have lhs : t (m₁ * m₂) r'' = m₁ • t m₂ r'' + t m₁ (r' * m₂) - t m₁ m₂ := by
    linear_combination (norm := abel) -e1
  have mid : t m₁ (r' * m₂) = t (r * m₁) m₂ - m₁ • t r' m₂ + t m₁ r' := by
    linear_combination (norm := abel) e2
  have last : t r (m₁ * m₂) = t (r * m₁) m₂ - r • t m₁ m₂ + t r m₁ := by
    linear_combination (norm := abel) e3
  rw [lhs, mid, last]
  abel

end EdgeAlgebra

section Homogeneous

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

/-- The homogeneous two-cochain of an inhomogeneous one. -/
def homogeneousOfInhomogeneous (c : G → G → V) (Q : Fin 3 → G) : V :=
  Q 0 • c ((Q 0)⁻¹ * Q 1) ((Q 1)⁻¹ * Q 2)

theorem homogeneousOfInhomogeneous_smul (c : G → G → V) (p : G) (Q : Fin 3 → G) :
    homogeneousOfInhomogeneous c (fun i => p * Q i) = p • homogeneousOfInhomogeneous c Q := by
  unfold homogeneousOfInhomogeneous
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_smul]

/-- The alternating face sum of a homogeneous two-cochain on four vertices. -/
def faceSum (C : (Fin 3 → G) → V) (Q : Fin 4 → G) : V :=
  C ![Q 1, Q 2, Q 3] - C ![Q 0, Q 2, Q 3] + C ![Q 0, Q 1, Q 3] - C ![Q 0, Q 1, Q 2]

/-- **The homogeneous cochain of a cocycle is closed.** -/
theorem faceSum_homogeneousOfInhomogeneous {c : G → G → V} (hc : IsTwoCocycle c)
    (Q : Fin 4 → G) : faceSum (homogeneousOfInhomogeneous c) Q = 0 := by
  unfold faceSum homogeneousOfInhomogeneous
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  set a := (Q 0)⁻¹ * Q 1
  set b := (Q 1)⁻¹ * Q 2
  set d := (Q 2)⁻¹ * Q 3
  have e := hc a b d
  have hQ1 : Q 1 = Q 0 * a := by simp [a]
  have hab : (Q 0)⁻¹ * Q 2 = a * b := by simp [a, b, mul_assoc]
  have hbd : (Q 1)⁻¹ * Q 3 = b * d := by simp [b, d, mul_assoc]
  rw [hab, hbd, hQ1, mul_smul]
  rw [← smul_sub, ← smul_add, ← smul_sub, e, smul_zero]

/-- The inhomogeneous cochain of a homogeneous one, with first vertex `1`. -/
def inhomogeneousOfHomogeneous (C : (Fin 3 → G) → V) (a b : G) : V := C ![1, a, a * b]

/-- **An equivariant closed homogeneous cochain gives an inhomogeneous cocycle.** -/
theorem isTwoCocycle_inhomogeneousOfHomogeneous {C : (Fin 3 → G) → V}
    (equivariant : ∀ (p : G) (Q : Fin 3 → G), C (fun i => p * Q i) = p • C Q)
    (closed : ∀ Q : Fin 4 → G, faceSum C Q = 0) :
    IsTwoCocycle (inhomogeneousOfHomogeneous C) := by
  intro a b d
  unfold inhomogeneousOfHomogeneous
  have shift : a • C ![1, b, b * d] = C ![a, a * b, a * b * d] := by
    rw [← equivariant]
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc]
  have face := closed ![1, a, a * b, a * b * d]
  unfold faceSum at face
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_three] at face
  rw [shift, ← mul_assoc]
  exact face

end Homogeneous

end TernaryPeriodPolynomials.AnalyticClasses
