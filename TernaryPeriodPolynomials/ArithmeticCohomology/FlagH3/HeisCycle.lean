module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.CycleFunctional

@[expose] public section


/-!
# The Heisenberg `3`-cocycle and the Heisenberg bar `3`-cycle

Formalized by Claude Sonnet 5.5.

A group `B` with `HeisCoords` is (a subgroup of) the Heisenberg group of unipotent upper triangular integer matrices: coordinates `a = γ₀₁`, `b = γ₁₂`, `c = γ₀₂` with
`a, b` additive and `c(gh) = c g + c h + a g · b h`, jointly injective.  The polynomial `3`-cochain `θ(g₁,g₂,g₃) = b(g₁) a(g₂) (2 c(g₃) + a(g₂) b(g₃))` is a cocycle (`theta_cocycle`),
and for elements `X`, `Y` with coordinates `(p,0,0)`, `(0,q,0)` the seven-term bar chain `heisCycle X Y` (a lift of the fundamental class of the nilmanifold, built from the Wang
sequence of `B → ℤ`) is a cycle (`cycle_isCycle`) on which `θ` takes the value `-2 p² q²` (`cycle_theta`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FlagH3

variable {B : Type} [Group B]

/-- Heisenberg coordinates on a group: the matrix entries `(γ₀₁, γ₁₂, γ₀₂)` of a unipotent upper triangular matrix. -/
structure HeisCoords (B : Type) [Group B] where
  a : B → ℤ
  b : B → ℤ
  c : B → ℤ
  a_mul : ∀ g h, a (g * h) = a g + a h
  b_mul : ∀ g h, b (g * h) = b g + b h
  c_mul : ∀ g h, c (g * h) = c g + c h + a g * b h
  inj : ∀ g h, a g = a h → b g = b h → c g = c h → g = h

namespace HeisCoords

variable (H : HeisCoords B)

/-- The Heisenberg `3`-cocycle `θ(g₁,g₂,g₃) = b(g₁) a(g₂) (2 c(g₃) + a(g₂) b(g₃))`. -/
def theta (g : Fin 3 → B) : ℚ :=
  (H.b (g 0) : ℚ) * (H.a (g 1) : ℚ) * (2 * (H.c (g 2) : ℚ) + (H.a (g 1) : ℚ) * (H.b (g 2) : ℚ))

theorem theta_cocycle : dThree H.theta = 0 := by
  funext g
  rw [dThree_apply]
  simp only [theta]
  simp [H.a_mul, H.b_mul, H.c_mul]
  ring


theorem a_one : H.a 1 = 0 := by
  have := H.a_mul 1 1
  simp at this
  omega

theorem b_one : H.b 1 = 0 := by
  have := H.b_mul 1 1
  simp at this
  omega

theorem c_one : H.c 1 = 0 := by
  have := H.c_mul 1 1
  simp [H.a_one] at this
  omega

theorem a_inv (g : B) : H.a g⁻¹ = - H.a g := by
  have := H.a_mul g g⁻¹
  simp [H.a_one] at this
  omega

theorem b_inv (g : B) : H.b g⁻¹ = - H.b g := by
  have := H.b_mul g g⁻¹
  simp [H.b_one] at this
  omega

theorem c_inv (g : B) : H.c g⁻¹ = - H.c g + H.a g * H.b g := by
  have := H.c_mul g g⁻¹
  simp [H.c_one, H.b_inv] at this
  linarith

/-- The coordinate triple. -/
def kappa (g : B) : ℤ × ℤ × ℤ := (H.a g, H.b g, H.c g)

theorem kappa_injective : Function.Injective H.kappa := by
  intro g h hgh
  simp only [kappa, Prod.mk.injEq] at hgh
  exact H.inj g h hgh.1 hgh.2.1 hgh.2.2

/-- A function of two group elements is a function of their coordinates. -/
theorem two_var (α : (Fin 2 → B) → ℚ) :
    ∃ F : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) → ℚ, ∀ u v : B, α ![u, v] = F (H.kappa u) (H.kappa v) := by
  classical
  have : Nonempty B := ⟨1⟩
  refine ⟨fun k l => α ![Function.invFun H.kappa k, Function.invFun H.kappa l], fun u v => ?_⟩
  simp [Function.leftInverse_invFun H.kappa_injective u, Function.leftInverse_invFun H.kappa_injective v]


end HeisCoords


/-- The commutator `[X,Y]`. -/
def comm (X Y : B) : B := X * Y * X⁻¹ * Y⁻¹

/-- The bar `3`-cycle of the Heisenberg group (`W = [X,Y]`, `Y' = X⁻¹ Y X`). -/
def heisCycle (X Y : B) : (Fin 3 → B) →₀ ℚ :=
  Finsupp.single ![X, X⁻¹ * Y * X, comm X Y] 1 - Finsupp.single ![Y, X, comm X Y] 1 +
    Finsupp.single ![Y, comm X Y, X] 1 - Finsupp.single ![X, comm X Y, X⁻¹ * Y * X] 1 +
    Finsupp.single ![comm X Y, X, X⁻¹ * Y * X] 1 - Finsupp.single ![comm X Y, Y, X] 1 -
    Finsupp.single ![comm X Y, X⁻¹ * Y * X, comm X Y] 1

namespace HeisCoords

variable (H : HeisCoords B)

theorem cycle_isCycle (X Y : B) (p q : ℤ) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0)
    (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0) : IsCycle (heisCycle X Y) := by
  intro α
  obtain ⟨F, hF⟩ := H.two_var α
  simp only [heisCycle, chainEval_add, chainEval_sub, chainEval_single, dTwo_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
    Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, hF, comm,
    HeisCoords.kappa, H.a_mul, H.b_mul, H.c_mul, H.a_inv, H.b_inv, H.c_inv, hXa, hXb, hXc, hYa, hYb, hYc]
  ring_nf


theorem cycle_theta (X Y : B) (p q : ℤ) (hXa : H.a X = p) (hXb : H.b X = 0) (hXc : H.c X = 0)
    (hYa : H.a Y = 0) (hYb : H.b Y = q) (hYc : H.c Y = 0) :
    chainEval (heisCycle X Y) H.theta = -2 * (p : ℚ) ^ 2 * (q : ℚ) ^ 2 := by
  simp only [heisCycle, chainEval_add, chainEval_sub, chainEval_single, theta, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, comm, H.a_mul, H.b_mul, H.c_mul, H.a_inv, H.b_inv, H.c_inv, hXa, hXb, hXc, hYa, hYb, hYc]
  push_cast
  ring_nf


end HeisCoords

end TernaryPeriodPolynomials.Argument.FlagH3
