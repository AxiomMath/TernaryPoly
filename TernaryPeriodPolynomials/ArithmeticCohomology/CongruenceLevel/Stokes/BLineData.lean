module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Data

@[expose] public section


/-!
# Line data: the algebra behind the `H³` classes of the line (plane) stabilizers

Formalized by Claude Sonnet 5.5.

A *line datum* on a group `G` is a pair of maps `A : G → M₂(ℤ)` (a homomorphism into the matrices of determinant one) and `v : G → ℤ²` (rows) with `v(gh) = v(g) A(h) + v(h)`; this is the
shape of the entries `([[1, v], [0, A]])` of the elements of the stabilizer of a line.  The form `β(g,h) = ω(v(g)A(h), v(h))` (`ω` the standard symplectic form) is a `2`-cocycle with
trivial rational coefficients (`LineData.beta_cocycle`), and for an additive `u : G → ℚ` the cup product `u(g₀) β(g₁,g₂)` is a `3`-cocycle (`LineData.cup_cocycle`).
`translate` (adding the coboundary `w(1 - A)` to `v`) changes `β` by a coboundary (`beta_translate`), and a change of basis by an invertible integer matrix `Q` multiplies `β` by `det Q` (`beta_basis`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open Matrix TernaryPeriodPolynomials.Argument.FlagH3

/-- The standard symplectic form on `ℤ²`. -/
def omega (x y : Fin 2 → ℤ) : ℤ := x 0 * y 1 - x 1 * y 0

theorem omega_vecMul (M : Matrix (Fin 2) (Fin 2) ℤ) (x y : Fin 2 → ℤ) :
    omega (x ᵥ* M) (y ᵥ* M) = M.det * omega x y := by
  simp [omega, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem omega_add_left (x x' y : Fin 2 → ℤ) : omega (x + x') y = omega x y + omega x' y := by
  simp [omega]; ring

theorem omega_add_right (x y y' : Fin 2 → ℤ) : omega x (y + y') = omega x y + omega x y' := by
  simp [omega]; ring

theorem omega_sub_left (x x' y : Fin 2 → ℤ) : omega (x - x') y = omega x y - omega x' y := by
  simp [omega]; ring

theorem omega_sub_right (x y y' : Fin 2 → ℤ) : omega x (y - y') = omega x y - omega x y' := by
  simp [omega]; ring

theorem omega_smul_left (c : ℤ) (x y : Fin 2 → ℤ) : omega (c • x) y = c * omega x y := by
  simp [omega]; ring

theorem omega_smul_right (c : ℤ) (x y : Fin 2 → ℤ) : omega x (c • y) = c * omega x y := by
  simp [omega]; ring

theorem omega_skew (x y : Fin 2 → ℤ) : omega y x = - omega x y := by
  simp [omega]; ring

theorem omega_self (x : Fin 2 → ℤ) : omega x x = 0 := by
  simp [omega]; ring

/-- A line datum on a group. -/
structure LineData (G : Type) [Group G] where
  A : G → Matrix (Fin 2) (Fin 2) ℤ
  v : G → Fin 2 → ℤ
  A_mul : ∀ g h, A (g * h) = A g * A h
  det_one : ∀ g, (A g).det = 1
  v_mul : ∀ g h, v (g * h) = v g ᵥ* A h + v h

namespace LineData

variable {G : Type} [Group G] (D : LineData G)

/-- The `2`-cocycle `β(g,h) = ω(v(g) A(h), v(h))`. -/
def beta (g h : G) : ℚ := (omega (D.v g ᵥ* D.A h) (D.v h) : ℤ)

theorem beta_cocycle (g h k : G) : D.beta h k - D.beta (g * h) k + D.beta g (h * k) - D.beta g h = 0 := by
  have h1 : omega ((D.v g ᵥ* D.A h) ᵥ* D.A k) (D.v h ᵥ* D.A k) = omega (D.v g ᵥ* D.A h) (D.v h) := by
    rw [omega_vecMul, D.det_one k, one_mul]
  have e1 : D.beta (g * h) k = (omega ((D.v g ᵥ* D.A h) ᵥ* D.A k) (D.v k) : ℤ) + (omega (D.v h ᵥ* D.A k) (D.v k) : ℤ) := by
    simp only [beta, D.v_mul, Matrix.add_vecMul, omega_add_left]
    push_cast
    rfl
  have e2 : D.beta g (h * k) = (omega ((D.v g ᵥ* D.A h) ᵥ* D.A k) (D.v h ᵥ* D.A k) : ℤ) +
      (omega ((D.v g ᵥ* D.A h) ᵥ* D.A k) (D.v k) : ℤ) := by
    simp only [beta, D.v_mul, D.A_mul, Matrix.vecMul_vecMul, omega_add_right]
    push_cast
    rfl
  have e3 : D.beta h k = (omega (D.v h ᵥ* D.A k) (D.v k) : ℤ) := rfl
  have e4 : D.beta g h = (omega (D.v g ᵥ* D.A h) (D.v h) : ℤ) := rfl
  rw [e1, e2, e3, e4]
  have h3 : ((omega ((D.v g ᵥ* D.A h) ᵥ* D.A k) (D.v h ᵥ* D.A k) : ℤ) : ℚ) = ((omega (D.v g ᵥ* D.A h) (D.v h) : ℤ) : ℚ) := by
    exact_mod_cast h1
  rw [h3]
  ring

/-- Adding the coboundary `w (1 - A)` to `v`. -/
def translate (w : Fin 2 → ℤ) : LineData G where
  A := D.A
  v g := D.v g + w ᵥ* (1 - D.A g)
  A_mul := D.A_mul
  det_one := D.det_one
  v_mul g h := by
    rw [D.v_mul, D.A_mul]
    simp only [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_sub, Matrix.sub_vecMul, Matrix.vecMul_one]
    abel

/-- The primitive of the change of `β` under translation. -/
def eta (w : Fin 2 → ℤ) (g : G) : ℤ := -omega (D.v g) w + omega (w ᵥ* D.A g) (D.v g) - omega w (w ᵥ* D.A g)

theorem trans_aux (x y w : Fin 2 → ℤ) (X Y : Matrix (Fin 2) (Fin 2) ℤ) (hY : Y.det = 1) :
    omega ((x + w ᵥ* (1 - X)) ᵥ* Y) (y + w ᵥ* (1 - Y)) =
      omega (x ᵥ* Y) y +
      ((-omega y w + omega (w ᵥ* Y) y - omega w (w ᵥ* Y)) -
        (-omega (x ᵥ* Y + y) w + omega (w ᵥ* (X * Y)) (x ᵥ* Y + y) - omega w (w ᵥ* (X * Y))) +
        (-omega x w + omega (w ᵥ* X) x - omega w (w ᵥ* X))) := by
  rw [Matrix.det_fin_two] at hY
  simp only [omega, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Matrix.mul_apply, Pi.add_apply]
  simp
  linear_combination ((-(x 0 * w 1) + x 1 * w 0) + (-(x 0 * w 0 * X 0 1) - x 0 * w 1 * X 1 1 + w 0 * w 1 * X 0 0 + w 0 * X 0 0 * x 1 - w 0 * w 1 * X 1 1 - w 0 ^ 2 * X 0 1 + w 1 * X 1 0 * x 1 + w 1 ^ 2 * X 1 0)) * hY

/-- **Translation changes `β` by a coboundary.** -/
theorem beta_translate (w : Fin 2 → ℤ) (g h : G) :
    (D.translate w).beta g h = D.beta g h + ((D.eta w h : ℤ) - (D.eta w (g * h) : ℤ) + (D.eta w g : ℤ)) := by
  have h1 := trans_aux (D.v g) (D.v h) w (D.A g) (D.A h) (D.det_one h)
  have h2 : omega ((D.v g + w ᵥ* (1 - D.A g)) ᵥ* D.A h) (D.v h + w ᵥ* (1 - D.A h)) =
      omega (D.v g ᵥ* D.A h) (D.v h) + (D.eta w h - D.eta w (g * h) + D.eta w g) := by
    rw [h1]
    simp only [eta, D.v_mul, D.A_mul]
  simp only [beta, translate]
  rw [h2]
  push_cast
  ring

/-- **A change of basis by an invertible integer matrix multiplies `β` by its determinant.** -/
theorem beta_basis (D D'' : LineData G) (Q Q' : Matrix (Fin 2) (Fin 2) ℤ) (hQQ' : Q * Q' = 1) (ε : ℤ) (hε : ε * ε = 1)
    (hA : ∀ g, D.A g = Q' * D''.A g * Q) (hv : ∀ g, D.v g = ε • (D''.v g ᵥ* Q)) (g h : G) :
    D.beta g h = Q.det * D''.beta g h := by
  have e1 : D.v g ᵥ* D.A h = ε • ((D''.v g ᵥ* D''.A h) ᵥ* Q) := by
    have hm : Q * (Q' * D''.A h * Q) = D''.A h * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [hv g, hA h, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hm]
  have e2 : omega (D.v g ᵥ* D.A h) (D.v h) = Q.det * omega (D''.v g ᵥ* D''.A h) (D''.v h) := by
    rw [e1, hv h, omega_smul_left, omega_smul_right, omega_vecMul, ← mul_assoc, hε, one_mul]
  simp only [beta]
  rw [e2]
  push_cast
  ring

/-- **The cup product with an additive function, evaluated on a bar `3`-cycle, only depends on the datum up to translation and change of basis.** -/
theorem cup_eval_change (z : (Fin 3 → G) →₀ ℚ) (hz : IsCycle z) (u : G → ℚ) (hu : ∀ g h, u (g * h) = u g + u h)
    (D D' : LineData G) (Q Q' : Matrix (Fin 2) (Fin 2) ℤ) (hQQ' : Q * Q' = 1) (ε : ℤ) (hε : ε * ε = 1) (w : Fin 2 → ℤ)
    (hA : ∀ g, D.A g = Q' * D'.A g * Q) (hv : ∀ g, D.v g = ε • ((D'.v g + w ᵥ* (1 - D'.A g)) ᵥ* Q)) :
    chainEval z (fun g : Fin 3 → G => u (g 0) * D.beta (g 1) (g 2)) =
      Q.det * chainEval z (fun g : Fin 3 → G => u (g 0) * D'.beta (g 1) (g 2)) := by
  have hb : ∀ g h, D.beta g h = Q.det * (D'.beta g h + (((D'.eta w h : ℤ) : ℚ) - ((D'.eta w (g * h) : ℤ) : ℚ) + ((D'.eta w g : ℤ) : ℚ))) := by
    intro g h
    rw [← beta_translate D' w g h]
    exact beta_basis D (D'.translate w) Q Q' hQQ' ε hε hA hv g h
  set f : (Fin 2 → G) → ℚ := fun x => u (x 0) * ((D'.eta w (x 1) : ℤ) : ℚ) with hf
  have hpt : (fun g : Fin 3 → G => u (g 0) * D.beta (g 1) (g 2)) =
      (Q.det : ℚ) • (fun g : Fin 3 → G => u (g 0) * D'.beta (g 1) (g 2)) - (Q.det : ℚ) • dTwo f := by
    funext g
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hb, dTwo_apply]
    simp only [hf, Matrix.cons_val_zero, Matrix.cons_val_one, hu]
    ring
  rw [← chainEvalL_apply, ← chainEvalL_apply, hpt, map_sub, map_smul, map_smul]
  have h0 : chainEvalL z (dTwo f) = 0 := hz f
  rw [h0]
  simp

end LineData

end TernaryPeriodPolynomials.Argument.GammaNStokes
