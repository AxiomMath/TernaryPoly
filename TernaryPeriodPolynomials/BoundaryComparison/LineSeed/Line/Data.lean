module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.PlaneRep
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Line.Iwasawa

@[expose] public section


/-!
# Line parabolic groups (line mirror of `SeedC3.PlaneGroup`, `SeedC3.PlaneRep`)

A group `G` with a Levi block `lam : G →* GL₂(ℝ)` of determinant one and a radical row vector `v : G → ℝ²` with the
semidirect-product law `v(gh) = v(h) + v(g) · lam(h)` is the group of the matrices `[[1, v], [0, lam]]` of the line parabolic
(the stabilizer of the line `⟨e₁⟩`; e.g. the determinant-one part of the good-line stabilizer after the pivot `e₁ ↔ e₃`).  It acts on the
line face `{(w, τ)}` (`LineAction`) and on the coefficients `E_n = Sym^n((ℂ³)*) ⊗ det⁻¹` through the matrix `[[1, v], [0, lam]]`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (lineParabolic)

/-- The abstract line parabolic group data. -/
structure LineData (G : Type) [Group G] where
  lam : G →* GL (Fin 2) ℝ
  v : G → (Fin 2 → ℝ)
  det_one : ∀ g, (lam g).det = 1
  v_mul : ∀ g h, v (g * h) = v h + Matrix.vecMul (v g) (lam h : Matrix (Fin 2) (Fin 2) ℝ)

namespace LineData

variable {G : Type} [Group G] (D : LineData G)

theorem v_one : D.v 1 = 0 := by
  have h := D.v_mul 1 1
  simp only [mul_one, map_one, Units.val_one, Matrix.vecMul_one] at h
  have : D.v 1 + 0 = D.v 1 + D.v 1 := by rw [add_zero]; exact h
  exact (add_left_cancel this).symm

/-- The `3 × 3` matrix `[[1, v(g)], [0, lam(g)]]`. -/
def lmat (g : G) : Matrix (Fin 3) (Fin 3) ℝ :=
  lineParabolic 1 (D.v g) ((D.lam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)

theorem lmat_mul (g h : G) : D.lmat (g * h) = D.lmat g * D.lmat h := by
  ext i j
  simp only [lmat, lineParabolic, map_mul, Units.val_mul, D.v_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem lmat_one : D.lmat 1 = 1 := by
  ext i j
  simp only [lmat, lineParabolic, map_one, Units.val_one, D.v_one]
  fin_cases i <;> fin_cases j <;> simp

theorem det_lmat (g : G) : (D.lmat g).det = 1 := by
  have h := D.det_one g
  have h2 : ((D.lam g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val h
  simp [lmat, lineParabolic, Matrix.det_fin_three, Matrix.det_fin_two] at h2 ⊢
  linarith

/-- The embedding into `GL₃(ℝ)`. -/
def sigma : G →* GL (Fin 3) ℝ where
  toFun g := ⟨D.lmat g, D.lmat g⁻¹, by rw [← D.lmat_mul, mul_inv_cancel, D.lmat_one],
    by rw [← D.lmat_mul, inv_mul_cancel, D.lmat_one]⟩
  map_one' := Units.ext D.lmat_one
  map_mul' g h := Units.ext (D.lmat_mul g h)

@[simp] theorem sigma_val (g : G) : ((D.sigma g : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = D.lmat g := rfl

/-- The coefficient representation (over `ℂ`) of the line parabolic group. -/
def rhoC (n : ℕ) : Representation ℂ G (HomogeneousPoly n) :=
  (GeneralEisenstein.realCoefficient n).comp D.sigma

theorem rhoC_coe (n : ℕ) (g : G) (q : HomogeneousPoly n) :
    ((D.rhoC n g q : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      rho (D.lmat g) (q : MvPolynomial (Fin 3) ℂ) := by
  have hinv : (D.lmat g)⁻¹ = D.lmat g⁻¹ :=
    Matrix.inv_eq_right_inv (by rw [← D.lmat_mul, mul_inv_cancel, D.lmat_one])
  have hdet : (D.lmat g).det = 1 := D.det_lmat g
  unfold rhoC
  change ((GeneralEisenstein.action (-1)
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (D.sigma g))) (q : MvPolynomial (Fin 3) ℂ)) = _
  rw [GeneralEisenstein.action_apply]
  unfold rho GeneralEisenstein.substitute GeneralEisenstein.linearForm
  rw [hinv, hdet]
  simp [GeneralEisenstein.determinantCharacter, Matrix.GeneralLinearGroup.map]
  have hd : ((D.lmat g).map Complex.ofReal).det = 1 := by
    have := RingHom.map_det Complex.ofRealHom (D.lmat g)
    rw [hdet, map_one] at this
    exact this.symm
  rw [hd, inv_one, one_smul, hinv]

/-- The coefficient action on the normed model `Coef n`. -/
def rhoCoef (n : ℕ) (g : G) : Coef n →ₗ[ℂ] Coef n := D.rhoC n g

/-- The real coefficient representation on the normed model `Coef n` (mirror of `PlaneData.rhoR`). -/
def rhoR (n : ℕ) : Representation ℝ G (Coef n) where
  toFun g := (D.rhoCoef n g).restrictScalars ℝ
  map_one' := by
    ext q
    change D.rhoC n 1 q = q
    rw [map_one]; rfl
  map_mul' g k := by
    ext q
    change D.rhoC n (g * k) q = D.rhoC n g (D.rhoC n k q)
    rw [map_mul]; rfl

theorem rhoR_apply (n : ℕ) (g : G) (q : Coef n) : D.rhoR n g q = D.rhoCoef n g q := rfl

theorem toPoly_rhoCoef (n : ℕ) (g : G) (q : Coef n) :
    Coef.toPoly (D.rhoCoef n g q) = rho (D.lmat g) (Coef.toPoly q) := D.rhoC_coe n g q

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
