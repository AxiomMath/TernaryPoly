module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Action

@[expose] public section


/-!
# The line coefficient polynomial `P_τ = τZ - Y` under the line parabolic group (LS3)

`rho_lmat_Ppoly`: `ρ([[1, v], [0, C]]) P_τ = (cτ+d) P_{C·τ}`.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry (lineParabolic)

/-- `P_τ = τ Z - Y`. -/
def Ppoly (τ : ℂ) : MvPolynomial (Fin 3) ℂ := C τ * X 2 - X 1

theorem Ppoly_isHomogeneous (τ : ℂ) : (Ppoly τ).IsHomogeneous 1 :=
  (isHomogeneous_C_mul_X _ _).sub (isHomogeneous_X ℂ _)

/-- The entries of the inverse of a determinant-one `2 × 2` matrix (the adjugate). -/
theorem inv_entries (γ : GL (Fin 2) ℝ) (h : γ.det = 1) :
    ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = γ 1 1 ∧
    ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -γ 0 1 ∧
    ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -γ 1 0 ∧
    ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = γ 0 0 := by
  have hd : (γ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    simpa [Matrix.GeneralLinearGroup.det] using congrArg Units.val h
  have e : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ :=
    Matrix.coe_units_inv γ
  rw [e, Matrix.inv_def, hd, Matrix.adjugate_fin_two]
  simp

theorem rho_lmat_Ppoly {G : Type} [Group G] (D : LineData G) (g : G) {τ : ℂ} (hτ : 0 < τ.im) :
    rho (D.lmat g) (Ppoly τ) = C (dnm (D.lam g) τ) * Ppoly (mob (D.lam g) τ) := by
  have hinv : (D.lmat g)⁻¹ = D.lmat g⁻¹ :=
    Matrix.inv_eq_right_inv (by rw [← D.lmat_mul, mul_inv_cancel, D.lmat_one])
  have hdet : (D.lmat g).det = 1 := D.det_lmat g
  obtain ⟨e00, e01, e10, e11⟩ := inv_entries (D.lam g) (D.det_one g)
  have hd := det_eq_one (D.lam g) (D.det_one g)
  have hne : dnm (D.lam g) τ ≠ 0 := dnm_ne_zero _ hτ
  have hl : (D.lam g⁻¹ : GL (Fin 2) ℝ) = (D.lam g)⁻¹ := map_inv _ _
  unfold rho Ppoly
  rw [hinv, hdet]
  simp only [map_sub, map_mul, bind₁_C_right, bind₁_X_right, Fin.sum_univ_three]
  simp only [LineData.lmat, lineParabolic, hl]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
  rw [e00, e01, e10, e11]
  have hm : dnm (D.lam g) τ * mob (D.lam g) τ = ((D.lam g 0 0 : ℝ) : ℂ) * τ + ((D.lam g 0 1 : ℝ) : ℂ) := by
    unfold mob; exact mul_div_cancel₀ _ hne
  have hr : (C (dnm (D.lam g) τ) * (C (mob (D.lam g) τ) * X 2 - X 1) : MvPolynomial (Fin 3) ℂ) =
      C (((D.lam g 0 0 : ℝ) : ℂ) * τ + ((D.lam g 0 1 : ℝ) : ℂ)) * X 2 - C (dnm (D.lam g) τ) * X 1 := by
    rw [← hm, map_mul]; ring
  refine Eq.trans ?_ hr.symm
  simp only [Complex.ofReal_one, inv_one, map_one, one_mul, Complex.ofReal_zero, map_zero, zero_mul, zero_add,
    Complex.ofReal_neg, dnm, map_add, map_mul, map_neg]
  ring

theorem rho_isHomogeneous_general (M : Matrix (Fin 3) (Fin 3) ℝ) {m : ℕ} {q : MvPolynomial (Fin 3) ℂ}
    (hq : q.IsHomogeneous m) : (rho M q).IsHomogeneous m := by
  have hlin : ∀ i : Fin 3, (∑ j : Fin 3, C (((M⁻¹ i j : ℝ)) : ℂ) * X j : MvPolynomial (Fin 3) ℂ).IsHomogeneous 1 :=
    fun i => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  have := hq.aeval (fun i : Fin 3 => ∑ j : Fin 3, C (((M⁻¹ i j : ℝ)) : ℂ) * X j) hlin
  have h0 := (isHomogeneous_C (Fin 3) (((M.det⁻¹ : ℝ)) : ℂ)).mul this
  simpa [rho, aeval_eq_bind₁] using h0

theorem rho_lmat_isHomogeneous {G : Type} [Group G] (D : LineData G) (g : G) {m : ℕ}
    {q : MvPolynomial (Fin 3) ℂ} (hq : q.IsHomogeneous m) : (rho (D.lmat g) q).IsHomogeneous m :=
  rho_isHomogeneous_general _ hq

end TernaryPeriodPolynomials.Argument.LineSeed
