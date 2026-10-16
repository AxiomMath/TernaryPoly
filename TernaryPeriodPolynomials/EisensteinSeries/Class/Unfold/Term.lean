module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Unfold.Levi
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.ClosedTerms
public import TernaryPeriodPolynomials.EisensteinSeries.ConstantTerms.Equivariance

@[expose] public section


/-!
# Translations of the summand and coefficient expansions

`nmat v` is the radical translation matrix `n(v)`. `summandPoly_mul_nmat`: the summand at `g n(v)` is
`ρ(n(-v))` applied to the summand at `g` evaluated at the translated point; `coeff_summandPoly_mul_nmat`
expands its coefficients as a finite combination (over the monomials of degree `n`) of the coefficients
of the summand at `g`, with the polynomial-in-`v` weights `(ρ(n(-v)) X^{m'})_m`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open MvPolynomial
noncomputable section
namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument

/-- The radical translation matrix of a vector. -/
def nmat (v : Fin 2 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := transMat (v 0) (v 1)

theorem nmat_mul (v w : Fin 2 → ℝ) : nmat v * nmat w = nmat (v + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nmat, transMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem nmat_zero : nmat (0 : Fin 2 → ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nmat, transMat]

theorem det_nmat (v : Fin 2 → ℝ) : (nmat v).det = 1 := det_transMat _ _

theorem inv_transMat (v w : ℝ) : (transMat v w)⁻¹ = transMat (-v) (-w) := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem formPullback_add_const (ω : (Fin 5 → ℝ) → Fin 5 → Fin 5 → MvPolynomial (Fin 3) ℂ)
    (c x : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback (fun y => y + c) ω x i j = ω (x + c) i j := by
  unfold formPullback
  rw [fderiv_add_const, fderiv_fun_id]
  simp only [ContinuousLinearMap.id_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro a _ ha
    simp [Pi.single_apply, ha]
  · simp

theorem nmat_inv (v : Fin 2 → ℝ) : (nmat v)⁻¹ = nmat (-v) := by
  unfold nmat
  rw [inv_transMat]
  rfl

/-- Right multiplication by a translation: the summand at `g n(v)` is the `ρ(n(-v))`-transport of the
summand at `g` evaluated at the translated point. -/
theorem summandPoly_mul_nmat (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ} (hg : g.det = 1)
    (v : Fin 2 → ℝ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5) :
    summandPoly n h (g * nmat v) q i j =
      rho (nmat (-v)) (summandPoly n h g (q + ![v 0, v 1, 0, 0, 0]) i j) := by
  rw [summandPoly_mul_eq n h hg (det_nmat v) hq, nmat_inv]
  congr 1
  have hev : planeAct (nmat v) =ᶠ[nhds q] fun y => y + ![v 0, v 1, 0, 0, 0] :=
    Filter.eventuallyEq_of_mem (isOpen_Omega.mem_nhds hq) fun y hy => planeAct_transMat _ _ hy
  rw [formPullback_congr _ hev, formPullback_add_const]

theorem coeff_summandPoly_mul_nmat (n : ℕ) (h : ℂ → ℂ) {g : Matrix (Fin 3) (Fin 3) ℝ}
    (hg : g.det = 1) (v : Fin 2 → ℝ) {q : Fin 5 → ℝ} (hq : q ∈ Omega) (i j : Fin 5)
    (m : Fin 3 →₀ ℕ) :
    (summandPoly n h (g * nmat v) q i j).coeff m =
      ∑ m' ∈ monSet n, (summandPoly n h g (q + ![v 0, v 1, 0, 0, 0]) i j).coeff m' *
        (rho (nmat (-v)) (monomial m' 1)).coeff m := by
  rw [summandPoly_mul_nmat n h hg v hq]
  exact coeff_rho_expansion (summandPoly_isHomogeneous n h hg _ i j) _ m

end TernaryPeriodPolynomials.Argument.EisensteinClass
