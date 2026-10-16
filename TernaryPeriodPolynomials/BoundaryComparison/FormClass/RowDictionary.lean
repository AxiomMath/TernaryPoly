module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.UnipotentCells
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.KBig

@[expose] public section


/-!
# (C), step 3a: rational points `w₀⁻¹ u(r)` and the cosets of `Γ(N)`

Formalized by Claude Sonnet 5.5.

For `a ∈ SL₃(ℤ)` with `a₂₀ ≠ 0` and `r = (a₂₁/a₂₀, a₂₂/a₂₀)`:
`w₀⁻¹ u(r) = π_a · a` with `π_a ∈ P(ℚ)` of determinant one (`piOf_mul`, `piOf_planeDet`), so for `a ∈ Γ(N)`
the finite adele `w₀⁻¹ u(r)` is decomposable (`decomp_gFin`) and the adelic section there is the classical section at
`a · u(w - r)` (`adelicSection_gFin_rational`).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem weylInvU_val {R : Type*} [CommRing R] (s t : R) :
    ((weyl⁻¹ * upperUnipotent s t : GL3 R) : Matrix (Fin 3) (Fin 3) R) = !![0, 1, 0; 0, 0, 1; 1, s, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The point `(ρ₁/ρ₀, ρ₂/ρ₀)` of a row. -/
def rowPt (ρ : Fin 3 → ℤ) : ℚ × ℚ := ((ρ 1 : ℚ) / ρ 0, (ρ 2 : ℚ) / ρ 0)

/-- The point of the bottom row of `a ∈ SL₃(ℤ)`. -/
def slRowPt (a : SL(3, ℤ)) : ℚ × ℚ := rowPt fun j => (a : Matrix (Fin 3) (Fin 3) ℤ) 2 j

/-- `π_a = w₀⁻¹ u(r) a⁻¹ ∈ GL₃(ℚ)`. -/
def piOf (r : ℚ × ℚ) (a : SL(3, ℤ)) : GL3 ℚ :=
  weyl⁻¹ * upperUnipotent r.1 r.2 * Matrix.SpecialLinearGroup.mapGL ℚ a⁻¹

theorem piOf_mul (r : ℚ × ℚ) (a : SL(3, ℤ)) :
    piOf r a * Matrix.SpecialLinearGroup.mapGL ℚ a = weyl⁻¹ * upperUnipotent r.1 r.2 := by
  unfold piOf
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem sl_row_inv (a : SL(3, ℤ)) (j : Fin 3) :
    ((a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) * (((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 j : ℚ) +
      ((a : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ) * (((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 j : ℚ) +
      ((a : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ) * (((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℚ) =
    if j = 2 then 1 else 0 := by
  have h := congrArg (fun m : SL(3, ℤ) => (m : Matrix (Fin 3) (Fin 3) ℤ) 2 j) (mul_inv_cancel a)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_apply,
    Fin.sum_univ_three, Matrix.one_apply] at h
  have h' : (((a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 * ((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 0 j +
      (a : Matrix (Fin 3) (Fin 3) ℤ) 2 1 * ((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 1 j +
      (a : Matrix (Fin 3) (Fin 3) ℤ) 2 2 * ((a⁻¹ : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℤ) : ℚ) =
      (((if (2 : Fin 3) = j then 1 else 0 : ℤ)) : ℚ) := by rw [h]
  push_cast at h'
  rw [h']
  by_cases hj : j = 2
  · subst hj; simp
  · have : (2 : Fin 3) ≠ j := fun e => hj e.symm
    simp [hj, this]

theorem piOf_row2 (a : SL(3, ℤ)) (h0 : (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) (j : Fin 3) :
    (piOf (slRowPt a) a : Matrix (Fin 3) (Fin 3) ℚ) 2 j =
      if j = 2 then (((a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ))⁻¹ else 0 := by
  have h0' : (((a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h0
  have key := sl_row_inv a j
  unfold piOf
  rw [Units.val_mul, weylInvU_val, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, slRowPt, rowPt, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const, RingHom.mapMatrix_apply, Matrix.map_apply,
    eq_intCast, Matrix.SpecialLinearGroup.map_apply_coe, algebraMap_int_eq]
  by_cases hj : j = 2
  · simp only [hj, ite_true] at key ⊢
    field_simp
    linear_combination key
  · simp only [hj, ite_false] at key ⊢
    field_simp
    linear_combination key

theorem piOf_mem (a : SL(3, ℤ)) (h0 : (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) :
    piOf (slRowPt a) a ∈ planeParabolic ℚ :=
  ⟨by rw [piOf_row2 a h0 0]; simp, by rw [piOf_row2 a h0 1]; simp⟩

theorem piOf_det (r : ℚ × ℚ) (a : SL(3, ℤ)) : (piOf r a : Matrix (Fin 3) (Fin 3) ℚ).det = 1 := by
  unfold piOf
  rw [Units.val_mul, Matrix.det_mul, weylInvU_val, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  rw [← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one, mul_one, Matrix.det_fin_three]
  simp

theorem piOf_planeDet (a : SL(3, ℤ)) (h0 : (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) :
    PlaneDet (piOf (slRowPt a) a) := ⟨piOf_mem a h0, piOf_det _ a⟩

variable (N : ℕ) [NeZero N]

theorem decomp_gFin {a : SL(3, ℤ)} (ha : a ∈ gammaN N) (h0 : (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) :
    IsDecomp N (gFin (algebraMap ℚ FiniteAdeles (slRowPt a).1, algebraMap ℚ FiniteAdeles (slRowPt a).2))
      (piOf (slRowPt a) a) (Matrix.SpecialLinearGroup.mapGL IntegralAdeles a) := by
  have := decomp_rational N (piOf_planeDet a h0) ha
  rw [piOf_mul] at this
  rwa [gFin_rational (slRowPt a)]

/-- The real shift `v` with `w₀⁻¹ u(w) = w₀⁻¹ u(r) · qMat v`. -/
def shiftV (r : ℚ × ℚ) (w : Fin 2 → ℝ) : Fin 2 → ℝ := ![(r.2 : ℝ) - w 1, (r.1 : ℝ) - w 0]

theorem ratReal_weylInvU (r : ℚ × ℚ) :
    ratReal (weyl⁻¹ * upperUnipotent r.1 r.2 : GL3 ℚ) = !![0, 1, 0; 0, 0, 1; 1, (r.1 : ℝ), (r.2 : ℝ)] := by
  ext i j
  rw [ratReal_apply]
  have this : ((weyl⁻¹ * upperUnipotent r.1 r.2 : GL3 ℚ) : Matrix (Fin 3) (Fin 3) ℚ) i j =
      (!![0, 1, 0; 0, 0, 1; 1, r.1, r.2] : Matrix (Fin 3) (Fin 3) ℚ) i j := by rw [weylInvU_val]
  rw [this]
  fin_cases i <;> fin_cases j <;> simp

theorem gReal_eq_mul_qMat (r : ℚ × ℚ) (w : Fin 2 → ℝ) :
    gReal w = ratReal (weyl⁻¹ * upperUnipotent r.1 r.2 : GL3 ℚ) * qMat (shiftV r w) := by
  rw [ratReal_weylInvU, gReal_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qMat, shiftV, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The adelic section at the rational point `w₀⁻¹ u(r_a)` of a coset is the classical section at
`a · qMat v`.** -/
theorem adelicSection_gFin_rational (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    {a : SL(3, ℤ)} (ha : a ∈ gammaN N) (h0 : (a : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) (w : Fin 2 → ℝ)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSection N n (hfun f) (gReal w)
        (gFin (algebraMap ℚ FiniteAdeles (slRowPt a).1, algebraMap ℚ FiniteAdeles (slRowPt a).2)) y i j =
      summandPoly n (hfun f) (realMat a * qMat (shiftV (slRowPt a) w)) y i j := by
  rw [adelicSection_of_decomp N hN n f (gReal_det w) (decomp_gFin N ha h0) hy i j]
  have e : ratReal (piOf (slRowPt a) a)⁻¹ * gReal w = realMat a * qMat (shiftV (slRowPt a) w) := by
    have h1 : (piOf (slRowPt a) a)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ a *
        (weyl⁻¹ * upperUnipotent (slRowPt a).1 (slRowPt a).2 : GL3 ℚ)⁻¹ := by
      unfold piOf
      rw [_root_.mul_inv_rev, map_inv, inv_inv]
    rw [h1, ratReal_mul, ratReal_mapGL, Matrix.mul_assoc, gReal_eq_mul_qMat (slRowPt a) w,
      ← Matrix.mul_assoc (ratReal _), ratReal_inv_mul, Matrix.one_mul]
  exact congrArg (fun G => summandPoly n (hfun f) G y i j) e

end TernaryPeriodPolynomials.Argument.FormClassK
