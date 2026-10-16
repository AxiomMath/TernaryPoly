module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspDecompK

@[expose] public section


/-!
# Every cusp: the section at the rational points and the cover

Formalized by Claude Sonnet 5.5.

`adelicSection_gFin_rational_K`: for `A ∈ SL₃(ℤ)` with `A k⁻¹ ∈ Γ(N)` and `A₂₀ ≠ 0`, the adelic section at `(w₀⁻¹u(w), w₀⁻¹u(r_A) ι(k⁻¹))` is
the classical section at `A · qMat(shiftV r_A w)`; `exists_elt_of_decompK`: every decomposable `w₀⁻¹u(r) ι(k⁻¹)` is of this form.
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.IntegralReduction
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N]

/-- **The adelic section at the rational point `w₀⁻¹u(r_A) · ι(k⁻¹)` is the classical section at `A · qMat v`.** -/
theorem adelicSection_gFin_rational_K (hN : 3 ≤ N) (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ))
    (k A : SL(3, ℤ)) (hA : A * k⁻¹ ∈ gammaN N) (h0 : (A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0) (w : Fin 2 → ℝ)
    {y : Fin 5 → ℝ} (hy : y ∈ Omega) (i j : Fin 5) :
    adelicSection N n (hfun f) (gReal w)
        (gFin (algebraMap ℚ FiniteAdeles (slRowPt A).1, algebraMap ℚ FiniteAdeles (slRowPt A).2) * kInvFin k) y i j =
      summandPoly n (hfun f) (realMat A * qMat (shiftV (slRowPt A) w)) y i j := by
  rw [adelicSection_of_decomp N hN n f (gReal_det w) (decompK_gFin N k A hA h0) hy i j]
  have e : ratReal (piOf (slRowPt A) A)⁻¹ * gReal w = realMat A * qMat (shiftV (slRowPt A) w) := by
    have h1 : (piOf (slRowPt A) A)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℚ A *
        (weyl⁻¹ * upperUnipotent (slRowPt A).1 (slRowPt A).2 : GL3 ℚ)⁻¹ := by
      unfold piOf
      rw [_root_.mul_inv_rev, map_inv, inv_inv]
    rw [h1, ratReal_mul, ratReal_mapGL, Matrix.mul_assoc, gReal_eq_mul_qMat (slRowPt A) w,
      ← Matrix.mul_assoc (ratReal _), ratReal_inv_mul, Matrix.one_mul]
  exact congrArg (fun G => summandPoly n (hfun f) G y i j) e

/-- **The cover for the cusp `k`**: if `w₀⁻¹u(r) ι(k⁻¹) ∈ P(ℚ) K(N)` then `r` is the point of the bottom row of some `A = w k`,
`w ∈ Γ(N)`, with `A₂₀ ≠ 0`. -/
theorem exists_elt_of_decompK (k : SL(3, ℤ)) (r : ℚ × ℚ)
    (h : ∃ π κ, IsDecomp N (gFin (algebraMap ℚ FiniteAdeles r.1, algebraMap ℚ FiniteAdeles r.2) * kInvFin k) π κ) :
    ∃ A : SL(3, ℤ), A * k⁻¹ ∈ gammaN N ∧ (A : Matrix (Fin 3) (Fin 3) ℤ) 2 0 ≠ 0 ∧ slRowPt A = r := by
  obtain ⟨π, κ, hd⟩ := h
  set X : GL3 ℚ := weyl⁻¹ * upperUnipotent r.1 r.2 with hX
  set ρ : GL3 ℚ := π⁻¹ * X * Matrix.SpecialLinearGroup.mapGL ℚ k⁻¹ with hρ
  have h1 : rationalFinite ρ = GeneralLinearGroup.map integralEmbedding κ := by
    have e : rationalFinite X * rationalFinite (Matrix.SpecialLinearGroup.mapGL ℚ k⁻¹) =
        rationalFinite π * GeneralLinearGroup.map integralEmbedding κ := by
      have := hd.eq
      rwa [gFin_rational r] at this
    rw [hρ, map_mul, map_mul, map_inv, mul_assoc, e, inv_mul_cancel_left]
  have hdet : ρ.val.det = 1 := by
    rw [hρ, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hd.ppos.inv.det, hX, weylInvU_val,
      Matrix.det_fin_three, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe]
    simp
  obtain ⟨w, hwN, hw⟩ := gammaN_of_rat_levelKernel N ρ hdet κ hd.ker h1
  have hρw : ρ = Matrix.SpecialLinearGroup.mapGL ℚ w := by
    apply Units.ext
    ext i j
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    exact (hw i j).symm
  have hXA : X = π * Matrix.SpecialLinearGroup.mapGL ℚ (w * k) := by
    have : X = π * ρ * Matrix.SpecialLinearGroup.mapGL ℚ k := by
      rw [hρ, map_inv]
      group
    rw [this, hρw, map_mul, mul_assoc]
  have row : ∀ j, X.val 2 j = π.val 2 2 * (((w * k : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℚ) := by
    intro j
    rw [hXA, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, hd.ppos.mem.1, hd.ppos.mem.2,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
    simp
  have e0 : X.val 2 0 = 1 := by rw [hX, weylInvU_val]; simp
  have e1 : X.val 2 1 = r.1 := by rw [hX, weylInvU_val]; simp
  have e2 : X.val 2 2 = r.2 := by rw [hX, weylInvU_val]; simp
  have hw0 : (((w * k : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) ≠ 0 := by
    intro h0
    have := row 0
    rw [e0, h0, mul_zero] at this
    exact one_ne_zero this
  refine ⟨w * k, by simpa using hwN, by exact_mod_cast hw0, ?_⟩
  have p22 : π.val 2 2 = ((((w * k : SL(3, ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ))⁻¹ := by
    have := row 0
    rw [e0] at this
    field_simp
    linarith
  unfold slRowPt rowPt
  ext
  · simp only
    rw [← e1, row 1, p22]; field_simp
  · simp only
    rw [← e2, row 2, p22]; field_simp

end TernaryPeriodPolynomials.Argument.FormClassK
