/-
  Smoothness transport under the archimedean variable change
  `x ↦ (map r)⁻¹ x (map r)` that appears in `atInfinity_mul_rationalGroup`.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SmoothTransport

/-- Matrix conjugation `A ↦ C A C⁻¹` preserves the `C^∞`-on-invertible domain
property. -/
theorem contDiffOn_mul_conj {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : (Fin k → Matrix (Fin 3) (Fin 3) ℝ) → E)
    (hP : ContDiffOn ℝ ⊤ P {A | ∀ i, (A i).det ≠ 0})
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0) :
    ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => P (fun i => C * A i * C⁻¹))
      {A | ∀ i, (A i).det ≠ 0} := by
  have hCinv : C⁻¹.det ≠ 0 := by
    intro h
    have h1 : (C⁻¹ * C).det = 1 := by
      rw [Matrix.nonsing_inv_mul C (isUnit_iff_ne_zero.mpr hC), Matrix.det_one]
    rw [Matrix.det_mul, h, zero_mul] at h1
    exact one_ne_zero h1.symm
  let gLin : (Fin k → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ] (Fin k → Matrix (Fin 3) (Fin 3) ℝ) :=
    { toFun := fun A => fun i => C * A i * C⁻¹
      map_add' := by intro a b; funext i; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro a b; funext i; simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let gCLM := gLin.toContinuousLinearMap
  have hg : ContDiffOn ℝ ⊤ (fun A => gCLM A) {A | ∀ i, (A i).det ≠ 0} :=
    gCLM.contDiff.contDiffOn
  have hmap : Set.MapsTo (fun A => gCLM A) {A | ∀ i, (A i).det ≠ 0}
      {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA
    simp only [Set.mem_ofPred_eq] at hA ⊢
    intro i
    show (C * A i * C⁻¹).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hC (hA i)) hCinv
  have h := hP.comp hg hmap
  refine h.congr (fun A _ => ?_)
  rfl

/-- `(invertibleMatrix A).val = A` when `A` is invertible. -/
theorem invertibleMatrix_val {A : Matrix (Fin 3) (Fin 3) ℝ} (h : A.det ≠ 0) :
    (invertibleMatrix A).val = A := by
  unfold invertibleMatrix
  rw [dite_eq_left h]
  rfl

/-- **Smoothness under the archimedean conjugation substitution.**  If `F` is a
smooth function of `RealGL3`-valued arguments, then so is
`x ↦ F (fun i => (map r)⁻¹ x i (map r))`.  This is the variable change produced
by `atInfinity_mul_rationalGroup`. -/
theorem Smooth.comp_conj {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin k → RealGL3) → E) (hF : Smooth F)
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0) :
    Smooth (fun x : Fin k → RealGL3 => F (fun i => invertibleMatrix (C * (x i).val * C⁻¹))) := by
  rw [Smooth] at hF ⊢
  refine (contDiffOn_mul_conj
    (fun B : Fin k → Matrix (Fin 3) (Fin 3) ℝ => F (fun i => invertibleMatrix (B i)))
    hF C hC).congr (fun A hA => ?_)
  congr 1
  funext i
  simp only [invertibleMatrix_val (hA i)]

end TernaryPeriodPolynomials.HeckeTranslate.SmoothTransport

end
