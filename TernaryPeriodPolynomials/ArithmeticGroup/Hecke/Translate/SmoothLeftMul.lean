/-
  Smoothness of the uniform left-multiplication variable change
  `x ↦ fun i => Cgl * x i`.  This is one half of the non-uniform variable change
  appearing in the multi-variable `HasSmoothCuspLift` transport.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.MatrixConjLemmas

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SmoothLeftMul

theorem invertibleMatrix_val_of_gl (g : RealGL3) :
    invertibleMatrix (g : Matrix (Fin 3) (Fin 3) ℝ) = g := by
  apply Units.ext
  rw [SmoothTransport.invertibleMatrix_val (A := (g : Matrix (Fin 3) (Fin 3) ℝ))
    (GeneralLinearGroup.det_ne_zero g)]

theorem smooth_left_mul {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin k → RealGL3) → E) (hg : Smooth g) (Cgl : RealGL3) :
    Smooth (fun x : Fin k → RealGL3 => g (fun i => Cgl * x i)) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      g (fun i => Cgl * invertibleMatrix (A i))) {A | ∀ i, (A i).det ≠ 0}
  have hg' : ContDiffOn ℝ ⊤ (fun A' : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      g (fun i => invertibleMatrix (A' i))) {A' | ∀ i, (A' i).det ≠ 0} := hg
  let L : (Fin k → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ] (Fin k → Matrix (Fin 3) (Fin 3) ℝ) :=
    { toFun := fun A i => (Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A i
      map_add' := by
        intro A B
        funext i
        simp only [Pi.add_apply, mul_add]
      map_smul' := by
        intro r A
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul] }
  have hmap : Set.MapsTo (fun A => L A) {A | ∀ i, (A i).det ≠ 0} {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA i
    show ((Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A i).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero Cgl) (hA i)
  have hL : ContDiffOn ℝ ⊤ (fun A => L A) {A | ∀ i, (A i).det ≠ 0} :=
    L.toContinuousLinearMap.contDiff.contDiffOn
  have hcomp := hg'.comp hL hmap
  refine hcomp.congr (fun A hA => ?_)
  congr 1
  funext i
  show Cgl * invertibleMatrix (A i) = invertibleMatrix ((Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A i)
  rw [MatrixConjLemmas.invertibleMatrix_mul (GeneralLinearGroup.det_ne_zero Cgl) (hA i),
    invertibleMatrix_val_of_gl Cgl]

end TernaryPeriodPolynomials.HeckeTranslate.SmoothLeftMul

end
