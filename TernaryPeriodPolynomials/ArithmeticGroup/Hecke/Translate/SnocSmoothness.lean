/-
  Smoothness of the non-uniform variable change
  `x ↦ Fin.snoc (fun j => Cgl * x j.castSucc) (Cgl * x.last * Cgl⁻¹)`
  appearing in the multi-variable `HasSmoothCuspLift` transport.  The map is
  linear in the underlying matrices, so its smoothness is `ContDiffOn.comp` with
  a continuous linear map preserving the invertible locus.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothLeftMul
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.MatrixConjLemmas

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SnocSmoothness

theorem smooth_snoc_conj {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin (k + 1) → RealGL3) → E) (hg : Smooth g) (Cgl : RealGL3) :
    Smooth (fun x : Fin (k + 1) → RealGL3 =>
      g (Fin.snoc (fun j : Fin k => Cgl * x (Fin.castSucc j))
          (Cgl * x (Fin.last k) * Cgl⁻¹))) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ =>
      g (Fin.snoc (fun j : Fin k => Cgl * invertibleMatrix (A (Fin.castSucc j)))
        (Cgl * invertibleMatrix (A (Fin.last k)) * Cgl⁻¹))) {A | ∀ i, (A i).det ≠ 0}
  have hg' : ContDiffOn ℝ ⊤ (fun A' : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ =>
      g (fun i => invertibleMatrix (A' i))) {A' | ∀ i, (A' i).det ≠ 0} := hg
  let δ : Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ :=
    fun i => if i = Fin.last k then ((Cgl⁻¹ : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ) else 1
  have hδ : ∀ i, (δ i).det ≠ 0 := by
    intro i
    by_cases h : i = Fin.last k
    · simp only [δ, h, ite_eq_left]; exact GeneralLinearGroup.det_ne_zero (Cgl⁻¹)
    · simp only [δ, h]; simp
  let L : (Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ]
      (Fin (k + 1) → Matrix (Fin 3) (Fin 3) ℝ) :=
    { toFun := fun A i => (Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A i * δ i
      map_add' := by
        intro A B
        funext i
        simp only [Pi.add_apply, mul_add, add_mul]
      map_smul' := by
        intro r A
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  have hmap : Set.MapsTo (fun A => L A) {A | ∀ i, (A i).det ≠ 0} {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA i
    show ((Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A i * δ i).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (GeneralLinearGroup.det_ne_zero Cgl) (hA i)) (hδ i)
  have hL : ContDiffOn ℝ ⊤ (fun A => L A) {A | ∀ i, (A i).det ≠ 0} :=
    L.toContinuousLinearMap.contDiff.contDiffOn
  have hcomp := hg'.comp hL hmap
  refine hcomp.congr (fun A hA => ?_)
  congr 1
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]
    show Cgl * invertibleMatrix (A (Fin.last k)) * Cgl⁻¹ =
      invertibleMatrix ((Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A (Fin.last k) * δ (Fin.last k))
    simp only [δ, ite_eq_left rfl]
    rw [GeneralLinearGroup.coe_inv,
      MatrixConjLemmas.invertibleMatrix_mul_conj (C := (Cgl : Matrix (Fin 3) (Fin 3) ℝ))
        (A := A (Fin.last k)) (GeneralLinearGroup.det_ne_zero Cgl) (hA (Fin.last k)),
      SmoothLeftMul.invertibleMatrix_val_of_gl Cgl]
  · intro j
    simp only [Fin.snoc_castSucc]
    show Cgl * invertibleMatrix (A j.castSucc) =
      invertibleMatrix ((Cgl : Matrix (Fin 3) (Fin 3) ℝ) * A j.castSucc * δ j.castSucc)
    simp only [δ, ite_eq_right (Fin.castSucc_ne_last j), mul_one]
    rw [MatrixConjLemmas.invertibleMatrix_mul (C := (Cgl : Matrix (Fin 3) (Fin 3) ℝ))
        (A := A j.castSucc) (GeneralLinearGroup.det_ne_zero Cgl) (hA j.castSucc),
      SmoothLeftMul.invertibleMatrix_val_of_gl Cgl]

end TernaryPeriodPolynomials.HeckeTranslate.SnocSmoothness

end
