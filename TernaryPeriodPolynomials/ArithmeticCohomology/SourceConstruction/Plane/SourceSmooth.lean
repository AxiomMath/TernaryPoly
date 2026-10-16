module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RealIwasawa
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothClosure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth

@[expose] public section


/-!
# Smoothness bookkeeping for the plane source cocycle

A matrix-valued function `M` of `k` real group elements is `MatSmooth` when its matrix entries are
real analytic on the invertible locus. This is closed under products, constants, coordinates, the
Iwasawa factor `b`, and extraction of the upper left block, and it transports `Smooth` along `M`.
Ordinary closure lemmas (difference, product, scalar multiplication) for `Smooth` complete the
toolbox used to prove the `Smooth` clauses of the plane source cocycle.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.SphericalDetection.Helpers (invertibleMatrix_coe invertibleMatrix_val)

namespace TernaryPeriodPolynomials.SourceConstruction

/-- Smoothness (real analyticity on the invertible locus) of a matrix-valued function of `k` real
group elements. -/
def MatSmooth {k m : ℕ} (M : (Fin k → RealGL3) → GeneralLinearGroup (Fin m) ℝ) : Prop :=
  ContDiffOn ℝ ⊤
    (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => (M (fun i => invertibleMatrix (A i))).val)
    {A | ∀ i, (A i).det ≠ 0}

theorem matSmooth_coord {k : ℕ} (i : Fin k) : MatSmooth (fun x : Fin k → RealGL3 => x i) := by
  unfold MatSmooth
  refine ((contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) i).contDiffOn).congr (fun A hA => ?_)
  exact invertibleMatrix_val (A i) (hA i)

theorem matSmooth_const {k m : ℕ} (c : GeneralLinearGroup (Fin m) ℝ) :
    MatSmooth (fun _ : Fin k → RealGL3 => c) := by
  unfold MatSmooth
  exact contDiffOn_const

theorem matSmooth_mul {k m : ℕ} {M₁ M₂ : (Fin k → RealGL3) → GeneralLinearGroup (Fin m) ℝ}
    (h₁ : MatSmooth M₁) (h₂ : MatSmooth M₂) : MatSmooth (fun x => M₁ x * M₂ x) := by
  unfold MatSmooth at h₁ h₂ ⊢
  have e₁ : ∀ i j, ContDiffOn ℝ ⊤
      (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => (M₁ (fun l => invertibleMatrix (A l))).val i j)
      {A | ∀ i, (A i).det ≠ 0} :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp h₁ i) j
  have e₂ : ∀ i j, ContDiffOn ℝ ⊤
      (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => (M₂ (fun l => invertibleMatrix (A l))).val i j)
      {A | ∀ i, (A i).det ≠ 0} :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp h₂ i) j
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Units.val_mul, Matrix.mul_apply]
  exact ContDiffOn.sum fun r _ => (e₁ i r).mul (e₂ r j)

theorem matSmooth_block {k : ℕ} {P : (Fin k → RealGL3) → RealGL3}
    {N : (Fin k → RealGL3) → GeneralLinearGroup (Fin 2) ℝ} (hP : MatSmooth P)
    (hN : ∀ x i j, (N x).val i j = (P x).val i.castSucc j.castSucc) : MatSmooth N := by
  unfold MatSmooth at hP ⊢
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  have h := contDiffOn_pi.mp (contDiffOn_pi.mp hP i.castSucc) j.castSucc
  exact h.congr (fun A _ => hN _ i j)

theorem matSmooth_iwasawaB {k : ℕ} {M : (Fin k → RealGL3) → RealGL3} (hM : MatSmooth M) :
    MatSmooth (fun x => iwasawaB (M x)) := by
  unfold MatSmooth at hM ⊢
  have hmaps : Set.MapsTo
      (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => (M (fun i => invertibleMatrix (A i))).val)
      {A | ∀ i, (A i).det ≠ 0} {B : Matrix (Fin 3) (Fin 3) ℝ | B.det ≠ 0} :=
    fun A _ => det_ne_zero_realGL3 _
  have h := iwasawaB_contDiffOn.comp hM hmaps
  refine h.congr (fun A _ => ?_)
  simp only [Function.comp]
  rw [invertibleMatrix_coe]

/-- Transport of `Smooth` along a `MatSmooth` change of variables. -/
theorem smooth_comp_matSmooth {k m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : GeneralLinearGroup (Fin m) ℝ → E)
    (hf : Smooth (fun x : Fin 1 → GeneralLinearGroup (Fin m) ℝ => f (x 0)))
    {M : (Fin k → RealGL3) → GeneralLinearGroup (Fin m) ℝ} (hM : MatSmooth M) :
    Smooth (fun x : Fin k → RealGL3 => f (M x)) := by
  unfold Smooth at hf ⊢
  unfold MatSmooth at hM
  have hmaps : Set.MapsTo
      (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
        fun _ : Fin 1 => (M (fun i => invertibleMatrix (A i))).val)
      {A | ∀ i, (A i).det ≠ 0} {B : Fin 1 → Matrix (Fin m) (Fin m) ℝ | ∀ i, (B i).det ≠ 0} :=
    fun A _ _ => GeneralLinearGroup.det_ne_zero _
  have hcomp := hf.comp (contDiffOn_pi.mpr fun _ => hM) hmaps
  refine hcomp.congr (fun A _ => ?_)
  simp only [Function.comp]
  rw [invertibleMatrix_coe]

section Closure

variable {k : ℕ}

theorem smooth_sub' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : (Fin k → RealGL3) → E} (hf : Smooth f) (hg : Smooth g) :
    Smooth (fun x => f x - g x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f (fun i => invertibleMatrix (A i)) - g (fun i => invertibleMatrix (A i)))
    {A | ∀ i, (A i).det ≠ 0}
  exact hf.sub hg

theorem smooth_mul_complex {f g : (Fin k → RealGL3) → ℂ} (hf : Smooth f) (hg : Smooth g) :
    Smooth (fun x => f x * g x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f (fun i => invertibleMatrix (A i)) * g (fun i => invertibleMatrix (A i)))
    {A | ∀ i, (A i).det ≠ 0}
  exact hf.mul hg

theorem smooth_const_complex (c : ℂ) : Smooth (fun _ : Fin k → RealGL3 => c) := by
  show ContDiffOn ℝ ⊤ (fun _ : Fin k → Matrix (Fin 3) (Fin 3) ℝ => c) {A | ∀ i, (A i).det ≠ 0}
  exact contDiffOn_const

theorem smooth_smul_vec {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] {f : (Fin k → RealGL3) → ℂ} {g : (Fin k → RealGL3) → E}
    (hf : Smooth f) (hg : Smooth g) : Smooth (fun x => f x • g x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f (fun i => invertibleMatrix (A i)) • g (fun i => invertibleMatrix (A i)))
    {A | ∀ i, (A i).det ≠ 0}
  exact hf.smul hg

end Closure

end TernaryPeriodPolynomials.SourceConstruction
