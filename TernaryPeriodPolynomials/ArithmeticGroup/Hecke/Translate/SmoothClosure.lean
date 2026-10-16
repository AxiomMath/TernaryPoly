/-
  Closure of `GeneralEisenstein.Adelic.Smooth` for a general normed codomain,
  used to package linear combinations of smooth cusp-vector families in the
  `HasSmoothCuspLift` transport of the Hecke translate.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.SmoothTransport

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure

variable {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_add {f g : (Fin k → RealGL3) → E} (hf : Smooth f) (hg : Smooth g) :
    Smooth (fun x => f x + g x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f (fun i => invertibleMatrix (A i)) + g (fun i => invertibleMatrix (A i)))
    {A | ∀ i, (A i).det ≠ 0}
  exact hf.add hg

theorem smooth_const_smul (c : ℝ) {f : (Fin k → RealGL3) → E} (hf : Smooth f) :
    Smooth (fun x => c • f x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      c • f (fun i => invertibleMatrix (A i))) {A | ∀ i, (A i).det ≠ 0}
  exact hf.const_smul c

theorem smooth_finset_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin k → RealGL3) → E)
    (h : ∀ i ∈ s, Smooth (f i)) : Smooth (fun x => ∑ i ∈ s, f i x) := by
  show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      ∑ i ∈ s, f i (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
  exact ContDiffOn.sum (fun i hi => by
    have := h i hi
    show ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f i (fun j => invertibleMatrix (A j))) {A | ∀ i, (A i).det ≠ 0}
    exact this)


theorem smooth_zero : Smooth (fun _ : Fin k → RealGL3 => (0 : E)) := by
  show ContDiffOn ℝ ⊤ (fun _ : Fin k → Matrix (Fin 3) (Fin 3) ℝ => (0 : E))
    {A | ∀ i, (A i).det ≠ 0}
  exact contDiffOn_const

theorem smooth_congr {f g : (Fin k → RealGL3) → E} (hf : Smooth f) (h : ∀ x, g x = f x) :
    Smooth g := by
  have hf' : ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ =>
      f (fun i => invertibleMatrix (A i))) {A | ∀ i, (A i).det ≠ 0} := hf
  exact hf'.congr (fun A _ => h _)

end TernaryPeriodPolynomials.HeckeTranslate.SmoothClosure

end
