module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth

@[expose] public section


/-!
# Small `Smooth` closure lemmas

Left multiplication by a fixed real matrix, multiplication by a constant, and composition with a
continuous linear map preserve `Smooth` (real analyticity on the invertible matrices); unitary
operators of a cuspidal representation as real continuous linear maps.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Smoothness helpers -/

section SmoothHelpers

/-- Left multiplication by a fixed real matrix preserves `Smooth` in one variable. -/
theorem smooth_comp_mul_left {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin 1 → RealGL3) → E) (hF : Smooth F) (h : RealGL3) :
    Smooth (fun x : Fin 1 → RealGL3 => F (fun _ => h * x 0)) := by
  rw [Smooth] at hF ⊢
  let gLin : (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ] (Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) :=
    { toFun := fun A i => h.val * A i
      map_add' := by intro a b; funext i; simp [Matrix.mul_add]
      map_smul' := by intro c a; funext i; simp }
  let gCLM := LinearMap.toContinuousLinearMap gLin
  have hg : ContDiffOn ℝ ⊤ (fun A => gCLM A) {A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0} :=
    gCLM.contDiff.contDiffOn
  have hmap : Set.MapsTo (fun A => gCLM A) {A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0}
      {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA i
    show (h.val * A i).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero h) (hA i)
  refine (hF.comp hg hmap).congr (fun A hA => ?_)
  show F (fun _ => h * invertibleMatrix (A 0)) = F (fun i => invertibleMatrix (h.val * A i))
  congr 1
  funext i
  fin_cases i
  apply Units.ext
  have hA0 : (A 0).det ≠ 0 := hA 0
  have hhA : (h.val * A 0).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero h) hA0
  rw [Units.val_mul, TernaryPeriodPolynomials.SphericalDetection.Helpers.invertibleMatrix_val _ hA0]
  exact (TernaryPeriodPolynomials.SphericalDetection.Helpers.invertibleMatrix_val _ hhA).symm

theorem smooth_const_mul {k : ℕ} {F : (Fin k → RealGL3) → ℂ} (hF : Smooth F) (c : ℂ) :
    Smooth (fun x => c * F x) := by
  rw [Smooth] at hF ⊢
  exact hF.const_smul c

theorem smooth_clm_comp {k : ℕ} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (T : E →L[ℝ] E') {F : (Fin k → RealGL3) → E}
    (hF : Smooth F) : Smooth (fun x => T (F x)) := by
  rw [Smooth] at hF ⊢
  exact T.contDiff.comp_contDiffOn hF

/-- A unitary operator of the cuspidal representation, as a real continuous linear map. -/
def piCLM (σ : CuspidalRepresentation) (g : BinaryAdelicGL) : σ.H →L[ℝ] σ.H :=
  ((σ.π g).mkContinuous 1 (fun v => by rw [σ.unitary, one_mul])).restrictScalars ℝ

theorem piCLM_apply (σ : CuspidalRepresentation) (g : BinaryAdelicGL) (v : σ.H) :
    piCLM σ g v = σ.π g v := rfl

end SmoothHelpers

end TernaryPeriodPolynomials.SourceConstruction
