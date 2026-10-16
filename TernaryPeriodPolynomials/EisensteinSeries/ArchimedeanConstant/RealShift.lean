module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.IsInducedShift
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.RepresentativeInvariance

@[expose] public section


/-!
# Induced sections are stable under real right translation

`IsInduced D side s` is preserved by `f ↦ f(· · h)` for every real `h ∈ GL₃(ℝ)`. This is the
closure property needed for the `K`-finite route: right `O(3)`-translates of an induced section
are induced sections.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein
open GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.ArchimedeanConstant

open TernaryPeriodPolynomials.HeckeTranslate

/-- Right multiplication by an invertible matrix preserves `C^∞` on the invertible domain. -/
theorem contDiffOn_mul_right {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : (Fin k → Matrix (Fin 3) (Fin 3) ℝ) → E)
    (hP : ContDiffOn ℝ ⊤ P {A | ∀ i, (A i).det ≠ 0})
    (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.det ≠ 0) :
    ContDiffOn ℝ ⊤ (fun A : Fin k → Matrix (Fin 3) (Fin 3) ℝ => P (fun i => A i * C))
      {A | ∀ i, (A i).det ≠ 0} := by
  let gLin : (Fin k → Matrix (Fin 3) (Fin 3) ℝ) →ₗ[ℝ] (Fin k → Matrix (Fin 3) (Fin 3) ℝ) :=
    { toFun := fun A => fun i => A i * C
      map_add' := by intro a b; funext i; simp [Matrix.add_mul]
      map_smul' := by intro a b; funext i; simp only [Pi.smul_apply, Matrix.smul_mul, RingHom.id_apply] }
  let gCLM := gLin.toContinuousLinearMap
  have hg : ContDiffOn ℝ ⊤ (fun A => gCLM A) {A | ∀ i, (A i).det ≠ 0} :=
    gCLM.contDiff.contDiffOn
  have hmap : Set.MapsTo (fun A => gCLM A) {A | ∀ i, (A i).det ≠ 0}
      {A | ∀ i, (A i).det ≠ 0} := by
    intro A hA
    simp only [Set.mem_ofPred_eq] at hA ⊢
    intro i
    show (A i * C).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hA i) hC
  exact (hP.comp hg hmap).congr (fun A _ => rfl)

theorem smooth_comp_mul_right {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin k → RealGL3) → E) (hF : Smooth F) (h : RealGL3) :
    Smooth (fun x : Fin k → RealGL3 => F (fun i => x i * h)) := by
  rw [Smooth] at hF ⊢
  refine (contDiffOn_mul_right
    (fun B : Fin k → Matrix (Fin 3) (Fin 3) ℝ => F (fun i => invertibleMatrix (B i)))
    hF h.val (GeneralLinearGroup.det_ne_zero h)).congr (fun A hA => ?_)
  congr 1
  funext i
  apply Units.ext
  have hAh : (A i * h.val).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero (hA i) (GeneralLinearGroup.det_ne_zero h)
  rw [Units.val_mul, SmoothTransport.invertibleMatrix_val (hA i),
    SmoothTransport.invertibleMatrix_val hAh]

variable {n : ℕ} {D : InducingData n} {side : Side} {s : ℂ}

/-- **Induced sections are stable under real right translation.** -/
theorem isInduced_right_real (h : RealGL3) {f : AdelicGL → ℂ} (hf : IsInduced D side s f) :
    IsInduced D side s (fun z => f (z * atInfinity h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G
    have hcomp := smooth_comp_mul_right
      (fun x' : Fin 1 → RealGL3 => f (G * atInfinity (x' 0))) (hf.1 G) h
    refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
    show f (G * atInfinity (x₁ 0) * atInfinity h) = f (G * atInfinity (x₁ 0 * h))
    rw [mul_assoc, HeckeInvariance.atInfinity_mul]
  · intro k G
    show f (G * atFinite k.val * atInfinity h) = f (G * atInfinity h)
    rw [mul_assoc, ← RepresentativeInvariance.atInfinity_atFinite_comm, ← mul_assoc]
    exact hf.2.1 k (G * atInfinity h)
  · intro a
    obtain ⟨v₀, hv₁, hv₂⟩ := hf.2.2.1 a
    refine ⟨fun x₁ : Fin 1 → RealGL3 => v₀ (fun _ : Fin 1 => x₁ 0 * h), ?_, ?_⟩
    · have hcomp := smooth_comp_mul_right (fun x' : Fin 1 → RealGL3 => (v₀ x').val) hv₁ h
      refine SmoothClosure.smooth_congr hcomp (fun x₁ => ?_)
      show (v₀ (fun _ : Fin 1 => x₁ 0 * h)).val = (v₀ (fun i => x₁ i * h)).val
      congr 2
      funext i
      fin_cases i
      rfl
    · intro x₁ A
      show D.cusp.realize (v₀ (fun _ : Fin 1 => x₁ 0 * h)) A =
          normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n side s) *
            f (binaryLevi side A * (a * atInfinity (x₁ 0)) * atInfinity h)
      rw [hv₂ (fun _ : Fin 1 => x₁ 0 * h) A]
      show _ * f (binaryLevi side A * (a * atInfinity (x₁ 0 * h))) = _
      rw [mul_assoc (binaryLevi side A), mul_assoc a, HeckeInvariance.atInfinity_mul]
  · cases side with
    | plane =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (planeUnipotent a b * G * atInfinity h) = f (G * atInfinity h)
        rw [mul_assoc]; exact hf.2.2.2.1 a b (G * atInfinity h)
      · intro t G
        show f (planeLevi 1 t * G * atInfinity h) =
          D.chi.toMonoidHom t * normPower t (-2 * inductionExponent .plane s) *
            f (G * atInfinity h)
        rw [mul_assoc]; exact hf.2.2.2.2.1 t (G * atInfinity h)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2.2 (G * atInfinity h)
    | line =>
      refine ⟨?_, ?_, ?_⟩
      · intro a b G
        show f (lineUnipotent a b * G * atInfinity h) = f (G * atInfinity h)
        rw [mul_assoc]; exact hf.2.2.2.1 a b (G * atInfinity h)
      · intro t G
        show f (lineLevi t 1 * G * atInfinity h) =
          D.chi.toMonoidHom t * normPower t (2 * inductionExponent .line s) *
            f (G * atInfinity h)
        rw [mul_assoc]; exact hf.2.2.2.2.1 t (G * atInfinity h)
      · intro G
        simpa only [mul_assoc] using hf.2.2.2.2.2 (G * atInfinity h)

end TernaryPeriodPolynomials.ArchimedeanConstant
