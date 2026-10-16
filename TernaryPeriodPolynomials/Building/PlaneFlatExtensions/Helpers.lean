module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix
open scoped Matrix.Norms.Elementwise


noncomputable section

namespace TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers

theorem normPower_zero (t : Adelesˣ) : normPower t 0 = 1 := by
  simp [normPower]

theorem normPower_add (t : Adelesˣ) (z w : ℂ) :
    normPower t (z + w) = normPower t z * normPower t w := by
  simp only [normPower, add_mul, Complex.exp_add]

theorem normPower_neg (t : Adelesˣ) (z : ℂ) :
    normPower t (-z) * normPower t z = 1 := by
  rw [← normPower_add, neg_add_cancel, normPower_zero]

theorem normPower_ne_zero (t : Adelesˣ) (z : ℂ) : normPower t z ≠ 0 :=
  Complex.exp_ne_zero _

def flatFactor (height : AdelicGL → ℝ) (s : ℂ) (g : AdelicGL) : ℂ :=
  Complex.exp ((inductionExponent .plane s -
    inductionExponent .plane cohomologicalPoint) * (height g : ℂ))

def flatTwist (height : AdelicGL → ℝ) (f : AdelicGL → ℂ)
    (s : ℂ) (g : AdelicGL) : ℂ := flatFactor height s g * f g

theorem flatTwist_at_point (height : AdelicGL → ℝ) (f : AdelicGL → ℂ) :
    flatTwist height f cohomologicalPoint = f := by
  funext g
  simp [flatTwist, flatFactor]

theorem flatTwist_analytic (height : AdelicGL → ℝ) (f : AdelicGL → ℂ)
    (g : AdelicGL) (s : ℂ) : AnalyticAt ℂ (fun z => flatTwist height f z g) s := by
  unfold flatTwist flatFactor inductionExponent
  fun_prop

structure PlaneHeight where
  height : AdelicGL → ℝ
  smooth : ∀ g, Smooth (fun x : Fin 1 → RealGL3 => height (g * atInfinity (x 0)))
  level : ∀ k : finiteLevel, ∀ g, height (g * atFinite k.val) = height g
  unipotent : ∀ a b g, height (planeUnipotent a b * g) = height g
  scalar : ∀ t g, height (planeLevi 1 t * g) =
    -2 * Real.log (adeleNorm t : ℝ) + height g
  binary : ∀ A g, height (planeLevi A 1 * g) =
    Real.log (adeleNorm (GeneralLinearGroup.det A) : ℝ) + height g
  compact : ∀ k, inMaximalCompact k → height k = 0

theorem PlaneHeight.factor_smooth (h : PlaneHeight) (s : ℂ) (g : AdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 => flatFactor h.height s (g * atInfinity (x 0))) := by
  have hs := h.smooth g
  unfold Smooth at hs ⊢
  unfold flatFactor
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.contDiffOn.comp hs
    (fun _ _ => Set.mem_univ _))).cexp

theorem PlaneHeight.factor_binary (h : PlaneHeight) (s : ℂ)
    (A : BinaryAdelicGL) (g : AdelicGL) :
    flatFactor h.height s (planeLevi A 1 * g) =
      normPower (GeneralLinearGroup.det A)
        (inductionExponent .plane s - inductionExponent .plane cohomologicalPoint) *
      flatFactor h.height s g := by
  simp only [flatFactor, h.binary, Complex.ofReal_add, mul_add, Complex.exp_add,
    normPower]

theorem PlaneHeight.factor_scalar (h : PlaneHeight) (s : ℂ)
    (t : Adelesˣ) (g : AdelicGL) :
    flatFactor h.height s (planeLevi 1 t * g) =
      normPower t (-2 * (inductionExponent .plane s -
        inductionExponent .plane cohomologicalPoint)) * flatFactor h.height s g := by
  simp only [flatFactor, h.scalar, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_ofNat, mul_add, Complex.exp_add, normPower]
  congr 2
  ring

theorem PlaneHeight.normalized_binary_twist (h : PlaneHeight) {n : ℕ}
    (f : AdelicGL → ℂ) (s : ℂ) (A : BinaryAdelicGL) (g : AdelicGL) :
    normPower (GeneralLinearGroup.det A) (-binaryInductionExponent n .plane s) *
      flatTwist h.height f s (planeLevi A 1 * g) =
    flatFactor h.height s g *
      (normPower (GeneralLinearGroup.det A)
        (-binaryInductionExponent n .plane cohomologicalPoint) *
        f (planeLevi A 1 * g)) := by
  rw [flatTwist, h.factor_binary]
  have he : -binaryInductionExponent n .plane s +
      (inductionExponent .plane s - inductionExponent .plane cohomologicalPoint) =
      -binaryInductionExponent n .plane cohomologicalPoint := by
    unfold binaryInductionExponent
    ring
  rw [← mul_assoc, ← mul_assoc, ← normPower_add, he]
  ring

theorem PlaneHeight.twist_smooth_cusp_lift (h : PlaneHeight) {n : ℕ}
    (D : InducingData n) (f : AdelicGL → ℂ)
    (hf : HasSmoothCuspLift D .plane cohomologicalPoint
      (fun (_ : Fin 0 → RealGL3) => f)) (s : ℂ) :
    HasSmoothCuspLift D .plane s (fun (_ : Fin 0 → RealGL3) =>
      flatTwist h.height f s) := by
  intro a
  obtain ⟨v, hv, he⟩ := hf a
  let w : (Fin 1 → RealGL3) → D.cusp.smooth :=
    fun x => flatFactor h.height s (a * atInfinity (x 0)) • v x
  refine ⟨w, ?_, ?_⟩
  · have hs := h.factor_smooth s a
    unfold Smooth at hs hv ⊢
    exact hs.smul hv
  · intro x A
    change D.cusp.realize
      (flatFactor h.height s (a * atInfinity (x 0)) • v x) A = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, he]
    exact (h.normalized_binary_twist f s A (a * atInfinity (x 0))).symm

theorem PlaneHeight.twist_induced (h : PlaneHeight) {n : ℕ}
    (D : InducingData n) (f : AdelicGL → ℂ)
    (hf : IsInduced D .plane cohomologicalPoint f) (s : ℂ) :
    IsInduced D .plane s (flatTwist h.height f s) := by
  obtain ⟨hsmooth, hlevel, hlift, hunipotent, hscalar, hbinary⟩ := hf
  refine ⟨?_, ?_, h.twist_smooth_cusp_lift D f hlift s, ?_, ?_, ?_⟩
  · intro g
    have hs := h.factor_smooth s g
    have hf := hsmooth g
    unfold Smooth at hs hf ⊢
    exact hs.mul hf
  · intro k g
    simp only [flatTwist, flatFactor, h.level k g, hlevel k g]
  · intro a b g
    simp only [flatTwist, flatFactor, h.unipotent a b g, hunipotent a b g]
  · intro t g
    rw [flatTwist, h.factor_scalar, hscalar]
    have he : -2 * (inductionExponent .plane s -
        inductionExponent .plane cohomologicalPoint) +
        -2 * inductionExponent .plane cohomologicalPoint =
        -2 * inductionExponent .plane s := by ring
    change _ = _ * _ * (flatFactor h.height s g * f g)
    calc
      _ = D.chi.toMonoidHom t *
          (normPower t (-2 * (inductionExponent .plane s -
            inductionExponent .plane cohomologicalPoint)) *
          normPower t (-2 * inductionExponent .plane cohomologicalPoint)) *
          (flatFactor h.height s g * f g) := by ring
      _ = _ := by rw [← normPower_add, he]
  · intro g
    change (fun A => normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .plane s) *
      flatTwist h.height f s (planeLevi A 1 * g)) ∈ _
    have hb := (cuspFunctions D.cusp).smul_mem (flatFactor h.height s g) (hbinary g)
    rw [show (fun A => normPower (GeneralLinearGroup.det A)
      (-binaryInductionExponent n .plane s) *
      flatTwist h.height f s (planeLevi A 1 * g)) =
      flatFactor h.height s g • (fun A => normPower (GeneralLinearGroup.det A)
        (-binaryInductionExponent n .plane cohomologicalPoint) *
        f (planeLevi A 1 * g)) by
      funext A
      exact h.normalized_binary_twist f s A g]
    exact hb

theorem PlaneHeight.flat_extension (h : PlaneHeight) {n : ℕ}
    (D : InducingData n) (f : AdelicGL → ℂ)
    (hf : IsInduced D .plane cohomologicalPoint f) :
    ∃ F : ℂ → AdelicGL → ℂ, IsFlatSection D F ∧ F cohomologicalPoint = f := by
  refine ⟨flatTwist h.height f, ⟨h.twist_induced D f hf, flatTwist_analytic h.height f,
    ?_⟩, flatTwist_at_point h.height f⟩
  intro s A k hk
  rw [h.normalized_binary_twist]
  simp only [flatFactor, h.compact k hk, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, flatTwist_at_point]

end TernaryPeriodPolynomials.PlaneFlatExtensions.Helpers
