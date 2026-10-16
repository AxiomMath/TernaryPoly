module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.Laws
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.LiftSmooth

@[expose] public section


/-!
# The smooth lift of the plane integral cochain

`omega_lift_family`: along any real-analytic family of frames `Wf = z x` and vertex triples `X x`, the coefficient `m` of
the plane integral cochain `cOmegaAt D F (X x) (a · z_∞(x)) A` is the realization at `A` of an explicit smooth vector
`piSmooth(b_F(a), OmegaVec ...)` that depends real-analytically on the family (`Smooth`, i.e. `ContDiffOn ℝ ω`), where
`F` is the weighted scalar realization of a smooth finite-level vector.  `omega_scalar_smooth_family` is the scalar
analyticity.

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise
open MeasureTheory MvPolynomial GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section Lift

variable {n : ℕ} (D : InducingData n) (stages : AnalyticScalar.ContinuousStages D.cusp) (hw : ℤ)
  (v : D.cusp.smooth) (fixed : v.val ∈ BinaryLevel.fixedSubspace D.cusp BinaryLevel.finiteCongruence)

include stages fixed

/-- **The smooth lift of the plane integral cochain along a real-analytic family of frames and vertices.** -/
theorem omega_lift_family
    (hol : ∀ h, DifferentiableOn ℂ (cuspScalarWeightedRealization D.cusp hw v h) {z : ℂ | 0 < z.im})
    (m : Fin 3 →₀ ℕ) (a : AdelicGL) {K : ℕ} (X : (Fin K → RealGL3) → Fin 3 → RealGL3)
    (z : (Fin K → RealGL3) → RealGL3) (fz f0 f1 f2 : (Fin K → Mat3) → Mat3)
    (cz : ContDiff ℝ ⊤ fz) (c0 : ContDiff ℝ ⊤ f0) (c1 : ContDiff ℝ ⊤ f1) (c2 : ContDiff ℝ ⊤ f2)
    (hz : ∀ x, (z x).val = fz (fun i => (x i).val))
    (h0 : ∀ x, gramOf (X x 0) = f0 (fun i => (x i).val))
    (h1 : ∀ x, gramOf (X x 1) = f1 (fun i => (x i).val))
    (h2 : ∀ x, gramOf (X x 2) = f2 (fun i => (x i).val)) :
    ∃ w : (Fin K → RealGL3) → D.cusp.smooth, Smooth (fun x => (w x).val) ∧
      ∀ x A, D.cusp.realize (w x) A =
        (cOmegaAt D (cuspScalarWeightedRealization D.cusp hw v) (X x) (a * atInfinity (z x)) A).val.coeff m := by
  classical
  by_cases hm : m.degree = n
  · have hRa : ∀ x, ((realGroup a).val * (z x).val).det ≠ 0 := fun x => by
      rw [Matrix.det_mul]
      exact mul_ne_zero (det_ne_zero_realGL3 _) (det_ne_zero_realGL3 _)
    let vec : (Fin K → RealGL3) → D.cusp.smooth := fun x =>
      piSmooth D.cusp (bF a) (OmegaVec D.cusp stages hw v fixed n m (cF D a)
        ((realGroup a).val * (z x).val) (gramOf (X x 0)) (gramOf (X x 1)) (gramOf (X x 2)) (hRa x)
        (posDef_gramOf _) (posDef_gramOf _) (posDef_gramOf _))
    have hvals : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) →
        (fun i => (invertibleMatrix (A i)).val) = A := fun A hA =>
      funext fun i => invertibleMatrix_val (A i) (hA i)
    refine ⟨vec, ?_, ?_⟩
    · unfold Smooth
      have hcd := contDiffOn_OmegaExpl D.cusp hw v n m (cF D a) (bF a) (K := K)
        (fun A => (realGroup a).val * fz A) f0 f1 f2 (contDiff_matMul contDiff_const cz) c0 c1 c2
        (fun A hA => by
          have e := hz (fun i => invertibleMatrix (A i))
          rw [hvals A hA] at e
          rw [Matrix.det_mul, ← e]
          exact mul_ne_zero (det_ne_zero_realGL3 _) (det_ne_zero_realGL3 _))
        (fun A hA => by
          have e := h0 (fun i => invertibleMatrix (A i))
          rw [hvals A hA] at e
          rw [← e]
          exact posDef_gramOf _)
        (fun A hA => by
          have e := h1 (fun i => invertibleMatrix (A i))
          rw [hvals A hA] at e
          rw [← e]
          exact posDef_gramOf _)
        (fun A hA => by
          have e := h2 (fun i => invertibleMatrix (A i))
          rw [hvals A hA] at e
          rw [← e]
          exact posDef_gramOf _)
      refine hcd.congr (fun A hA => ?_)
      have ez := hz (fun i => invertibleMatrix (A i))
      have e0 := h0 (fun i => invertibleMatrix (A i))
      have e1 := h1 (fun i => invertibleMatrix (A i))
      have e2 := h2 (fun i => invertibleMatrix (A i))
      rw [hvals A hA] at ez e0 e1 e2
      show (piSmooth D.cusp (bF a) (OmegaVec D.cusp stages hw v fixed n m (cF D a) _ _ _ _ _ _ _ _)).val = _
      show D.cusp.π (bF a) (OmegaVec D.cusp stages hw v fixed n m (cF D a) _ _ _ _ _ _ _ _).val = _
      rw [OmegaVec_val]
      unfold OmegaExpl
      rw [ez, e0, e1, e2]
    · intro x A
      have hcoef : (cOmegaAt D (cuspScalarWeightedRealization D.cusp hw v) (X x) (a * atInfinity (z x)) A).val.coeff m =
          cOmegaCoeffAt n D (cuspScalarWeightedRealization D.cusp hw v) (X x) (a * atInfinity (z x)) A m := by
        unfold cOmegaAt
        rw [coeff_ofCoeffs, ite_eq_left hm]
      rw [hcoef, cOmegaCoeffAt_eq_scal D _ hol, cF_mul_atInfinity, bF_mul_atInfinity, realGroup_mul_atInfinity,
        Units.val_mul]
      have h1 : D.cusp.realize (vec x) A = D.cusp.realize
          (OmegaVec D.cusp stages hw v fixed n m (cF D a) ((realGroup a).val * (z x).val)
            (gramOf (X x 0)) (gramOf (X x 1)) (gramOf (X x 2)) (hRa x)
            (posDef_gramOf _) (posDef_gramOf _) (posDef_gramOf _)) (A * bF a) :=
        realize_piSmooth D.cusp (bF a) _ A
      rw [h1]
      exact (OmegaScal_eq_realize D.cusp stages hw v fixed n m (cF D a) (A * bF a) _ _ _ _ (hRa x)
        (posDef_gramOf _) (posDef_gramOf _) (posDef_gramOf _)).symm
  · refine ⟨fun _ => 0, ?_, fun x A => ?_⟩
    · unfold Smooth
      exact contDiffOn_const
    · have hcoef : (cOmegaAt D (cuspScalarWeightedRealization D.cusp hw v) (X x) (a * atInfinity (z x)) A).val.coeff m = 0 := by
        unfold cOmegaAt
        rw [coeff_ofCoeffs, ite_eq_right hm]
      rw [hcoef]
      simp


omit stages fixed in
/-- **Real analyticity of the plane integral cochain in the family of frames and vertices.** -/
theorem omega_scalar_smooth_family (F : BinaryAdelicGL → ℂ → ℂ)
    (hol : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (m : Fin 3 →₀ ℕ) (a : AdelicGL) (A : BinaryAdelicGL) {K : ℕ} (X : (Fin K → RealGL3) → Fin 3 → RealGL3)
    (z : (Fin K → RealGL3) → RealGL3) (fz f0 f1 f2 : (Fin K → Mat3) → Mat3)
    (cz : ContDiff ℝ ⊤ fz) (c0 : ContDiff ℝ ⊤ f0) (c1 : ContDiff ℝ ⊤ f1) (c2 : ContDiff ℝ ⊤ f2)
    (hz : ∀ x, (z x).val = fz (fun i => (x i).val))
    (h0 : ∀ x, gramOf (X x 0) = f0 (fun i => (x i).val))
    (h1 : ∀ x, gramOf (X x 1) = f1 (fun i => (x i).val))
    (h2 : ∀ x, gramOf (X x 2) = f2 (fun i => (x i).val)) :
    Smooth (fun x : Fin K → RealGL3 => (cOmegaAt D F (X x) (a * atInfinity (z x)) A).val.coeff m) := by
  classical
  by_cases hm : m.degree = n
  · have hvals : ∀ A : Fin K → Mat3, (∀ i, (A i).det ≠ 0) →
        (fun i => (invertibleMatrix (A i)).val) = A := fun A hA =>
      funext fun i => invertibleMatrix_val (A i) (hA i)
    have hF : ∀ h z, 0 < z.im → AnalyticAt ℝ (F h) z := fun h z hz =>
      ((hol h).analyticAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)).restrictScalars
    unfold Smooth
    have hcd := contDiffOn_OmegaScal F hF n m (cF D a) (A * bF a) (K := K)
      (fun A => (realGroup a).val * fz A) f0 f1 f2 (contDiff_matMul contDiff_const cz) c0 c1 c2
      (fun A hA => by
        have e := hz (fun i => invertibleMatrix (A i))
        rw [hvals A hA] at e
        rw [Matrix.det_mul, ← e]
        exact mul_ne_zero (det_ne_zero_realGL3 _) (det_ne_zero_realGL3 _))
      (fun A hA => by
        have e := h0 (fun i => invertibleMatrix (A i))
        rw [hvals A hA] at e
        rw [← e]
        exact posDef_gramOf _)
      (fun A hA => by
        have e := h1 (fun i => invertibleMatrix (A i))
        rw [hvals A hA] at e
        rw [← e]
        exact posDef_gramOf _)
      (fun A hA => by
        have e := h2 (fun i => invertibleMatrix (A i))
        rw [hvals A hA] at e
        rw [← e]
        exact posDef_gramOf _)
    refine hcd.congr (fun A' hA' => ?_)
    have ez := hz (fun i => invertibleMatrix (A' i))
    have e0 := h0 (fun i => invertibleMatrix (A' i))
    have e1 := h1 (fun i => invertibleMatrix (A' i))
    have e2 := h2 (fun i => invertibleMatrix (A' i))
    rw [hvals A' hA'] at ez e0 e1 e2
    show (cOmegaAt D F (X (fun i => invertibleMatrix (A' i))) (a * atInfinity (z (fun i => invertibleMatrix (A' i)))) A).val.coeff m = _
    unfold cOmegaAt
    rw [coeff_ofCoeffs, ite_eq_left hm, cOmegaCoeffAt_eq_scal D F hol, cF_mul_atInfinity, bF_mul_atInfinity,
      realGroup_mul_atInfinity, Units.val_mul, ez, e0, e1, e2]
  · have : (fun x : Fin K → RealGL3 => (cOmegaAt D F (X x) (a * atInfinity (z x)) A).val.coeff m) = fun _ => 0 := by
      funext x
      unfold cOmegaAt
      rw [coeff_ofCoeffs, ite_eq_right hm]
    rw [this]
    unfold Smooth
    exact contDiffOn_const

end Lift

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
