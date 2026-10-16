module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamRadial
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter MeasureTheory ContinuousAlternatingMap
open scoped ContDiff Topology

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- The radial segment has the literal affine derivative in its spatial variable. -/
theorem radialPoint_hasFDerivAt (a x : E) (t : ℝ) :
    HasFDerivAt (fun y => radialPoint a (y, t)) (t • ContinuousLinearMap.id ℝ E) x := by
  exact (((hasFDerivAt_id x).sub_const a).const_smul t).const_add a

/-- The full spatial derivative of the weighted radial integrand. -/
theorem radialIntegrand_hasFDerivAt (a x : E) (t : ℝ) {w : RawForm E F (n + 1)}
    (hw : DifferentiableAt ℝ w (radialPoint a (x, t))) :
    HasFDerivAt (fun y => radialIntegrand a w (y, t))
      (t ^ n • ((w (radialPoint a (x, t))).curryLeft +
        t • (insertCLM (x - a)).comp (fderiv ℝ w (radialPoint a (x, t))))) x := by
  have hcomp : HasFDerivAt (fun y => w (radialPoint a (y, t)))
      ((fderiv ℝ w (radialPoint a (x, t))).comp (t • ContinuousLinearMap.id ℝ E)) x := by
    exact hw.hasFDerivAt.comp x (radialPoint_hasFDerivAt a x t)
  have hi := (radialInsert_hasFDerivAt hcomp.differentiableAt a).const_smul (t ^ n)
  rw [hcomp.fderiv] at hi
  convert hi using 1 <;> ext v <;> simp [radialIntegrand, ContinuousLinearMap.comp_apply]

/-- Antisymmetrization of the integrand derivative, with the extra radial differential term. -/
theorem radialIntegrand_cartan (a x : E) (t : ℝ) {w : RawForm E F (n + 1)}
    (hw : DifferentiableAt ℝ w (radialPoint a (x, t))) :
    extDeriv (fun y => radialIntegrand a w (y, t)) x +
        radialIntegrand a (extDeriv w) (x, t) =
      t ^ n • ((n + 1) • w (radialPoint a (x, t))) +
        t ^ (n + 1) • (fderiv ℝ w (radialPoint a (x, t)) (x - a)) := by
  unfold extDeriv
  rw [(radialIntegrand_hasFDerivAt a x t hw).fderiv,
    alternatizeUncurryFin_smul, alternatizeUncurryFin_add,
    alternatizeUncurryFin_curryLeft, alternatizeUncurryFin_smul]
  have hid := alternatize_insert (fderiv ℝ w (radialPoint a (x, t))) (x - a)
  simp only [radialIntegrand, smul_add, ← mul_smul, ← pow_succ]
  rw [add_assoc, ← smul_add, hid]

/-- The temporal derivative used by the fundamental theorem of calculus. -/
theorem radialWeighted_hasDerivAt (a x : E) (t : ℝ) {w : RawForm E F (n + 1)}
    (hw : DifferentiableAt ℝ w (radialPoint a (x, t))) :
    HasDerivAt (fun r : ℝ => r ^ (n + 1) • w (radialPoint a (x, r)))
      (t ^ n • ((n + 1) • w (radialPoint a (x, t))) +
        t ^ (n + 1) • (fderiv ℝ w (radialPoint a (x, t)) (x - a))) t := by
  have hr : HasDerivAt (fun r : ℝ => radialPoint a (x, r)) (x - a) t := by
    simpa [radialPoint] using ((hasDerivAt_id t).smul_const (x - a)).const_add a
  have ht : HasDerivAt (fun r : ℝ => r ^ (n + 1)) ((n + 1 : ℕ) * t ^ n) t := by
    simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) t
  have heq : t ^ n • ((n + 1) • w (radialPoint a (x, t))) =
      (((n + 1 : ℕ) : ℝ) * t ^ n) • w (radialPoint a (x, t)) := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul, smul_comm]
  apply (ht.smul (hw.hasFDerivAt.comp_hasDerivAt t hr)).congr_deriv
  simp only [Function.comp_apply]
  rw [heq]
  exact add_comm _ _

end TernaryPoly.SmoothLocalDeRham
