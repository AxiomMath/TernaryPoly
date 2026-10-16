module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tensor.MetricData

@[expose] public section

/-! Genuine first derivatives of affine coefficient frames and their bilinear metrics. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open ContinuousLinearMap
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Affine endomorphisms provide exact first variations; invertibility is not required. -/
def affineOperator (A : V →L[ℝ] V) (t : ℝ) : V →L[ℝ] V := ContinuousLinearMap.id ℝ V + t • A

@[simp] theorem affineOperator_zero (A : V →L[ℝ] V) : affineOperator A 0 = ContinuousLinearMap.id ℝ V := by
  simp only [affineOperator, zero_smul, add_zero]

theorem contDiff_affineOperator (A : V →L[ℝ] V) : ContDiff ℝ ∞ (affineOperator A) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem hasDerivAt_affineOperator (A : V →L[ℝ] V) : HasDerivAt (affineOperator A) A 0 := by
  convert! (hasDerivAt_const (0 : ℝ) (ContinuousLinearMap.id ℝ V)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const A) using 1
  simp

theorem hasDerivAt_bilinear_eval {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {D : V →L[ℝ] V →L[ℝ] ℝ}
    (hB : HasDerivAt B D 0) (p q : V) : HasDerivAt (fun t => B t p q) (D p q) 0 := by
  have hp := hB.clm_apply (hasDerivAt_const (0 : ℝ) p)
  have hq := hp.clm_apply (hasDerivAt_const (0 : ℝ) q)
  simpa only [map_zero, add_zero] using hq

theorem hasDerivAt_bilinear_of_eval (B : ℝ → V →L[ℝ] V →L[ℝ] ℝ) (D : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : DifferentiableAt ℝ B 0) (h : ∀ p q : V, HasDerivAt (fun t => B t p q) (D p q) 0) :
    HasDerivAt B D 0 := by
  have hd := DifferentiableAt.hasDerivAt (f := B) (x := (0 : ℝ)) (by convert! hB using 1)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro q
  have hh := hasDerivAt_bilinear_eval hd p q
  exact ((h p q).unique hh)

theorem hasDerivAt_fixed_bilinear (B : V →L[ℝ] V →L[ℝ] ℝ) {w z : ℝ → V} {w' z' : V}
    (hw : HasDerivAt w w' 0) (hz : HasDerivAt z z' 0) :
    HasDerivAt (fun t => B (w t) (z t)) (B w' (z 0) + B (w 0) z') 0 := by
  have h := ContinuousLinearMap.hasDerivAt_of_bilinear (B := B) (fun _ => hw) (fun _ => hz)
  convert! h using 1
  exact add_comm _ _

theorem hasDerivAt_variable_bilinear {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} {B' : V →L[ℝ] V →L[ℝ] ℝ}
    {w z : ℝ → V} {w' z' : V} (hB : HasDerivAt B B' 0) (hw : HasDerivAt w w' 0) (hz : HasDerivAt z z' 0) :
    HasDerivAt (fun t => B t (w t) (z t))
      (B' (w 0) (z 0) + B 0 w' (z 0) + B 0 (w 0) z') 0 := by
  have hp := hB.clm_apply hw
  have hq := hp.clm_apply hz
  simpa only [_root_.add_apply] using hq

variable [FiniteDimensional ℝ V]

theorem contDiff_bilinear_affine (B : V →L[ℝ] V →L[ℝ] ℝ) (A : V →L[ℝ] V) :
    ContDiff ℝ ∞ (fun t => B.bilinearComp (affineOperator A t) (affineOperator A t)) := by
  apply contDiff_clm_apply_iff.mpr
  intro p
  apply contDiff_clm_apply_iff.mpr
  intro q
  exact (contDiff_const.clm_apply ((contDiff_affineOperator A).clm_apply contDiff_const)).clm_apply
    ((contDiff_affineOperator A).clm_apply contDiff_const)

theorem hasDerivAt_bilinear_affine (B : V →L[ℝ] V →L[ℝ] ℝ) (A : V →L[ℝ] V) :
    HasDerivAt (fun t => B.bilinearComp (affineOperator A t) (affineOperator A t))
      (B.bilinearComp A (ContinuousLinearMap.id ℝ V) + B.bilinearComp (ContinuousLinearMap.id ℝ V) A) 0 := by
  apply hasDerivAt_bilinear_of_eval
  · exact (contDiff_bilinear_affine B A).differentiable (by simp) |>.differentiableAt
  · intro p q
    have hp := (hasDerivAt_affineOperator A).clm_apply (hasDerivAt_const (0 : ℝ) p)
    have hq := (hasDerivAt_affineOperator A).clm_apply (hasDerivAt_const (0 : ℝ) q)
    have h := ((hasDerivAt_const (0 : ℝ) B).clm_apply hp).clm_apply hq
    simpa only [affineOperator_zero, map_zero, add_zero, zero_add, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.bilinearComp_apply, _root_.add_apply, _root_.zero_apply] using h

end TernaryPoly.PolynomialFormConnection
