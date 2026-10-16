module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularDerivative
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularSeparation
public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamOnePrimitive

@[expose] public section


/-! A genuine smooth one-form which is a scalar-current gradient is genuinely closed. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation in a fixed direction commutes with the genuine derivative of a smooth covector field. -/
theorem regularCovector_fderiv_apply (Ω : TopologicalSpace.Opens E) (a : E → E →L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a Ω) {x : E} (hx : x ∈ Ω) (u v : E) :
    fderiv ℝ (fun y => a y v) x u = fderiv ℝ a x u v := by
  have hd := (ha.differentiableOn (by simp) x hx).differentiableAt (Ω.isOpen.mem_nhds hx)
  have hh := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  exact congrArg (fun L : E →L[ℝ] ℝ => L u) hh |>.trans (by simp)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

/-- Equality of the actual mixed weak derivatives forces symmetry of the genuine derivative
of a smooth covector field representing a scalar-current gradient. -/
theorem smoothGradientCurrent_symmetric (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω)
    (a : E → E →L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω)
    (hT : ∀ v, scalarWeakDerivative Ω v T =
      scalarRegularCurrent μ Ω (fun x => a x v) (ha.continuousOn.clm_apply continuousOn_const))
    {x : E} (hx : x ∈ Ω) (u v : E) :
    fderiv ℝ a x u v = fderiv ℝ a x v u := by
  have hh := scalarWeakDerivative_commute Ω T u v
  rw [hT v, hT u, scalarRegularCurrent_derivative μ Ω (fun x => a x v)
    (ha.clm_apply contDiffOn_const) u,
    scalarRegularCurrent_derivative μ Ω (fun x => a x u) (ha.clm_apply contDiffOn_const) v] at hh
  have he := (scalarRegularCurrent_eq_iff μ Ω _ _ _ _).mp hh hx
  simpa only [regularCovector_fderiv_apply Ω a ha hx] using he

/-- The smooth alternating one-form underlying an actual scalar-current gradient is closed. -/
theorem smoothGradientCurrent_closed (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω)
    (a : E → E →L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω)
    (hT : ∀ v, scalarWeakDerivative Ω v T =
      scalarRegularCurrent μ Ω (fun x => a x v) (ha.continuousOn.clm_apply continuousOn_const)) :
    ∀ x ∈ Ω, extDeriv (fun y => SmoothLocalDeRham.oneEquiv (a y)) x = 0 := by
  intro x hx
  apply (SmoothLocalDeRham.extDeriv_oneEquiv_eq_zero_iff a x).mpr
  exact smoothGradientCurrent_symmetric μ Ω T a ha hT hx

end TernaryPoly.PolynomialFormWeakSmooth
