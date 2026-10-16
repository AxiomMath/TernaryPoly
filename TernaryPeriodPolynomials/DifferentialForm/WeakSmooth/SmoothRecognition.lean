module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.SmoothGradientClosed
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularRigidity
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.BoxConvex

@[expose] public section


/-! Genuine smooth recognition of scalar currents having smooth gradients on actual boxes. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure ContinuousAlternatingMap SmoothLocalDeRham
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

/-- On an actual convex domain with proved weak zero-gradient rigidity, a scalar current whose
gradient is a genuine smooth covector field is represented by a genuine smooth scalar function. -/
theorem scalarCurrent_smooth_of_smooth_gradient (Ω : TopologicalSpace.Opens E)
    (hΩ : Convex ℝ (Ω : Set E)) (hn : (Ω : Set E).Nonempty)
    (I : ScalarWeak Ω) (hI : ScalarWeakZeroRigid Ω I) (T : ScalarWeak Ω)
    (a : E → E →L[ℝ] ℝ) (ha : ContDiffOn ℝ ∞ a Ω)
    (hT : ∀ v, scalarWeakDerivative Ω v T =
      scalarRegularCurrent μ Ω (fun x => a x v) (ha.continuousOn.clm_apply continuousOn_const)) :
    ∃ (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f Ω), T = scalarRegularCurrent μ Ω f hf.continuousOn := by
  obtain ⟨x₀, hx₀⟩ := hn
  let w : RawForm E ℝ 1 := fun x => oneEquiv (a x)
  have hw : ContDiffOn ℝ ∞ w Ω :=
    (oneEquiv (E := E) (F := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn ha
  have hclosed : ∀ x ∈ Ω, extDeriv w x = 0 := smoothGradientCurrent_closed μ Ω T a ha hT
  let g := segmentPrimitive x₀ w
  have hg : ContDiffOn ℝ ∞ g Ω := segmentPrimitive_smooth Ω.isOpen hΩ hw hclosed hx₀
  have hdg (x : E) (hx : x ∈ Ω) : fderiv ℝ g x = a x := by
    rw [(segmentPrimitive_hasFDerivAt Ω.isOpen hΩ hw hclosed hx₀ hx).fderiv]
    exact oneEquiv.symm_apply_apply (a x)
  have hres : HasZeroWeakDerivative Ω (T - scalarRegularCurrent μ Ω g hg.continuousOn) := by
    intro v
    rw [map_sub, hT v, scalarRegularCurrent_derivative μ Ω g hg v]
    apply sub_eq_zero.mpr
    apply scalarRegularCurrent_congr μ Ω
    intro x hx
    exact congrArg (fun L : E →L[ℝ] ℝ => L v) (hdg x hx).symm
  obtain ⟨c, hc⟩ := scalarWeakZeroRigid_regular μ Ω I hI ⟨x₀, hx₀⟩
    (T - scalarRegularCurrent μ Ω g hg.continuousOn) hres
  refine ⟨fun x => g x + c, hg.add contDiffOn_const, ?_⟩
  have he := scalarRegularCurrent_add μ Ω g (fun _ => c) hg.continuousOn continuousOn_const
  change scalarRegularCurrent μ Ω (fun x => g x + c) _ = _ at he
  rw [he, scalarRegularCurrent_const μ Ω c]
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

/-- Actual affine coordinate boxes satisfy smooth-gradient recognition unconditionally for their
actual compact-test currents and genuine coordinate Haar measure. -/
theorem coordinateTestBox_smooth_of_smooth_gradient
    (ν : Measure SymmetricSpaceCharts.Coordinates) [IsAddHaarMeasure ν]
    (e : WeakCubeFive ≃L[ℝ] SymmetricSpaceCharts.Coordinates) (b : SymmetricSpaceCharts.Coordinates)
    (T : ScalarWeak (coordinateTestBox e b))
    (a : SymmetricSpaceCharts.Coordinates → SymmetricSpaceCharts.Coordinates →L[ℝ] ℝ)
    (ha : ContDiffOn ℝ ∞ a (coordinateTestBox e b))
    (hT : ∀ v, scalarWeakDerivative (coordinateTestBox e b) v T =
      scalarRegularCurrent ν (coordinateTestBox e b) (fun x => a x v)
        (ha.continuousOn.clm_apply continuousOn_const)) :
    ∃ (f : SymmetricSpaceCharts.Coordinates → ℝ)
      (hf : ContDiffOn ℝ ∞ f (coordinateTestBox e b)),
      T = scalarRegularCurrent ν (coordinateTestBox e b) f hf.continuousOn :=
  scalarCurrent_smooth_of_smooth_gradient ν (coordinateTestBox e b)
    (coordinateTestBox_convex e b) (coordinateTestBox_nonempty e b)
    (coordinateTestBoxMass e b) (coordinateTestBoxMass_rigid e b) T a ha hT

end TernaryPoly.PolynomialFormWeakSmooth
