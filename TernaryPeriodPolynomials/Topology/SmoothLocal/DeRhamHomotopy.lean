module

public import TernaryPeriodPolynomials.Topology.SmoothLocal.DeRhamRadialDerivative

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothLocalDeRham
open Set Filter MeasureTheory ContinuousAlternatingMap
open scoped ContDiff Topology

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

theorem radialIntegrand_intervalIntegrable {s : Set E} (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    IntervalIntegrable (fun t => radialIntegrand a w (x, t)) volume 0 1 := by
  exact ((radialIntegrand_smooth a hw).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hx).intervalIntegrable_of_Icc zero_le_one

theorem radial_parameterDerivative_intervalIntegrable {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    IntervalIntegrable (fun t => parameterDerivative (radialIntegrand a w) (x, t)) volume 0 1 := by
  exact ((parameterDerivative_smooth (radialDomain_isOpen hs a) (radialIntegrand_smooth a hw)).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hx).intervalIntegrable_of_Icc zero_le_one

theorem radial_parameterDerivative_eq {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E} {t : ℝ}
    (hp : radialPoint a (x, t) ∈ s) :
    parameterDerivative (radialIntegrand a w) (x, t) =
      fderiv ℝ (fun y => radialIntegrand a w (y, t)) x :=
  (parameterDerivative_hasFDerivAt (radialDomain_isOpen hs a) (radialIntegrand_smooth a hw) hp).fderiv.symm

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- The actual exterior differential commutes with this smooth compact parameter integral. -/
theorem extDeriv_radialHomotopy {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    extDeriv (radialHomotopy a w) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun y => radialIntegrand a w (y, t)) x := by
  unfold extDeriv
  rw [(radialHomotopy_hasFDerivAt hs a hw hx).fderiv]
  unfold alternatizeUncurryFin
  rw [← (alternatizeUncurryFinCLM ℝ E F (n := n)).intervalIntegral_comp_comm
    (radial_parameterDerivative_intervalIntegrable hs a hw hx)]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [radial_parameterDerivative_eq hs a hw (hx t (by simpa using ht))]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem extDeriv_radialIntegrand_intervalIntegrable {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    IntervalIntegrable (fun t => extDeriv (fun y => radialIntegrand a w (y, t)) x) volume 0 1 := by
  have hc : ContinuousOn (fun t => alternatizeUncurryFinCLM ℝ E F (n := n)
      (parameterDerivative (radialIntegrand a w) (x, t))) (Icc (0 : ℝ) 1) := by
    apply (alternatizeUncurryFinCLM ℝ E F (n := n)).continuous.comp_continuousOn
    exact (parameterDerivative_smooth (radialDomain_isOpen hs a) (radialIntegrand_smooth a hw)).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hx
  apply (hc.intervalIntegrable_of_Icc zero_le_one).congr
  intro t ht
  dsimp only
  unfold extDeriv
  rw [radial_parameterDerivative_eq hs a hw (hx t (by simpa using uIoc_subset_uIcc ht))]
  rfl

/-- The all-degree radial chain homotopy identity, with actual smooth forms and actual integrals. -/
theorem radial_homotopy_identity {s : Set E} (hs : IsOpen s) (a : E)
    {w : RawForm E F (n + 1)} (hw : ContDiffOn ℝ ∞ w s) {x : E}
    (hx : x ∈ sliceDomain (radialDomain a s)) :
    extDeriv (radialHomotopy a w) x + radialHomotopy a (extDeriv w) x = w x := by
  rw [extDeriv_radialHomotopy hs a hw hx]
  unfold radialHomotopy
  rw [← intervalIntegral.integral_add (extDeriv_radialIntegrand_intervalIntegrable hs a hw hx)
    (radialIntegrand_intervalIntegrable a (smooth_extDeriv hs hw) hx)]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t ^ (n + 1) • w (radialPoint a (x, t)))
    (f' := fun t => extDeriv (fun y => radialIntegrand a w (y, t)) x +
      radialIntegrand a (extDeriv w) (x, t))
    (a := (0 : ℝ)) (b := 1) (fun t ht => ?_)
    ((extDeriv_radialIntegrand_intervalIntegrable hs a hw hx).add
      (radialIntegrand_intervalIntegrable a (smooth_extDeriv hs hw) hx))
  · simpa [radialPoint] using hftc
  · have hp := hx t (by simpa using ht)
    have hdiff := ((hw _ hp).contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
    rw [radialIntegrand_cartan a x t hdiff]
    exact radialWeighted_hasDerivAt a x t hdiff

end TernaryPoly.SmoothLocalDeRham
