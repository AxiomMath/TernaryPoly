module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open Complex MeasureTheory Set Metric

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundedHolomorphicFamily

theorem complexWedgeIntegral_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (map : E →L[ℂ] F) (function : ℂ → E) (first second : ℂ)
    (hcontinuous : ContinuousOn function (first.Rectangle second)) :
    map (first.wedgeIntegral second function) =
      first.wedgeIntegral second (fun point => map (function point)) := by
  have hhorizontal : IntervalIntegrable (fun time : ℝ => function (time + first.im * I)) volume first.re second.re := by
    apply ContinuousOn.intervalIntegrable
    apply hcontinuous.comp (by fun_prop)
    intro time htime
    change (time + first.im * I).re ∈ uIcc first.re second.re ∧
      (time + first.im * I).im ∈ uIcc first.im second.im
    simpa using And.intro htime (left_mem_uIcc : first.im ∈ uIcc first.im second.im)
  have hvertical : IntervalIntegrable (fun time : ℝ => function (second.re + time * I)) volume first.im second.im := by
    apply ContinuousOn.intervalIntegrable
    apply hcontinuous.comp (by fun_prop)
    intro time htime
    change (second.re + time * I).re ∈ uIcc first.re second.re ∧
      (second.re + time * I).im ∈ uIcc first.im second.im
    simpa using And.intro (right_mem_uIcc : second.re ∈ uIcc first.re second.re) htime
  simp only [Complex.wedgeIntegral, map_add, map_smul,
    ← map.intervalIntegral_comp_comm hhorizontal, ← map.intervalIntegral_comp_comm hvertical]

theorem boundedHolomorphicFamily_differentiableOn_of_continuousOn
    {Space : Type*} [TopologicalSpace Space]
    (function : ℂ → BoundedContinuousFunction Space ℂ) (domain : Set ℂ) (hopen : IsOpen domain)
    (hcontinuous : ContinuousOn function domain)
    (hholomorphic : ∀ point, DifferentiableOn ℂ (fun parameter => function parameter point) domain) :
    DifferentiableOn ℂ function domain := by
  apply (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hopen).mp
  refine ⟨?_, hcontinuous⟩
  intro first second hrectangle
  ext point
  have hreverse : second.Rectangle first ⊆ domain := by
    simpa only [Complex.Rectangle, uIcc_comm] using hrectangle
  have hfirst := complexWedgeIntegral_clm (BoundedContinuousFunction.evalCLM ℂ point)
    function first second (hcontinuous.mono hrectangle)
  have hsecond := complexWedgeIntegral_clm (BoundedContinuousFunction.evalCLM ℂ point)
    function second first (hcontinuous.mono hreverse)
  change (first.wedgeIntegral second function) point = -(second.wedgeIntegral first function) point
  rw [show (first.wedgeIntegral second function) point =
    first.wedgeIntegral second (fun parameter => function parameter point) from hfirst,
    show (second.wedgeIntegral first function) point =
    second.wedgeIntegral first (fun parameter => function parameter point) from hsecond]
  exact (hholomorphic point).isConservativeOn first second hrectangle

theorem boundedHolomorphicFamily_lipschitzOn_ball
    {Space : Type*} [TopologicalSpace Space]
    (function : ℂ → BoundedContinuousFunction Space ℂ) (center : ℂ) (radius bound : ℝ)
    (hradius : 0 < radius)
    (hholomorphic : ∀ point, DifferentiableOn ℂ (fun parameter => function parameter point) (ball center (2 * radius)))
    (hbound : ∀ parameter ∈ ball center (2 * radius), ‖function parameter‖ ≤ bound) :
    LipschitzOnWith ⟨|bound| / radius, by positivity⟩ function (ball center radius) := by
  have hsmall : ball center radius ⊆ ball center (2 * radius) := ball_subset_ball (by linarith)
  have hdisc (parameter : ℂ) (hparameter : parameter ∈ ball center radius) :
      closedBall parameter radius ⊆ ball center (2 * radius) := by
    intro value hvalue
    apply lt_of_le_of_lt (dist_triangle value parameter center)
    have hnear : dist value parameter ≤ radius := hvalue
    have hcenter : dist parameter center < radius := hparameter
    linarith
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first hfirst second hsecond
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (div_nonneg (abs_nonneg bound) hradius.le) (norm_nonneg (first - second)))).mpr
  intro point
  have hderivative (parameter : ℂ) (hparameter : parameter ∈ ball center radius) :
      ‖deriv (fun value => function value point) parameter‖ ≤ |bound| / radius := by
    rw [← Complex.cderiv_eq_deriv isOpen_ball (hholomorphic point) hradius (hdisc parameter hparameter)]
    apply Complex.norm_cderiv_le hradius
    intro value hvalue
    exact ((function value).norm_coe_le_norm point).trans
      ((hbound value (hdisc parameter hparameter (sphere_subset_closedBall hvalue))).trans (le_abs_self bound))
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun parameter hparameter => (hholomorphic point parameter (hsmall hparameter)).differentiableAt
      (isOpen_ball.mem_nhds (hsmall hparameter))) hderivative (convex_ball center radius) hsecond hfirst

theorem boundedHolomorphicFamily_differentiableOn_of_localBound
    {Space : Type*} [TopologicalSpace Space]
    (function : ℂ → BoundedContinuousFunction Space ℂ) (domain : Set ℂ) (hopen : IsOpen domain)
    (hholomorphic : ∀ point, DifferentiableOn ℂ (fun parameter => function parameter point) domain)
    (hbound : ∀ center ∈ domain, ∃ radius : ℝ, 0 < radius ∧ ball center (2 * radius) ⊆ domain ∧
      ∃ bound : ℝ, ∀ parameter ∈ ball center (2 * radius), ‖function parameter‖ ≤ bound) :
    DifferentiableOn ℂ function domain := by
  apply boundedHolomorphicFamily_differentiableOn_of_continuousOn function domain hopen _ hholomorphic
  intro center hcenter
  obtain ⟨radius, hradius, hsub, bound, hbound⟩ := hbound center hcenter
  have hlip := boundedHolomorphicFamily_lipschitzOn_ball function center radius bound hradius
    (fun point => (hholomorphic point).mono hsub) hbound
  exact (hlip.continuousOn.continuousAt (ball_mem_nhds center hradius)).continuousWithinAt

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BoundedHolomorphicFamily
