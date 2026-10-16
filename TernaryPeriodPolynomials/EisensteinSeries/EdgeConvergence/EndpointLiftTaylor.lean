module

public import Mathlib
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.TaylorIntegral
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# Real-analytic dependence of a circle average on a parameter

Interface for the smoothness of the endpoint lift. If a family `family s` of functions of a real
parameter `x` has, for every `s` on a circle, a power series `series s` at `center` on a common
ball, whose coefficients are continuous in `s` and bounded geometrically uniformly in `s`
(`‖series s n‖ ≤ constant * radius⁻¹ ^ n`), then the circle average of the family is a function of
`x` with the circle averaged power series on the same ball
(`TaylorIntegral.hasFPowerSeriesOnBall` for the circle measure).

The endpoint lift is `circleAverage (fun s => lam s • R s)`
(`EndpointLift.endpointLift_eq_circleAverage`), so the lift of a real analytic family of vectors
`orbit s` is covered by taking `family s x = lam s • orbit s x` and `series s = lam s • series' s`.
-/

open Metric MeasureTheory
open scoped NNReal

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace EndpointLift

open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The circle average of a family of real analytic functions with uniformly geometric Taylor
coefficients is real analytic on the common ball, with the circle averaged coefficients. -/
theorem circleAverage_hasFPowerSeriesOnBall {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {c : ℂ} {r : ℝ} (hr : 0 < r)
    (family : ℂ → X → F) (series : ℂ → FormalMultilinearSeries ℝ X F) (center : X)
    (radius : ℝ≥0) (positive : 0 < radius) (constant : ℝ)
    (expansion : ∀ s ∈ sphere c r, HasFPowerSeriesOnBall (family s) (series s) center radius)
    (continuous : ∀ n, ContinuousOn (fun s => series s n) (sphere c r))
    (bounded : ∀ s ∈ sphere c r, ∀ n, ‖series s n‖ ≤ constant * (radius : ℝ)⁻¹ ^ n) :
    HasFPowerSeriesOnBall (fun x => Real.circleAverage (fun s => family s x) c r)
      (fun n => Real.circleAverage (fun s => series s n) c r) center radius := by
  have hmem : ∀ θ : ℝ, circleMap c r θ ∈ sphere c r := fun θ => circleMap_mem_sphere c hr.le θ
  have hcont : ∀ n, Continuous (fun θ : ℝ => series (circleMap c r θ) n) := fun n =>
    (continuous n).comp_continuous (continuous_circleMap c r) hmem
  have hint : ∀ n, Integrable (fun θ : ℝ => series (circleMap c r θ) n)
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := fun n => (hcont n).integrableOn_Ioc
  have hbound : ∀ n, (∫ θ, ‖series (circleMap c r θ) n‖
      ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) ≤
        (constant * (2 * Real.pi)) * (radius : ℝ)⁻¹ ^ n := by
    intro n
    calc (∫ θ, ‖series (circleMap c r θ) n‖ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
        ≤ ∫ θ, constant * (radius : ℝ)⁻¹ ^ n ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
          integral_mono (hint n).norm (integrable_const _)
            (fun θ => bounded _ (hmem θ) n)
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi, constant * (radius : ℝ)⁻¹ ^ n :=
          (intervalIntegral.integral_of_le (by positivity)).symm
      _ = (2 * Real.pi - 0) • (constant * (radius : ℝ)⁻¹ ^ n) := intervalIntegral.integral_const _
      _ = (constant * (2 * Real.pi)) * (radius : ℝ)⁻¹ ^ n := by
          rw [smul_eq_mul]
          ring
  have hT := TaylorIntegral.hasFPowerSeriesOnBall
    (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
    (fun θ : ℝ => family (circleMap c r θ)) (fun θ : ℝ => series (circleMap c r θ))
    center radius positive (constant * (2 * Real.pi))
    (fun θ => expansion _ (hmem θ)) hint hbound
  have e1 : (fun x => Real.circleAverage (fun s => family s x) c r) =
      ((2 * Real.pi)⁻¹ : ℝ) • (fun x => ∫ θ, family (circleMap c r θ) x
        ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
    funext x
    simp only [Real.circleAverage_def, Pi.smul_apply]
    rw [intervalIntegral.integral_of_le (by positivity)]
  have e2 : ((fun n => Real.circleAverage (fun s => series s n) c r) :
        FormalMultilinearSeries ℝ X F) =
      ((2 * Real.pi)⁻¹ : ℝ) • ((fun n => ∫ θ, series (circleMap c r θ) n
        ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) : FormalMultilinearSeries ℝ X F) := by
    refine funext fun n => ?_
    show Real.circleAverage (fun s => series s n) c r =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ θ, series (circleMap c r θ) n
        ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)]
  rw [e1, e2]
  exact hT.const_smul

end EndpointLift

end TernaryPeriodPolynomials.EdgeConvergence
