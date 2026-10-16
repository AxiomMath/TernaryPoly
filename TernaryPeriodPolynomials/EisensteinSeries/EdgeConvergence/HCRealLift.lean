module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealCircle

@[expose] public section


/-!
# Input 3b: the Cauchy lift realizes the circle average of the local scalars

Original work by Claude Sonnet 5.5.

`localLiftRealization` proves `EdgeInputs.LocalLiftRealization` (input 3b) without any further
input: for every family of smooth vectors equal to the Cauchy circle average of the local standard
integrals, the realization at a binary adele is the circle average of the local scalars
`EdgeInputs.localScalar`. It is a consequence of `HCReal.circle_lift_realizes` (itself a
consequence of the local realization theorem `localValue_realizes` and of
`HCReal.realize_integral_of_fixed`), applied in the generality of an arbitrary indexed family of
plane sections and integral arguments (`HCReal.localLift_general`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace HCReal

/-- A maximal compact element times a real element has integral finite part. -/
theorem mul_atInfinity_mem_integralArguments {compact : AdelicGL}
    (membership : inMaximalCompact compact) (real : RealGL3) :
    compact * atInfinity real ∈ integralArguments := by
  obtain ⟨integral, equation⟩ := membership.2
  refine ⟨integral, ?_⟩
  rw [map_mul, InducedContinuity.finiteGroup_atInfinity, mul_one, equation]

/-- The local scalar `EdgeInputs.localScalar` is the integral of the scalar integrand over the local
radical, for `Re s > -n/2 - 1`. -/
theorem localScalar_eq_integral {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re) (argument : AdelicGL)
    (integral : argument ∈ integralArguments) (binary : BinaryAdelicGL) :
    EdgeInputs.localScalar data holomorphic sectionValue parameter argument binary =
      ∫ coordinates, localScalarIntegrand data parameter
        (EdgeInputs.flatFamily data holomorphic sectionValue parameter)
        ((EdgeInputs.flatFamily_flat data holomorphic sectionValue).1 parameter) argument binary
        coordinates ∂localRadicalMeasure := by
  have memberSmooth : EdgeInputs.localVector data holomorphic sectionValue parameter argument ∈
      data.cusp.smooth :=
    localValue_mem_smooth data parameter
      (EdgeInputs.flatFamily data holomorphic sectionValue parameter)
      ((EdgeInputs.flatFamily_flat data holomorphic sectionValue).1 parameter) halfPlane argument
      integral
  have equality : EdgeInputs.localScalar data holomorphic sectionValue parameter argument binary =
      data.cusp.realize ⟨EdgeInputs.localVector data holomorphic sectionValue parameter argument,
        memberSmooth⟩ binary := by
    unfold EdgeInputs.localScalar
    exact EdgeInputs.vecScalar_of_mem data memberSmooth binary
  rw [equality]
  exact localValue_realizes data (EdgeInputs.flatFamily data holomorphic sectionValue)
    (EdgeInputs.flatFamily_flat data holomorphic sectionValue) parameter halfPlane argument
    integral binary

/-- **Realization of the Cauchy lift of the local vectors**, for an indexed family of plane sections
and arguments with integral finite part: the lift is fixed by the principal congruence subgroup and
realizes the circle average of the local scalars. -/
theorem localLift_general {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (multiplier : ℂ → ℂ) (radius : ℝ) (radiusPositive : 0 < radius)
    (ballSubset : Metric.closedBall cohomologicalPoint radius ⊆ EdgeInputs.localHalfPlane degree)
    (multiplierContinuous : ContinuousOn multiplier (Metric.sphere cohomologicalPoint radius))
    {index : Type}
    (sectionOf : index → SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argumentOf : index → AdelicGL) (integralOf : ∀ point, argumentOf point ∈ integralArguments)
    (lift : index → data.cusp.smooth)
    (liftEquation : ∀ point, (lift point).val = EndpointLift.endpointLift cohomologicalPoint radius
      multiplier (fun parameter => EdgeInputs.localVector data holomorphic (sectionOf point)
        parameter (argumentOf point)))
    (point : index) (binary : BinaryAdelicGL) :
    (∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) (lift point).val = (lift point).val) ∧
    data.cusp.realize (lift point) binary =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
        (parameter - cohomologicalPoint)⁻¹ • (multiplier parameter •
          EdgeInputs.localScalar data holomorphic (sectionOf point) parameter (argumentOf point)
            binary) := by
  have circle := circle_lift_realizes data
    (EdgeInputs.flatFamily data holomorphic (sectionOf point))
    (EdgeInputs.flatFamily_flat data holomorphic (sectionOf point))
    cohomologicalPoint radius radiusPositive ballSubset multiplier multiplierContinuous
    (argumentOf point) (integralOf point) (lift point) (liftEquation point) binary
  refine ⟨circle.1, ?_⟩
  rw [circle.2]
  congr 1
  refine circleIntegral.integral_congr radiusPositive.le (fun parameter membership => ?_)
  have halfPlane : -(degree : ℝ) / 2 - 1 < parameter.re :=
    ballSubset (Metric.sphere_subset_closedBall membership)
  have equation := localScalar_eq_integral data holomorphic (sectionOf point) parameter halfPlane
    (argumentOf point) (integralOf point) binary
  exact congrArg (fun value : ℂ => (parameter - cohomologicalPoint)⁻¹ • (multiplier parameter •
    value)) equation.symm

end HCReal

/-- **Input 3b (`EdgeInputs.LocalLiftRealization`).** The Cauchy lift of the local vectors
realizes the circle average of the local scalars. Unconditional. -/
theorem localLiftRealization {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EdgeInputs.LocalLiftRealization data holomorphic := by
  intro multiplier radius radiusPositive ballSubset multiplierContinuous arity family induced _
    compact compactMembership lift _ liftEquation x binary
  exact (HCReal.localLift_general data holomorphic multiplier radius radiusPositive ballSubset
    multiplierContinuous
    (fun point : Fin (arity + 1) → RealGL3 =>
      (⟨family (fun index => point index.castSucc), induced _⟩ :
        SectionSpace.inducedSections data .plane cohomologicalPoint))
    (fun point => compact * atInfinity (point (Fin.last arity)))
    (fun point => HCReal.mul_atInfinity_mem_integralArguments compactMembership
      (point (Fin.last arity)))
    lift liftEquation x binary).2

end TernaryPeriodPolynomials.EdgeConvergence
