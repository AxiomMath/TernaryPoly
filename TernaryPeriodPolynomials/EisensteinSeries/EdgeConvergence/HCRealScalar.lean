module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCRealLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FixedFamilyAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Analyticity

@[expose] public section


/-!
# Scalar smoothness of a smooth vector family in one real variable from its joint orbit

Original work by Claude Sonnet 5.5.

For a family `x ↦ W(x)` of smooth vectors fixed by the principal congruence subgroup, indexed by one
real matrix `x ∈ GL₃(ℝ)` (the case `arity = 0`), the scalar `x ↦ realize (W x) B` is real analytic as
soon as the joint orbit `(b, x) ↦ π(b) W(x)` is real analytic on `GL₂(ℝ) × GL₃(ℝ)`
(`FixedFamilyAnalyticity.scalar_analyticAt`, finite rotation types). This is the form in which the
scalar smoothness of the Cauchy lift of the local standard integrals (`EdgeInputs.LocalLiftScalarSmooth`,
input 3c, a single plane section) is reduced to a statement about the Hilbert-space valued joint
orbit (`LocalLiftOrbit`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
  (PlaneMatrix JointMatrix BinaryMatrix jointDomain jointDomain_isOpen)
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

namespace HCReal

/-- **Scalar smoothness from joint orbit smoothness (one real variable).** -/
theorem scalar_smooth_of_orbit {degree : ℕ} (data : InducingData degree)
    (lift : (Fin 1 → RealGL3) → data.cusp.smooth)
    (fixed : ∀ x, ∀ unit : BinaryLevel.finiteCongruence,
      data.cusp.π (atFinite unit.val) (lift x).val = (lift x).val)
    (orbit : ContDiffOn ℝ ⊤ (fun matrices : JointMatrix => data.cusp.π
      (atInfinity (invertibleMatrix matrices.1))
      (lift (fun _ => invertibleMatrix matrices.2)).val) jointDomain)
    (binary : BinaryAdelicGL) :
    Smooth (fun x : Fin 1 → RealGL3 => data.cusp.realize (lift x) binary) := by
  obtain ⟨family, familyEquation⟩ : ∃ family : PlaneMatrix → data.cusp.smooth,
      ∀ matrix, family matrix = lift (fun _ => invertibleMatrix matrix) :=
    ⟨fun matrix => lift (fun _ => invertibleMatrix matrix), fun _ => rfl⟩
  have familyFixed : ∀ matrix, (family matrix).val ∈
      BinaryLevel.fixedSubspace data.cusp BinaryLevel.finiteCongruence := by
    intro matrix unit
    rw [familyEquation]
    exact fixed _ unit
  have scalarAnalytic : ∀ center : PlaneMatrix, center.det ≠ 0 →
      AnalyticAt ℝ (fun matrix => data.cusp.realize (family matrix) binary) center := by
    intro center centerInvertible
    have jointSmooth : ContDiffOn ℝ ⊤ (LocalAnalyticFamilies.familyOrbit data.cusp
        (fun matrix => (family matrix).val)) jointDomain := by
      refine orbit.congr (fun matrices _ => ?_)
      change data.cusp.π (atInfinity (invertibleMatrix matrices.1)) (family matrices.2).val = _
      rw [familyEquation]
    have membership : ((1 : BinaryMatrix), center) ∈ jointDomain := ⟨by simp, centerInvertible⟩
    have joint : AnalyticAt ℝ (LocalAnalyticFamilies.familyOrbit data.cusp
        (fun matrix => (family matrix).val)) (1, center) :=
      (jointSmooth.contDiffAt (jointDomain_isOpen.mem_nhds membership)).analyticAt
    exact FixedFamilyAnalyticity.scalar_analyticAt data.cusp BinaryLevel.finiteCongruence
      BinaryLevel.finiteCongruence_isOpen BinaryLevel.finiteCongruence_isCompact
      (EndpointAdmissibility.all_finiteDimensional data) family familyFixed center joint binary
  apply (SmoothAnalyticity.smooth_iff_analyticOn _).mpr
  intro matrices membership
  have analytic := scalarAnalytic (matrices 0) (membership 0)
  have extensionEquality : SmoothJets.matrixExtension
      (fun x : Fin 1 → RealGL3 => data.cusp.realize (lift x) binary) =
      fun other : SmoothJets.MatrixTuples 3 1 => data.cusp.realize (family (other 0)) binary := by
    funext other
    rw [familyEquation]
    have indexEquality : (fun index : Fin 1 => invertibleMatrix (other index)) =
        fun _ => invertibleMatrix (other 0) :=
      funext (fun index => by rw [Subsingleton.elim index 0])
    change data.cusp.realize (lift (fun index : Fin 1 => invertibleMatrix (other index))) binary = _
    rw [indexEquality]
  rw [extensionEquality]
  let projection : SmoothJets.MatrixTuples 3 1 →L[ℝ] PlaneMatrix := ContinuousLinearMap.proj 0
  exact (analytic.fun_comp (f := fun other : SmoothJets.MatrixTuples 3 1 => other 0)
    (x := matrices) (projection.analyticAt matrices)).analyticWithinAt

end HCReal

/-- **Remaining input at arity `0` (`LocalLiftOrbit`): the Cauchy lift with an analytic joint
orbit.** For a single plane section `f`, a maximal compact `κ` and a multiplier `m` continuous on
the circle `|s - s₀| = r` inside `Re s > -n/2 - 1`, the Cauchy lift
`W(x) = (2πi)⁻¹ ∮ (s-s₀)⁻¹ (m(s) • L_s(κ x))` of the local standard integrals (`EndpointLift.endpointLift`)
is a family of smooth vectors of the cusp representation, indexed by the real matrix `x ∈ GL₃(ℝ)`,
whose joint orbit `(b, x) ↦ π(b) W(x)` is real analytic on `GL₂(ℝ) × GL₃(ℝ)` (Hilbert space valued).

This is `EdgeInputs.LocalLiftVector` (input 3a) at arity `0` with the extra variable `b`: since
`π(b) L_s(g) = |det b|^{-e(s)} L_s(lineLevi(b) g)` (`localValue_lineLevi_real`), the orbit of the
circle average is the circle average of the family
`(b, x) ↦ m(s) |det b|^{-e(s)} L_s(lineLevi(b) κ x)`, whose Taylor series are uniform on the circle
(`LocalTaylorProducer`, `EndpointLiftTaylor.circleAverage_hasFPowerSeriesOnBall`). The `s`-dependent
twist `|det b|^{-e(s)}` is why 3a for the fixed multiplier `m` does not imply it. By
`HCReal.scalar_smooth_of_orbit` it implies the scalar smoothness `localLiftScalarSmooth`
(`EdgeInputs.LocalLiftScalarSmooth`, input 3c). -/
def LocalLiftOrbit {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) : Prop :=
  ∀ (multiplier : ℂ → ℂ) (radius : ℝ), 0 < radius →
    Metric.closedBall cohomologicalPoint radius ⊆ EdgeInputs.localHalfPlane degree →
    ContinuousOn multiplier (Metric.sphere cohomologicalPoint radius) →
    ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (compact : AdelicGL), inMaximalCompact compact →
      ∃ lift : (Fin 1 → RealGL3) → data.cusp.smooth,
        (∀ x, (lift x).val = EndpointLift.endpointLift cohomologicalPoint radius multiplier
          (fun parameter => EdgeInputs.localVector data holomorphic sectionValue parameter
            (compact * atInfinity (x 0)))) ∧
        ContDiffOn ℝ ⊤ (fun matrices : JointMatrix => data.cusp.π
          (atInfinity (invertibleMatrix matrices.1))
          (lift (fun _ => invertibleMatrix matrices.2)).val) jointDomain

/-- **Input 3c (`EdgeInputs.LocalLiftScalarSmooth`)**, from the analytic joint orbit
`LocalLiftOrbit` of the Cauchy lift of the local vectors. -/
theorem localLiftScalarSmooth {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (orbit : LocalLiftOrbit data holomorphic) :
    EdgeInputs.LocalLiftScalarSmooth data holomorphic := by
  intro multiplier radius radiusPositive ballSubset multiplierContinuous sectionValue compact
    compactMembership binary
  obtain ⟨lift, liftEquation, liftOrbit⟩ := orbit multiplier radius radiusPositive ballSubset
    multiplierContinuous sectionValue compact compactMembership
  have general := fun x : Fin 1 → RealGL3 => HCReal.localLift_general data holomorphic multiplier
    radius radiusPositive ballSubset multiplierContinuous
    (fun _ : Fin 1 → RealGL3 => sectionValue) (fun point => compact * atInfinity (point 0))
    (fun point => HCReal.mul_atInfinity_mem_integralArguments compactMembership (point 0))
    lift liftEquation x binary
  have equality : (fun x : Fin 1 → RealGL3 =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ parameter in C(cohomologicalPoint, radius),
        (parameter - cohomologicalPoint)⁻¹ • (multiplier parameter • EdgeInputs.localScalar data
          holomorphic sectionValue parameter (compact * atInfinity (x 0)) binary)) =
      fun x => data.cusp.realize (lift x) binary := funext (fun x => (general x).2.symm)
  have smooth : Smooth (fun x : Fin 1 → RealGL3 => data.cusp.realize (lift x) binary) :=
    HCReal.scalar_smooth_of_orbit data lift (fun x unit => (general x).1 unit) liftOrbit binary
  exact (congrArg (fun function : (Fin 1 → RealGL3) → ℂ => Smooth function) equality).mpr smooth

end TernaryPeriodPolynomials.EdgeConvergence
