module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftMember

@[expose] public section


/-!
# Input 3a: the Cauchy lift of the local vectors

Original work by Claude Sonnet 5.5.

`EdgeInputs.LocalLiftVector`: for a function `lam` continuous on a circle inside the half plane
`Re s > -n/2 - 1`, a family of plane sections with a smooth cusp lift and a maximal compact `κ`, the
Cauchy lifts `W(x) = (2πi)⁻¹ ∮ (s - s₀)⁻¹ lam(s) L_s(κ · x_last) ds` of the local Hilbert vectors of
the flat family are smooth vectors of the cusp representation and depend smoothly on `x`. This is the
case of weight `0` of `HCLift.liftVector_smooth`, `HCLift.liftVector_mem_smooth`; the hypothesis
`LocalVectorsSmooth` is not needed (the membership in the smooth vectors is proved for the lift
directly).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Metric
open scoped Matrix.Norms.Elementwise
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- **Input 3a (`LocalLiftVector`).** -/
theorem localLiftVector {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EdgeInputs.LocalLiftVector data holomorphic := by
  intro lam radius radiusPositive halfPlane continuous arity family induced lift compact
    compactMembership
  have weightSmooth : Smooth (fun _ : Fin arity → RealGL3 => (0 : ℝ)) := contDiffOn_const
  refine ⟨fun x => ⟨HCLift.liftVector data holomorphic family induced (fun _ => 0) radius lam
    compact x, HCLift.liftVector_mem_smooth data holomorphic family induced (fun _ => 0) lift
      weightSmooth radius radiusPositive halfPlane lam continuous compact compactMembership x⟩,
    ?_, ?_⟩
  · exact HCLift.liftVector_smooth data holomorphic family induced (fun _ => 0) lift weightSmooth
      radius radiusPositive halfPlane lam continuous compact compactMembership
  · intro x
    change EndpointLift.endpointLift cohomologicalPoint radius lam _ = _
    congr 1
    funext parameter
    unfold localFamilyValue
    exact HCLift.localValue_congr data parameter (funext fun y => by simp [HCLift.twistedAt,
      HCLift.flatAt]) _ _ _

end TernaryPeriodPolynomials.EdgeConvergence
