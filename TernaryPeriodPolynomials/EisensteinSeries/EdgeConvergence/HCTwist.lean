module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCTwistBound
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCTwistIntegrand

@[expose] public section


/-!
# Joint continuity of the local scalar of the twisted sections

Original work by Claude Sonnet 5.5.

The fourth input `EdgeInputs.TwistedLocalContinuity` of the `n = 3` totality argument: for a
plane section `f`, a real element `h`, a maximal compact `κ` and a binary adele `B`, the realization
at `B` of the local Hilbert standard integral of the flat family of `Φ_z = ρ_h^z · R(h) f` at `κ` is
jointly continuous in `(s, z)` on `{|s - s₀| ≤ r} × {|z| < w}`, whenever the closed disc lies in
`Re s > -n/2 - 1`.

The proof is dominated convergence (`MeasureTheory.continuousOn_of_dominated`) for the scalar
integrand of the local standard integral. By `HCTwistIntegrand`, that integrand is the explicit
function `twistIntegrand s z u`, jointly continuous in `(s, z)`, and
`twistIntegrand s z u = ρ_h(P)^z · twistIntegrand s 0 u`. The `z = 0` integrand is dominated, uniformly
on the vertical strip `|Re s - Re s₀| ≤ r`, by an integrable power of the local height
(`localScalarIntegrand_bound`), and `|ρ_h(P)^z| ≤ exp (w C_h)` by `HCTwistBound.logXi_translate_bounded`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence.HCTwist

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- **Input 4 (`TwistedLocalContinuity`), proved.** -/
theorem twistedLocalContinuity_unconditional {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : SectionMultipliers.HeightLaw logXi) :
    EdgeInputs.TwistedLocalContinuity data holomorphic law := by
  intro sectionValue real compact compactMembership binary radius width halfPlane
  rcases lt_or_ge radius 0 with negative | nonnegative
  · have empty : Metric.closedBall cohomologicalPoint radius = ∅ :=
      Metric.closedBall_eq_empty.mpr negative
    rw [empty, Set.empty_prod]
    exact continuousOn_empty _
  obtain ⟨lower, lowerDef⟩ : ∃ lower : ℝ, lower = cohomologicalPoint.re - radius := ⟨_, rfl⟩
  obtain ⟨upper, upperDef⟩ : ∃ upper : ℝ, upper = cohomologicalPoint.re + radius := ⟨_, rfl⟩
  have lowerPoint : cohomologicalPoint - (radius : ℂ) ∈
      Metric.closedBall cohomologicalPoint radius := by
    have distance : dist (cohomologicalPoint - (radius : ℂ)) cohomologicalPoint = radius := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg nonnegative]
    exact Metric.mem_closedBall.mpr distance.le
  have lowerHalfPlane : -(degree : ℝ) / 2 - 1 < lower := by
    have membership : -(degree : ℝ) / 2 - 1 < (cohomologicalPoint - (radius : ℂ)).re :=
      halfPlane lowerPoint
    have realPart : (cohomologicalPoint - (radius : ℂ)).re = cohomologicalPoint.re - radius := by
      simp
    rw [realPart] at membership
    rw [lowerDef]
    exact membership
  have ordered : lower ≤ upper := by
    rw [lowerDef, upperDef]
    linarith
  have strip : ∀ parameter ∈ Metric.closedBall cohomologicalPoint radius,
      lower ≤ parameter.re ∧ parameter.re ≤ upper := by
    intro parameter membership
    have distance : ‖parameter - cohomologicalPoint‖ ≤ radius := by
      have raw := Metric.mem_closedBall.mp membership
      rwa [dist_eq_norm] at raw
    have realPart : |(parameter - cohomologicalPoint).re| ≤ radius :=
      (Complex.abs_re_le_norm _).trans distance
    rw [Complex.sub_re] at realPart
    obtain ⟨left, right⟩ := abs_le.mp realPart
    constructor
    · rw [lowerDef]
      linarith
    · rw [upperDef]
      linarith
  obtain ⟨heightBound, _, heightBounded⟩ := HCTwistBound.logXi_translate_bounded law real
  obtain ⟨constant, _, zeroBounded⟩ := localScalarIntegrand_bound data
    (EdgeInputs.flatFamily data holomorphic (twistSection data law real 0 sectionValue))
    (EdgeInputs.flatFamily_flat data holomorphic (twistSection data law real 0 sectionValue))
    lower upper lowerHalfPlane ordered compact (integralArguments_of_compact compactMembership)
  have dominated : ContinuousOn (fun p : ℂ × ℂ => ∫ coordinates,
      twistIntegrand degree logXi sectionValue.val real binary compact p.1 p.2 coordinates
        ∂localRadicalMeasure)
      (Metric.closedBall cohomologicalPoint radius ×ˢ Metric.ball (0 : ℂ) width) := by
    refine continuousOn_of_dominated
      (F := fun (p : ℂ × ℂ) (coordinates : LocalLine × LocalLine) =>
        twistIntegrand degree logXi sectionValue.val real binary compact p.1 p.2 coordinates)
      (bound := fun coordinates =>
        Real.exp (width * heightBound) * hcMajorant degree lower constant coordinates)
      ?_ ?_ ?_ ?_
    · intro p _
      have sameFunction : (fun coordinates => twistIntegrand degree logXi sectionValue.val real
          binary compact p.1 p.2 coordinates) =
          localScalarIntegrand data p.1
            (EdgeInputs.flatFamily data holomorphic (twistSection data law real p.2 sectionValue)
              p.1)
            ((EdgeInputs.flatFamily_flat data holomorphic
              (twistSection data law real p.2 sectionValue)).1 p.1) compact binary :=
        funext fun coordinates => (localScalarIntegrand_twist data holomorphic law sectionValue
          real binary compact p.2 p.1 coordinates).symm
      show AEStronglyMeasurable (fun coordinates => twistIntegrand degree logXi sectionValue.val
        real binary compact p.1 p.2 coordinates) localRadicalMeasure
      rw [sameFunction]
      exact (localScalarIntegrand_continuous data p.1 _ _ compact binary).aestronglyMeasurable
    · intro p membership
      refine Filter.Eventually.of_forall (fun coordinates => ?_)
      obtain ⟨lowerBound, upperBound⟩ := strip p.1 membership.1
      have zeroBound : ‖twistIntegrand degree logXi sectionValue.val real binary compact p.1 0
          coordinates‖ ≤ hcMajorant degree lower constant coordinates := by
        have raw := zeroBounded p.1 lowerBound upperBound binary coordinates
        rw [localScalarIntegrand_twist data holomorphic law sectionValue real binary compact 0
          p.1 coordinates] at raw
        exact raw
      have multiplierBound := HCTwistBound.norm_heightMultiplier_le logXi real p.2
        (evaluationPoint binary compact coordinates) width heightBound
        (heightBounded _) (mem_ball_zero_iff.mp membership.2).le
      show ‖twistIntegrand degree logXi sectionValue.val real binary compact p.1 p.2 coordinates‖ ≤
        Real.exp (width * heightBound) * hcMajorant degree lower constant coordinates
      rw [twistIntegrand_eq_mul degree logXi sectionValue.val real binary compact p.1 p.2
        coordinates, norm_mul]
      exact mul_le_mul multiplierBound zeroBound (norm_nonneg _) (Real.exp_nonneg _)
    · exact (hcMajorant_integrable lower constant lowerHalfPlane).const_mul _
    · exact Filter.Eventually.of_forall (fun coordinates =>
        (twistIntegrand_continuous degree logXi sectionValue.val real binary compact
          coordinates).continuousOn)
  refine dominated.congr ?_
  intro p membership
  have halfP : -(degree : ℝ) / 2 - 1 < p.1.re := halfPlane membership.1
  exact localScalar_twist_eq_integral data holomorphic law sectionValue real p.1 p.2 halfP compact
    compactMembership binary

/-- **Input 4 (`TwistedLocalContinuity`).** The statement of the interface of `EdgeAssembly`:
the hypotheses `LocalVectorsSmooth` and `LocalScalarAnalytic` are not needed (the smoothness of the
local vectors of every plane section is `localValue_mem_smooth`). -/
theorem twistedLocalContinuity {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) {logXi : AdelicGL → ℝ}
    (law : SectionMultipliers.HeightLaw logXi)
    (_localVectorsSmooth : EdgeInputs.LocalVectorsSmooth data holomorphic)
    (_localScalarAnalytic : EdgeInputs.LocalScalarAnalytic data holomorphic) :
    EdgeInputs.TwistedLocalContinuity data holomorphic law :=
  twistedLocalContinuity_unconditional data holomorphic law

end TernaryPeriodPolynomials.EdgeConvergence
