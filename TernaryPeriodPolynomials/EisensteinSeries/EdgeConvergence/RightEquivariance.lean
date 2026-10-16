module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Standard
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.RightEquivarianceAnalytic

@[expose] public section


/-!
# Right real equivariance of the edge standard value: reduction to one two-variable family

`EdgeStandardOperator.right_real` says `S (R(h) f) = R(h) (S f)` for the holomorphic-continuation
standard operator `S = HolomorphicStandardValue.sectionStandard`. Fix a plane section `f`, a real
`h` and an adelic `g`. Write `cont f` for the chosen standard continuation of the (unique) flat
family of `f`. Then `S f (g) = cont f s₀ g`, so the claim is

  `cont (R(h) f) s₀ g = cont f s₀ (g h)`.                                            (*)

`DiagonalDatum` packages a family `G(s, z)` with `G(s₀, 0) = cont (R(h) f) s₀ g` and
`G(s, s - s₀) = cont f s (g h)` for `s ≠ s₀` near `s₀` (take `G(s, z)` the standard integral of the
flat family of `ρ_h^z · R(h) f`, see `SectionMultipliers`), holomorphic in `s` on a closed disc for
each small `z`, and jointly continuous on the circle `|s - s₀| = r`. Then (*) holds by
`RightEquivariance.eq_of_axis_diagonal`, with no control of the pole order of `λ̃`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Metric Filter Topology
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance

/-- The chosen standard continuation of the flat family of a plane section. -/
def sectionContinuation {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    ℂ → AdelicGL → ℂ :=
  StandardValue.chosenContinuation data
    (HolomorphicStandardValue.regularFamily data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic sectionValue))

/-- The edge standard value is the endpoint value of the chosen continuation. -/
theorem edgeStd_apply {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    (EdgeStandard.edgeStd data holomorphic sectionValue).val argument =
      sectionContinuation data holomorphic sectionValue cohomologicalPoint argument := rfl

/-- The chosen continuation is analytic at the cohomological point (Sol's `HasRegularStandard`). -/
theorem sectionContinuation_analyticAt {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    AnalyticAt ℂ (fun parameter => sectionContinuation data holomorphic sectionValue parameter argument)
      cohomologicalPoint :=
  (StandardValue.chosenContinuation_spec data
    (HolomorphicStandardValue.regularFamily data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic sectionValue))).2 argument

/-- A two-variable family comparing the flat family of `R(h) f` at `g` (the axis `z = 0`) with the
flat family of `f` at `g h` (the diagonal `z = s - s₀`). -/
structure DiagonalDatum {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (argument : AdelicGL) where
  family : ℂ → ℂ → ℂ
  radius : ℝ
  width : ℝ
  radius_pos : 0 < radius
  width_pos : 0 < width
  axis : sectionContinuation data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)
      cohomologicalPoint argument = family cohomologicalPoint 0
  diagonal : ∀ᶠ parameter in 𝓝[≠] cohomologicalPoint,
    sectionContinuation data holomorphic sectionValue parameter (argument * atInfinity real) =
      family parameter (parameter - cohomologicalPoint)
  holomorphic_in_parameter : ∀ z : ℂ, ‖z‖ < width →
    DifferentiableOn ℂ (fun parameter => family parameter z) (closedBall cohomologicalPoint radius)
  continuous_on_circle : ContinuousOn (fun p : ℂ × ℂ => family p.1 p.2)
    (sphere cohomologicalPoint radius ×ˢ ball (0 : ℂ) width)

/-- Equation (*) at one point, from a `DiagonalDatum`. -/
theorem value_eq_of_diagonalDatum {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (argument : AdelicGL)
    (datum : DiagonalDatum data holomorphic sectionValue real argument) :
    sectionContinuation data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)
        cohomologicalPoint argument =
      sectionContinuation data holomorphic sectionValue cohomologicalPoint
        (argument * atInfinity real) :=
  eq_of_axis_diagonal datum.radius_pos datum.width_pos datum.holomorphic_in_parameter
    datum.continuous_on_circle
    (A := fun parameter => sectionContinuation data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)
      parameter argument)
    (B := fun parameter => sectionContinuation data holomorphic sectionValue parameter
      (argument * atInfinity real))
    datum.axis
    (sectionContinuation_analyticAt data holomorphic sectionValue
      (argument * atInfinity real)).continuousAt
    datum.diagonal

/-- Right real equivariance of the edge standard operator, given a `DiagonalDatum` for every
section, real element and adelic point. -/
theorem right_real_of_diagonalData {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (datum : ∀ (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (real : RealGL3) (argument : AdelicGL),
      Nonempty (DiagonalDatum data holomorphic sectionValue real argument))
    (real : RealGL3) (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    (EdgeStandard.edgeStd data holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val =
      fun argument => (EdgeStandard.edgeStd data holomorphic sectionValue).val
        (argument * atInfinity real) := by
  funext argument
  obtain ⟨family⟩ := datum sectionValue real argument
  exact value_eq_of_diagonalDatum data holomorphic sectionValue real argument family

end TernaryPeriodPolynomials.EdgeConvergence.RightEquivariance
