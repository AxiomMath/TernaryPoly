module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.HCLiftFixed
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticBinary
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RightOrbitAnalyticity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.StandardSmooth

@[expose] public section


/-!
# The `GL₂(ℝ)` orbit of the Cauchy lift of the local vectors

Original work by Claude Sonnet 5.5.

For a binary real matrix `g`, the local Hilbert vector satisfies
`π(g) L_s(h) = |det g|^{-e(s)} L_s(lineLevi(1, g) h)` (`localValue_lineLevi_real`), where the exponent
`e(s)` is affine in `s`. The `s`-dependent part of the factor `|det g|^{-e(s)}` is the twist
`exp ((s - s₀) τ(r))` of the vertex `r = lineLevi(1, g)` by the weight `τ(r) = -(1/3) log det r`
(`HCLift.extendedWeight`). Hence
`π(g) liftAt(vertices, translation) = |det g|^{-e(s₀)} · liftAt'((r, vertices), r · (ρ · translation))`
(`orbit_identity`), where `liftAt'` is the Cauchy lift of the family with one more vertex and `ρ` the
real part of the maximal compact argument. The right hand side is smooth in `g` by the
analyticity of the lift in the vertices (`orbit_smooth`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix MeasureTheory
  Metric
open scoped Matrix.Norms.Elementwise NNReal
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.HCLift

/-- The `s`-dependent part of the determinant factor of the line Levi covariance. -/
theorem normPower_line_split (degree : ℕ) (parameter : ℂ) (matrix : BinaryRealGL) :
    normPower (GeneralLinearGroup.det (atInfinity matrix))
        (-binaryInductionExponent degree .line parameter) =
      normPower (GeneralLinearGroup.det (atInfinity matrix))
          (-binaryInductionExponent degree .line cohomologicalPoint) *
        Complex.exp ((parameter - cohomologicalPoint) *
          ((-(1 / 3) * Real.log matrix.val.det : ℝ) : ℂ)) := by
  have exponent : binaryInductionExponent degree .line parameter =
      binaryInductionExponent degree .line cohomologicalPoint +
        (parameter - cohomologicalPoint) / 3 := by
    simp only [binaryInductionExponent, inductionExponent]
    ring
  rw [SmoothNormPower.normPower_det_atInfinity, SmoothNormPower.normPower_det_atInfinity,
    exponent, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem lineLevi_det (matrix : BinaryRealGL) : (lineLevi 1 matrix).val.det = matrix.val.det := by
  rw [lineLevi_val]
  simp [Matrix.det_fin_three, Matrix.det_fin_two]

section Orbit

variable {degree arity : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)
  (family : (Fin arity → RealGL3) → AdelicGL → ℂ)
  (induced : ∀ vertices, IsInduced data .plane cohomologicalPoint (family vertices))
  (weight : (Fin arity → RealGL3) → ℝ)

/-- **The orbit identity.** -/
theorem orbit_identity (lift : HasSmoothCuspLift data .plane cohomologicalPoint family)
    (weightSmooth : Smooth weight) (circleRadius : ℝ) (circlePositive : 0 < circleRadius)
    (halfPlane : closedBall cohomologicalPoint circleRadius ⊆ EdgeInputs.localHalfPlane degree)
    (lam : ℂ → ℂ) (lamContinuous : ContinuousOn lam (sphere cohomologicalPoint circleRadius))
    (compact : AdelicGL) (compactMembership : inMaximalCompact compact)
    (vertices : Fin arity → RealGL3) (translation : RealGL3) (matrix : BinaryRealGL) :
    data.cusp.π (atInfinity matrix)
        (liftAt data holomorphic family induced weight circleRadius lam compact vertices
          translation) =
      normPower (GeneralLinearGroup.det (atInfinity matrix))
          (-binaryInductionExponent degree .line cohomologicalPoint) •
        liftAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
          (extendedWeight weight) circleRadius lam (atFinite (finiteGroup compact))
          (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 matrix) vertices)
          (lineLevi 1 matrix * (realGroup compact * translation)) := by
  rw [liftAt_compact data holomorphic family induced weight circleRadius lam compact vertices
    translation]
  have continuous := continuousOn_liftValue data holomorphic family induced weight lift
    weightSmooth circleRadius circlePositive halfPlane (atFinite (finiteGroup compact))
    (inMaximalCompact_atFinite compact compactMembership) vertices (realGroup compact * translation)
  let transformation :=
    (CuspHilbertAction.isometry data.cusp (atInfinity matrix)).toContinuousLinearMap
  let scalar := normPower (GeneralLinearGroup.det (atInfinity matrix))
    (-binaryInductionExponent degree .line cohomologicalPoint)
  let values : ℂ → data.cusp.H := fun parameter =>
    localFamilyValue data parameter (twistedAt data holomorphic family induced weight parameter)
      (twistedAt_induced data holomorphic family induced weight parameter) vertices
      (atFinite (finiteGroup compact) * atInfinity (realGroup compact * translation))
  let extendedValues : ℂ → data.cusp.H := fun parameter =>
    localFamilyValue data parameter
      (twistedAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
        (extendedWeight weight) parameter)
      (twistedAt_induced data holomorphic (dropFirst family)
        (dropFirst_induced data family induced) (extendedWeight weight) parameter)
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 matrix) vertices)
      (atFinite (finiteGroup compact) *
        atInfinity (lineLevi 1 matrix * (realGroup compact * translation)))
  have pointwise : ∀ parameter : ℂ, transformation (values parameter) =
      scalar • extendedValues parameter := by
    intro parameter
    have covariance := localValue_lineLevi_real data parameter
      (twistedAt data holomorphic family induced weight parameter vertices)
      (twistedAt_induced data holomorphic family induced weight parameter vertices) matrix
      (atFinite (finiteGroup compact) * atInfinity (realGroup compact * translation))
    have cancel : normPower (GeneralLinearGroup.det (atInfinity matrix))
        (-binaryInductionExponent degree .line parameter) *
        normPower (GeneralLinearGroup.det (atInfinity matrix))
          (binaryInductionExponent degree .line parameter) = 1 := by
      simpa only [mul_one] using ParabolicInvariance.normPower_neg_mul
        (GeneralLinearGroup.det (atInfinity matrix))
        (binaryInductionExponent degree .line parameter) (1 : ℂ)
    have line : lineLevi 1 (atInfinity matrix) *
        (atFinite (finiteGroup compact) * atInfinity (realGroup compact * translation)) =
        atFinite (finiteGroup compact) *
          atInfinity (lineLevi 1 matrix * (realGroup compact * translation)) := by
      conv_lhs => rw [← HilbertStandardSmooth.lineLevi_atInfinity, ← mul_assoc,
        ← RealTranslations.atFinite_atInfinity_commute, mul_assoc,
        ← RealTranslations.atInfinity_mul]
    have valueEquality : data.cusp.π (atInfinity matrix)
        (localValue data parameter (twistedAt data holomorphic family induced weight parameter
          vertices) (twistedAt_induced data holomorphic family induced weight parameter vertices)
          (atFinite (finiteGroup compact) * atInfinity (realGroup compact * translation))) =
        normPower (GeneralLinearGroup.det (atInfinity matrix))
            (-binaryInductionExponent degree .line parameter) •
          localValue data parameter (twistedAt data holomorphic family induced weight parameter
            vertices) (twistedAt_induced data holomorphic family induced weight parameter vertices)
            (atFinite (finiteGroup compact) *
              atInfinity (lineLevi 1 matrix * (realGroup compact * translation))) := by
      rw [← line, covariance, smul_smul, cancel, one_smul]
    have extended := localFamilyValue_extended data holomorphic family induced weight parameter
      (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 matrix) vertices)
      (atFinite (finiteGroup compact) *
        atInfinity (lineLevi 1 matrix * (realGroup compact * translation)))
    simp only [Fin.cons_zero, Fin.cons_succ] at extended
    change data.cusp.π (atInfinity matrix) (localValue data parameter
      (twistedAt data holomorphic family induced weight parameter vertices)
      (twistedAt_induced data holomorphic family induced weight parameter vertices)
      (atFinite (finiteGroup compact) * atInfinity (realGroup compact * translation))) =
      scalar • localFamilyValue data parameter
        (twistedAt data holomorphic (dropFirst family) (dropFirst_induced data family induced)
          (extendedWeight weight) parameter)
        (twistedAt_induced data holomorphic (dropFirst family)
          (dropFirst_induced data family induced) (extendedWeight weight) parameter)
        (Fin.cons (α := fun _ => RealGL3) (lineLevi 1 matrix) vertices)
        (atFinite (finiteGroup compact) *
          atInfinity (lineLevi 1 matrix * (realGroup compact * translation)))
    rw [extended, valueEquality, normPower_line_split, mul_smul]
    simp only [determinantTwist, lineLevi_det]
    rfl
  unfold liftAt
  change transformation (EndpointLift.endpointLift cohomologicalPoint circleRadius lam values) =
    scalar • EndpointLift.endpointLift cohomologicalPoint circleRadius lam extendedValues
  calc transformation (EndpointLift.endpointLift cohomologicalPoint circleRadius lam values)
      = EndpointLift.endpointLift cohomologicalPoint circleRadius lam
          (fun parameter => transformation (values parameter)) :=
        EndpointLift.map_endpointLift transformation circlePositive lamContinuous continuous
    _ = EndpointLift.endpointLift cohomologicalPoint circleRadius lam
          (fun parameter => scalar • extendedValues parameter) := by
        rw [funext pointwise]
    _ = scalar • EndpointLift.endpointLift cohomologicalPoint circleRadius lam extendedValues :=
        endpointLift_const_smul circlePositive lam scalar extendedValues

end Orbit

end TernaryPeriodPolynomials.EdgeConvergence.HCLift
