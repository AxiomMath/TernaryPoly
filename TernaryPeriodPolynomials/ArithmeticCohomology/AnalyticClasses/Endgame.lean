module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ComparisonAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Target.Glue
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicit
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.TransferCommute

@[expose] public section


/-!
# The arithmetic period of the finite average of the source endpoint vanishes

Let `v` be the classical lower endpoint of the binary cocycle `B` of the canonical relative
cocycle of the determinant-normalized source, reconstructed as `B = N_{F_v} + δκ` from `v` and a
smooth spherical correction `κ`. Then the arithmetic period class of the finite average of `v`
vanishes: the averaged real form `F_avg` satisfies the real-side comparison with the averaged
transfer `T = t_{N_{F_avg}} + δH` and the one-cochain `β = F_rad - prism - edge`, so the twisted
Eichler normal form of `F_avg` at the identity, which is the finite average of that of `F_v`, is a
one-coboundary of `GL₂(ℤ)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {index : Type} [Fintype index]

/-- **The arithmetic period of the finite average of the source endpoint vanishes.** -/
theorem cuspClassicalArithmeticPeriodMap_sourceEndpoint_eq_zero (large : 9 ≤ n) (odd : Odd n)
    (local_entry : LocalBadPlaneEntry) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument =>
        (standard parameter vertices argument).val.coeff monomial))
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial)
        cohomologicalPoint)
    (linePrimitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
      goodLineCoefficientRep n)
    (lineRelative : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n))
    (lineFormula : ∀ first second : flagArithmeticStabilizer .line
        (QuotientGroup.mk rationalGoodLine),
      lineRelative.val (first, second) = (id (goodLineComplementFamily standard
          cohomologicalPoint (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (![1, first.val, first.val * second.val] index))) : goodLineCoefficientRep n) -
        ((goodLineCoefficientRep n).ρ first (linePrimitive second) -
          linePrimitive (first * second) + linePrimitive first))
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (primitive_analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis
            (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (projected : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ)
      (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      ∫ u, projectedAverage data source cocycle γ functional u
          ∂((volume : Measure ℝ).prod volume) =
        functional (goodLineMixedCoordinate n γ (fun pair =>
          twoBoundaryCycle (goodLineCoefficientRep n)
            (linePrimitive - prismStabilizerCochain data source cocycle) pair)))
    (canonical : ∀ (γ : GeneralLinearGroup (Fin 2) ℤ)
      (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ),
      ∫ u, projectedAverage data source cocycle γ functional u
          ∂((volume : Measure ℝ).prod volume) =
        ∫ u, canonicalProjectedAverage data trivial basis relative regular γ functional u
            ∂((volume : Measure ℝ).prod volume) +
          functional (goodLineMixedCoordinate n γ (fun pair =>
            twoBoundaryCycle (goodLineCoefficientRep n)
              (edgeStabilizerCochain data
                (totalPrimitiveEdge data trivial basis primitive relative regular)) pair)))
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      data.cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((n : ℤ) + 3))
    (classical : cuspClassicalVectors data.cusp halfWeight)
    (hF : EichlerData n (cuspScalarWeightedRealization data.cusp halfWeight classical.val))
    (correction : Fin (n + 2) → data.cusp.H)
    (correction_smooth : ∀ position, correction position ∈ data.cusp.smooth)
    (correction_spherical : ∀ position, correction position ∈ cuspSphericalValues data.cusp)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding data.cusp (binaryWeightBasis (n + 1))
          (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod data.cusp n halfWeight classical.val.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod data.cusp n halfWeight classical.val.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) A correction -
          correction)) :
    cuspClassicalArithmeticPeriodMap data.cusp halfWeight (by omega) (n + 1) (by omega)
      (by obtain ⟨half, equality⟩ := odd; exact ⟨half + 1, by omega⟩) 0 0 (by norm_num)
      (cuspClassicalFiniteAverageFamily data.cusp central_positive halfWeight (by omega)
        ((n : ℂ) / 2 + 3 + cohomologicalPoint) classical) = 0 := by
  have spherical := classical.property.1
  have averaged := hF.averagedReal_cuspScalar data.cusp halfWeight classical.val spherical
    (by omega)
  have velocity : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  obtain ⟨P, hP⟩ := exists_eichlerTwisted_coboundary large averaged
    (averagedRealForm_cuspScalar_left_realLevi data.cusp halfWeight classical.val spherical)
    (2 * Real.pi * Complex.I) velocity
    (lowerRadicalCoordinate_edgeMixedIntegral (by omega) averaged)
    (hasDerivAt_edgeNormal_diagonal averaged) 1 (fun g => by rw [one_mul, mul_one])
    (fun q => averagedLine (bridgeTransfer (hilbertLift data.cusp n correction) q))
    (fun q g ℓ => by
      rw [one_mul]
      exact linearAt_averagedLine_bridgeTransfer (by omega) data.cusp correction
        correction_smooth correction_spherical q g ℓ)
    (fun γ q ℓ => by
      have invariant := averagedLine_bridgeTransfer_hilbertLift_realLevi data.cusp correction
        correction_smooth correction_spherical q γ 1 ℓ
      rw [atInfinity_one] at invariant
      exact invariant)
    (linePrimitive - prismStabilizerCochain data source cocycle -
      edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative regular))
    (radical_averagedTransfer data trivial basis source cocycle linePrimitive primitive relative
      regular halfWeight classical.val spherical hF correction correction_smooth
      correction_spherical reconstruction large local_entry flat standard sections endpoint
      support continuations analytic lineRelative lineFormula primitive_analytic formula)
    (mixed_averagedTransfer data trivial basis source cocycle linePrimitive primitive relative
      regular halfWeight classical.val spherical hF correction correction_smooth
      correction_spherical reconstruction large projected canonical)
  refine cuspClassicalArithmeticPeriodMap_finiteAverage_eq_zero data.cusp central_positive large
    odd halfWeight weight classical ⟨P, fun γ => ?_⟩
  rw [← eichlerTwisted_averagedRealForm_eq data.cusp halfWeight classical.val spherical
    (by omega), hP γ]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
