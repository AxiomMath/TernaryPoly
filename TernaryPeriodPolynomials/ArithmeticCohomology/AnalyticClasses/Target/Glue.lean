module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Target.GlueLinear
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.LatticeAssembly
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Target.GlueConv
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalTransferGlueAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay

@[expose] public section


/-!
# The radical and mixed identities of the good-line target

On the arithmetic good-line stabilizer let
`β = F_rad - prism - edge` be the radical primitive of the complementary good-line family minus
the integrated Iwasawa prism cochain and the edge stabilizer cochain of the explicit total
primitive. Let `T = t_{N_{F_avg}} + δH` be the averaged real transfer of the binary cocycle `B`
of the canonical relative cocycle, reconstructed as `B = N_{F_v} + δκ` from its classical endpoint
`v` and a finite-level correction `κ`.

* On radical pairs, `δβ (r₁, r₂)` is the vector of `T` at the real radical elements `3 r₁, 3 r₂`
  at the identity: the complementary family is `δ F_rad` there, the radical-pair decomposition
  identifies it with the integrated finite average of the canonical term plus `δ(prism + edge)`,
  and that integral is the finite average of the transfer of `B`.
* The mixed coordinate of `δβ` at `γ` is the sum over the two radical generators of the mixed
  radical edges of `T` at the identity, tested through the lower radical lattice contributions:
  the projected coboundary and the canonical reduction identify it with the integral of the
  canonical projected average.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

variable {n : ℕ} {index : Type} [Fintype index]

theorem twoBoundaryCycle_sub_apply {E : Type} [Group E] (representation : Rep ℂ E)
    (first second : E → representation) (pair : E × E) :
    twoBoundaryCycle representation (first - second) pair =
      twoBoundaryCycle representation first pair - twoBoundaryCycle representation second pair := by
  obtain ⟨g, h⟩ := pair
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply, Pi.sub_apply,
    Pi.sub_apply, Pi.sub_apply, map_sub]
  abel

/-- **Regularity of the binary values of the canonical relative cocycle** from the
reconstruction of its binary cocycle by the classical endpoint and a smooth correction. -/
theorem canonicalBinaryValues_regular_of_reconstruction (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) (halfWeight : ℤ)
    (vector : data.cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues data.cusp)
    (correction : Fin (n + 2) → data.cusp.H)
    (correction_smooth : ∀ position, correction position ∈ data.cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding data.cusp (binaryWeightBasis (n + 1))
          (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod data.cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod data.cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) A correction - correction)) :
    BinaryValuesRegular (canonicalBinaryValues data trivial basis relative regular) :=
  canonicalBinaryValues_regular data trivial basis relative regular halfWeight vector correction
    correction_smooth fun A h => original_eq_eichlerNormal_add_of_smooth data.cusp
      (continuousStages data) halfWeight vector (spherical_mem_fixedSubspace _ _ spherical)
      (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular)
      correction correction_smooth reconstruction A h

/-- A scalar test of the lattice coordinate of coefficient vectors at the identity is the sum of
the tests through the lower radical lattice contributions. -/
theorem functional_latticeCoordinate_lineVector (X : RadicalLattice → LineValues n)
    (linear : ∀ r, LinearAt (X r) 1) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    functional (latticeCoordinate n (fun r => lineVector (X r) 1)) =
      ∑ i : Fin 2, X (![radicalLatticeFirst, radicalLatticeSecond] i)
        (1, functional.comp (lowerRadicalLatticeContribution n i)) := by
  have expand := lowerRadicalCoordinate_averages n
    (fun i => lineVector (X (radicalLatticeGenerator i)) 1)
  change functional (lowerRadicalCoordinate n (fun i => (lowerRadicalAverageEquiv n i).symm
    (lineVector (X (radicalLatticeGenerator i)) 1))) = _
  rw [expand, map_add, Fin.sum_univ_two, linear, linear]
  rfl

/-! ### Instantiating the endpoint data -/

/-- **The Eichler data of the classical lower endpoint**: the scalar weighted realization of a
classical vector equal to the lower endpoint of a closed relative pair has the Eichler data. -/
theorem eichlerData_classicalEndpoint (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (odd : Odd n) (cohomological : Cohomological cusp n)
    (level : Subgroup BinaryFiniteGL) (halfWeight : ℤ) (weight : 2 * halfWeight = -((n : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (n + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight n (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight n 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (n + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (n + 1)) 2 upper)
    (classical : cuspClassicalVectors cusp halfWeight)
    (value : classical.val.val = (lower 0).val) :
    EichlerData n (cuspScalarWeightedRealization cusp halfWeight classical.val) :=
  eichlerData_cuspScalarWeightedRealization cusp
    (cohomological_centralCharacter_positive cusp cohomological) halfWeight classical.val
    classical.property.2.1 weight
    (classicalEndpoint_scalar_holomorphic cusp spherical odd cohomological level halfWeight weight
      lower upper lower_mem upper_mem closed classical value)

/-- A tuple fixed by `GL₂(Ẑ)` is spherical. -/
theorem spherical_of_integralLevel (cusp : CuspidalRepresentation)
    (correction : Fin (n + 2) → cusp.H)
    (fixed : correction ∈ binaryHilbertFiniteValues cusp (finiteIntegralGLLevel 2))
    (position : Fin (n + 2)) : correction position ∈ cuspSphericalValues cusp :=
  fun element => fixed ⟨_, element, rfl⟩ position

section Glue

variable (data : InducingData n) (trivial : data.chi = trivialCharacter)
  (basis : Module.Basis index ℂ (HomogeneousPoly n))
  (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
  (linePrimitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) →
    goodLineCoefficientRep n)
  (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
  (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
    (realPlaneLevelCuspidalRep n data.cusp data.chi))
  (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
  (halfWeight : ℤ) (vector : data.cusp.smooth)
  (spherical : vector.val ∈ cuspSphericalValues data.cusp)
  (hF : EichlerData n (cuspScalarWeightedRealization data.cusp halfWeight vector))
  (correction : Fin (n + 2) → data.cusp.H)
  (correction_smooth : ∀ position, correction position ∈ data.cusp.smooth)
  (correction_spherical : ∀ position, correction position ∈ cuspSphericalValues data.cusp)
  (reconstruction : ∀ A : BinaryRealGL,
    binaryHilbertEmbedding data.cusp (binaryWeightBasis (n + 1))
        (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular A) =
      (2 : ℂ)⁻¹ • (binaryEndpointPeriod data.cusp n halfWeight vector.val
        ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
          (binaryEndpointPeriod data.cusp n halfWeight vector.val
            (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
      (binaryHilbertOperator data.cusp (binaryWeightBasis (n + 1)) A correction - correction))

include spherical hF correction_smooth correction_spherical reconstruction in
/-- **The radical identity, tested.** On a radical pair, a scalar test of `δβ` is the scalar test
of the averaged transfer `T` at the real radical elements `3 r₁, 3 r₂` at the identity. -/
theorem functional_radical_averagedTransfer (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
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
    (lineRelative : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n))
    (lineFormula : ∀ first second : flagArithmeticStabilizer .line
        (QuotientGroup.mk rationalGoodLine),
      lineRelative.val (first, second) = (id (goodLineComplementFamily standard
          cohomologicalPoint (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (![1, first.val, first.val * second.val] index))) : goodLineCoefficientRep n) -
        ((goodLineCoefficientRep n).ρ first (linePrimitive second) -
          linePrimitive (first * second) + linePrimitive first))
    (primitive_analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis
            (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (twoBoundaryCycle (goodLineCoefficientRep n)
        (linePrimitive - prismStabilizerCochain data source cocycle -
          edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative
            regular))
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      averagedTransfer n (cuspScalarWeightedRealization data.cusp halfWeight vector)
        (hilbertLift data.cusp n correction) (latticePoint r₁) (latticePoint r₂)
        (1, functional) := by
  have vanish : lineRelative.val (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) = 0 :=
    lineRelative.property r₁ r₂
  rw [lineFormula] at vanish
  have line : twoBoundaryCycle (goodLineCoefficientRep n) linePrimitive
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
      goodLineRealGroupCochain n (goodLineComplementFamily standard cohomologicalPoint)
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) := by
    rw [twoBoundaryCycle_apply]
    exact (sub_eq_zero.mp vanish).symm
  have decomposition := radicalPair_complement_decomposition_of_analytic large local_entry data
    trivial basis source cocycle flat standard sections endpoint support continuations analytic
    primitive primitive_analytic relative formula regular r₁ r₂ functional
  have binaryRegular := canonicalBinaryValues_regular_of_reconstruction data trivial basis
    relative regular halfWeight vector spherical correction correction_smooth reconstruction
  have average := integral_radicalCanonicalAverage (by omega) data trivial basis relative regular
    binaryRegular r₁ r₂ functional
  have split := (finiteAverageLine_original data.cusp (continuousStages data) halfWeight vector
    spherical hF (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular)
    correction correction_smooth correction_spherical reconstruction (by omega) (latticePoint r₁)
    (latticePoint r₂) functional).2
  set test := functional.comp (goodLineCoefficientPolynomial n)
  have difference : functional (twoBoundaryCycle (goodLineCoefficientRep n)
      (linePrimitive - prismStabilizerCochain data source cocycle -
        edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative
          regular))
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      test (twoBoundaryCycle (goodLineCoefficientRep n) linePrimitive
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) -
        test (twoBoundaryCycle (goodLineCoefficientRep n) (prismStabilizerCochain data source
          cocycle) (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) -
        test (twoBoundaryCycle (goodLineCoefficientRep n) (edgeStabilizerCochain data
          (totalPrimitiveEdge data trivial basis primitive relative regular))
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
    change test _ = _
    rw [twoBoundaryCycle_sub_apply, twoBoundaryCycle_sub_apply, map_sub, map_sub]
  have sum : functional (twoBoundaryCycle (goodLineCoefficientRep n)
      (prismStabilizerCochain data source cocycle + edgeStabilizerCochain data
        (totalPrimitiveEdge data trivial basis primitive relative regular))
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      test (twoBoundaryCycle (goodLineCoefficientRep n) (prismStabilizerCochain data source
          cocycle) (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) +
        test (twoBoundaryCycle (goodLineCoefficientRep n) (edgeStabilizerCochain data
          (totalPrimitiveEdge data trivial basis primitive relative regular))
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
    change test _ = _
    rw [twoBoundaryCycle_add_apply, map_add]
  have lineTest : test (twoBoundaryCycle (goodLineCoefficientRep n) linePrimitive
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      functional (goodLineRealGroupCochain n (goodLineComplementFamily standard cohomologicalPoint)
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
    rw [line]
    rfl
  rw [difference, lineTest, decomposition, sum, average]
  change finiteAverageLine (lineTransferCochain (fun A =>
    (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular A).val)
      (latticePoint r₁) (latticePoint r₂)) functional + _ - _ - _ = _
  rw [split]
  ring

include spherical hF correction_smooth correction_spherical reconstruction in
/-- **The radical identity.** On a radical pair, `δβ` is the vector of the averaged transfer `T`
at the real radical elements `3 r₁, 3 r₂` at the identity. -/
theorem radical_averagedTransfer (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
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
    (lineRelative : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n))
    (lineFormula : ∀ first second : flagArithmeticStabilizer .line
        (QuotientGroup.mk rationalGoodLine),
      lineRelative.val (first, second) = (id (goodLineComplementFamily standard
          cohomologicalPoint (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (![1, first.val, first.val * second.val] index))) : goodLineCoefficientRep n) -
        ((goodLineCoefficientRep n).ρ first (linePrimitive second) -
          linePrimitive (first * second) + linePrimitive first))
    (primitive_analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ
      (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
        binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
          (cuspidalTensorHilbertEmbedding data.cusp basis
            (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (r₁ r₂ : RadicalLattice) :
    twoBoundaryCycle (goodLineCoefficientRep n)
        (linePrimitive - prismStabilizerCochain data source cocycle -
          edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative
            regular))
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
      lineVector (averagedTransfer n (cuspScalarWeightedRealization data.cusp halfWeight vector)
        (hilbertLift data.cusp n correction) (latticePoint r₁) (latticePoint r₂)) 1 := by
  refine (homogeneousBasis n).ext_elem fun j => ?_
  have value := functional_radical_averagedTransfer data trivial basis source cocycle
    linePrimitive primitive relative regular halfWeight vector spherical hF correction
    correction_smooth correction_spherical reconstruction large local_entry flat standard sections
    endpoint support continuations analytic lineRelative lineFormula primitive_analytic formula r₁
    r₂ ((homogeneousBasis n).coord j)
  rw [← coord_lineVector (averagedTransfer n
    (cuspScalarWeightedRealization data.cusp halfWeight vector) (hilbertLift data.cusp n correction)
    (latticePoint r₁) (latticePoint r₂)) 1 j] at value
  exact value

include spherical hF correction_smooth correction_spherical reconstruction in
/-- **The mixed identity, tested.** A scalar test of the mixed coordinate of `δβ` at `γ` is the
sum over the two radical generators of the mixed radical edges of the averaged transfer `T` at
the identity, tested through the lower radical lattice contributions. -/
theorem functional_mixed_averagedTransfer (large : 9 ≤ n)
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
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    functional (goodLineMixedCoordinate n γ (fun pair =>
        twoBoundaryCycle (goodLineCoefficientRep n)
          (linePrimitive - prismStabilizerCochain data source cocycle -
            edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative
              regular)) pair)) =
      ∑ i : Fin 2, radicalEdge (averagedTransfer n
          (cuspScalarWeightedRealization data.cusp halfWeight vector)
          (hilbertLift data.cusp n correction)) (integralLevi γ)
        (latticeVector (![radicalLatticeFirst, radicalLatticeSecond] i))
        (1, functional.comp (lowerRadicalLatticeContribution n i)) := by
  have binaryRegular := canonicalBinaryValues_regular_of_reconstruction data trivial basis
    relative regular halfWeight vector spherical correction correction_smooth reconstruction
  rw [goodLineMixedCoordinate_twoBoundary_sub, map_sub, ← projected γ functional,
    canonical γ functional, add_sub_cancel_right,
    integral_canonicalProjectedAverage_sum (by omega) data trivial basis relative regular
      binaryRegular γ functional]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact finiteAverageLine_radicalEdge_original data.cusp (continuousStages data) halfWeight vector
    spherical hF (realPlaneLevelBinaryCocycle n data.cusp data.chi trivial basis relative regular)
    correction correction_smooth correction_spherical reconstruction (by omega) (integralLevi γ)
    _ _

include spherical hF correction_smooth correction_spherical reconstruction in
/-- **The mixed identity.** The mixed coordinate of `δβ` at `γ` is the lattice coordinate of the
vectors at the identity of the mixed radical edges of the averaged transfer `T` along the real
radical elements `3 r`. -/
theorem mixed_averagedTransfer (large : 9 ≤ n)
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
    (γ : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedCoordinate n γ (fun pair =>
        twoBoundaryCycle (goodLineCoefficientRep n)
          (linePrimitive - prismStabilizerCochain data source cocycle -
            edgeStabilizerCochain data (totalPrimitiveEdge data trivial basis primitive relative
              regular)) pair) =
      latticeCoordinate n (fun r => lineVector (radicalEdge (averagedTransfer n
          (cuspScalarWeightedRealization data.cusp halfWeight vector)
          (hilbertLift data.cusp n correction)) (integralLevi γ) (latticeVector r)) 1) := by
  refine (binaryWeightBasis (n + 1)).ext_elem fun j => ?_
  have value := functional_mixed_averagedTransfer data trivial basis source cocycle linePrimitive
    primitive relative regular halfWeight vector spherical hF correction correction_smooth
    correction_spherical reconstruction large projected canonical γ
    ((binaryWeightBasis (n + 1)).coord j)
  have lattice := functional_latticeCoordinate_lineVector (fun r => radicalEdge (averagedTransfer n
      (cuspScalarWeightedRealization data.cusp halfWeight vector)
      (hilbertLift data.cusp n correction)) (integralLevi γ) (latticeVector r))
    (fun r => linearAt_radicalEdge_averagedTransfer data.cusp halfWeight vector spherical hF
      correction correction_smooth correction_spherical (by omega) (integralLevi γ)
      (latticeVector r)) ((binaryWeightBasis (n + 1)).coord j)
  exact value.trans lattice.symm

end Glue

end TernaryPeriodPolynomials.AnalyticClasses
