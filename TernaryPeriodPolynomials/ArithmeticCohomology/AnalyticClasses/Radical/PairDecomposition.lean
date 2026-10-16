module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PairIwasawa
public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.TotalPrimitiveEdgeIntegrable

@[expose] public section


/-!
# The radical-pair decomposition of the good-line target

The radical analogue of the mixed-coordinate chain `mixedReal_endpoint_eq_integral`,
`integral_mixedFiniteFamily_iwasawa` and `integral_projectedAverage_canonical`. For one radical
simplex `(1, r₁, r₁ r₂)` of the good-line stabilizer, every vertex moved by the good-line
argument `g(u)` is of the form `planeLevi B 1 · g(w)` with `|det B| = 1`, so Codexiom's real-plane
chain for the determinant-normalized source splits the projected part into the canonical binary
relative cocycle on the real-plane points of the Gram–Schmidt simplex and three transported edges
of the explicit total primitive. By radical equivariance the integrated edges are the scalar test
of the two-coboundary of the edge stabilizer cochain at the radical pair. Together with the
literal integral at `s = -3/2` and the Iwasawa prism transfer, the value of the complementary
good-line family at the radical pair is

`∫ FinAvg(canonical term) + ℓ(δ(prism cochain + edge cochain)(r₁, r₂))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {index : Type} [Fintype index]

/-- The canonical term of a radical simplex: the canonical binary relative cocycle on the
real-plane points of the Gram–Schmidt simplex of `g(u) · (1, r₁, r₁ r₂)`, transported back by the
real good-line argument. -/
def radicalCanonicalTerm (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) : cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap data.cusp
    (realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹)
    (canonicalSimplexValue data trivial basis relative regular
      (fun i => gsPlaneVertex (standardGoodLineRealArgument u *
        ![1, edgeRadical r₁, edgeRadical r₁ * edgeRadical r₂] i)))

theorem radicalCanonicalTerm_finiteLevel (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) :
    radicalCanonicalTerm data trivial basis relative regular u r₁ r₂ ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap_finiteLevel _ _ _
    (realPlaneCuspidalRep_finiteLevel n data.cusp data.chi _ _
      (realPlaneLevelBinaryRelativeCycle_finiteLevel n data.cusp data.chi trivial basis relative
        regular _))

theorem goodLineForm_radicalVertices (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) (i : Fin 3) :
    GoodLineForm (standardGoodLineRealArgument u * radicalVertices r₁ r₂ i) := by
  fin_cases i
  · exact goodLineForm_one u
  · exact goodLineForm_radical u r₁
  · change GoodLineForm (standardGoodLineRealArgument u * (edgeRadical r₁ * edgeRadical r₂))
    rw [← edgeRadical_mul]
    exact goodLineForm_radical u (r₁ * r₂)

/-- **The projected part of a radical simplex: canonical term plus three transported edges.** -/
theorem radicalProjectedTerm_split (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) :
    radicalProjectedTerm data source cocycle u r₁ r₂ =
      radicalCanonicalTerm data trivial basis relative regular u r₁ r₂ +
        (edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            (edgeRadical r₁) (edgeRadical r₁ * edgeRadical r₂) -
          edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            1 (edgeRadical r₁ * edgeRadical r₂) +
          edgeTransported data (totalPrimitiveEdge data trivial basis primitive relative regular) u
            1 (edgeRadical r₁)) := by
  have split := source_gsSimplex_split data trivial basis source cocycle primitive relative
    formula regular _ (goodLineForm_radicalVertices u r₁ r₂)
  unfold radicalProjectedTerm radicalCanonicalTerm
  rw [split]
  apply Subtype.ext
  funext A
  simp only [Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply,
    cuspidalTensorMap_val_apply, edgeTransported, map_add, map_sub]
  rfl

/-- One radical projected average splits into the canonical average and three edge averages. -/
theorem radicalProjectedAverage_split (large : 3 < n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (r₁ r₂ : RadicalLattice) (u : ℝ × ℝ) :
    radicalProjectedAverage data source cocycle functional r₁ r₂ u =
      tensorAverage data functional
          (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂) +
        (edgeAverage data (totalPrimitiveEdge data trivial basis primitive relative regular)
            functional (edgeRadical r₁) (edgeRadical r₁ * edgeRadical r₂) u -
          edgeAverage data (totalPrimitiveEdge data trivial basis primitive relative regular)
            functional 1 (edgeRadical r₁ * edgeRadical r₂) u +
          edgeAverage data (totalPrimitiveEdge data trivial basis primitive relative regular)
            functional 1 (edgeRadical r₁) u) := by
  set E := totalPrimitiveEdge data trivial basis primitive relative regular
  have finite := totalPrimitiveEdge_finite data trivial basis primitive relative regular
  have T (x y : RealGL3) := edgeTransported_finiteLevel data E finite u x y
  have C := radicalCanonicalTerm_finiteLevel data trivial basis relative regular u r₁ r₂
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  change tensorAverage data functional (radicalProjectedTerm data source cocycle u r₁ r₂) = _
  rw [radicalProjectedTerm_split data trivial basis source cocycle primitive relative formula
      regular u r₁ r₂,
    tensorAverage_add large data functional _ _ C
      (Submodule.add_mem _ (Submodule.sub_mem _ (T _ _) (T _ _)) (T _ _)),
    tensorAverage_add large data functional _ _ (Submodule.sub_mem _ (T _ _) (T _ _)) (T _ _),
    tensorAverage_sub large data functional _ _ (T _ _) (T _ _)]
  rfl

/-- Integrability of the three transported edges of a radical simplex. -/
theorem radicalEdges_integrable (data : InducingData n) (E : EdgeCochain data)
    (integrable : EdgeIntegrable data E) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r₁ r₂ : RadicalLattice) :
    Integrable (edgeAverage data E functional (edgeRadical r₁) (edgeRadical r₁ * edgeRadical r₂))
        ((volume : Measure ℝ).prod volume) ∧
      Integrable (edgeAverage data E functional 1 (edgeRadical r₁ * edgeRadical r₂))
        ((volume : Measure ℝ).prod volume) ∧
      Integrable (edgeAverage data E functional 1 (edgeRadical r₁))
        ((volume : Measure ℝ).prod volume) := by
  refine ⟨?_, ?_, (integrable functional 1 r₁).2.2.2⟩
  · have shifted := (radicalShift_measurePreserving r₁).integrable_comp_of_integrable
      (integrable (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁))) 1
        r₂).2.2.2
    refine shifted.congr (Filter.Eventually.of_forall fun u => ?_)
    have := edgeAverage_radical data E functional r₁ 1 (edgeRadical r₂) u
    rw [mul_one] at this
    exact this.symm
  · rw [← edgeRadical_mul]
    exact (integrable functional 1 (r₁ * r₂)).2.2.2

/-- The scalar test of the two-coboundary of an edge stabilizer cochain at a radical pair. -/
theorem functional_edge_twoBoundary_radical (large : 3 < n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (E : EdgeCochain data) (finite : EdgeFinite data E)
    (integrable : EdgeIntegrable data E) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r₁ r₂ : RadicalLattice) :
    (functional.comp (goodLineCoefficientPolynomial n))
        (twoBoundaryCycle (goodLineCoefficientRep n) (edgeStabilizerCochain data E)
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      edgeIntegral data E functional (edgeRadical r₁) (edgeRadical r₁ * edgeRadical r₂) -
        edgeIntegral data E functional 1 (edgeRadical r₁ * edgeRadical r₂) +
        edgeIntegral data E functional 1 (edgeRadical r₁) := by
  have dual (r : RadicalLattice) (ℓ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ (edgeDualVector data E (edgeRadical r)) = edgeIntegral data E ℓ 1 (edgeRadical r) :=
    functional_edgeDualVector large data E finite (edgeRadical r)
      (fun ℓ' => (integrable ℓ' 1 r).2.2.2) ℓ
  have radicalEdge : edgeIntegral data E functional (edgeRadical r₁)
      (edgeRadical r₁ * edgeRadical r₂) =
      edgeIntegral data E (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁)))
        1 (edgeRadical r₂) := by
    have := edgeIntegral_radical data E functional r₁ 1 (edgeRadical r₂)
    rwa [mul_one] at this
  have termρ (v : goodLineCoefficientRep n) :
      (functional.comp (goodLineCoefficientPolynomial n))
          ((goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁) v) =
        (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁))) v := by
    rw [trivial]; rfl
  rw [twoBoundaryCycle_apply, map_add, map_sub, termρ]
  change (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁)))
      (edgeDualVector data E (edgeRadical r₂)) -
    functional (edgeDualVector data E (GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (goodLineRadicalInclusion r₁ * goodLineRadicalInclusion r₂).val)) +
    functional (edgeDualVector data E (edgeRadical r₁)) = _
  rw [edgeRadicalPair_eq, ← edgeRadical_mul, dual, dual, dual, ← radicalEdge, edgeRadical_mul]

/-- **The projected integral of a radical simplex is the canonical one plus a coboundary.**
Also exports the integrability of the canonical average. -/
theorem integral_radicalProjectedAverage_canonical (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (edgeIntegrable : EdgeIntegrable data
      (totalPrimitiveEdge data trivial basis primitive relative regular))
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => tensorAverage data functional
        (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂))
        ((volume : Measure ℝ).prod volume) ∧
      ∫ u, radicalProjectedAverage data source cocycle functional r₁ r₂ u
          ∂((volume : Measure ℝ).prod volume) =
        ∫ u, tensorAverage data functional
            (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂)
            ∂((volume : Measure ℝ).prod volume) +
          (functional.comp (goodLineCoefficientPolynomial n))
            (twoBoundaryCycle (goodLineCoefficientRep n)
              (edgeStabilizerCochain data
                (totalPrimitiveEdge data trivial basis primitive relative regular))
              (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
  have three : 3 < n := by omega
  set E := totalPrimitiveEdge data trivial basis primitive relative regular with hE
  have hsplit := radicalProjectedAverage_split three data trivial basis source cocycle primitive
    relative formula regular functional r₁ r₂
  have iP := (integral_simplexFiniteFamily_radical_iwasawa large data trivial source cocycle r₁ r₂
    functional).1
  obtain ⟨i1, i2, i3⟩ := radicalEdges_integrable data E edgeIntegrable functional r₁ r₂
  have iC : Integrable (fun u => tensorAverage data functional
      (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂))
      ((volume : Measure ℝ).prod volume) := by
    refine (iP.sub ((i1.sub i2).add i3)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, hsplit u]
    ring
  refine ⟨iC, ?_⟩
  have total : (fun u => radicalProjectedAverage data source cocycle functional r₁ r₂ u) =
      fun u => tensorAverage data functional
          (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂) +
        ((edgeAverage data E functional (edgeRadical r₁) (edgeRadical r₁ * edgeRadical r₂) u -
          edgeAverage data E functional 1 (edgeRadical r₁ * edgeRadical r₂) u) +
          edgeAverage data E functional 1 (edgeRadical r₁) u) := funext hsplit
  have h1 := integral_add iC ((i1.sub i2).add i3)
  have h2 := integral_add (i1.sub i2) i3
  have h3 := integral_sub i1 i2
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [total, h1, h2, h3, functional_edge_twoBoundary_radical three data trivial E
    (totalPrimitiveEdge_finite data trivial basis primitive relative regular) edgeIntegrable]
  rfl

/-- Integrability of the finite average of the canonical term of a radical simplex. -/
theorem radicalCanonicalAverage_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (edgeIntegrable : EdgeIntegrable data
      (totalPrimitiveEdge data trivial basis primitive relative regular))
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (fun u => tensorAverage data functional
        (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂))
      ((volume : Measure ℝ).prod volume) :=
  (integral_radicalProjectedAverage_canonical large data trivial basis source cocycle primitive
    relative formula regular edgeIntegrable r₁ r₂ functional).1

theorem twoBoundaryCycle_add_apply {E : Type} [Group E] (representation : Rep ℂ E)
    (first second : E → representation) (pair : E × E) :
    twoBoundaryCycle representation (first + second) pair =
      twoBoundaryCycle representation first pair + twoBoundaryCycle representation second pair := by
  obtain ⟨g, h⟩ := pair
  rw [twoBoundaryCycle_apply, twoBoundaryCycle_apply, twoBoundaryCycle_apply, Pi.add_apply,
    Pi.add_apply, Pi.add_apply, map_add]
  abel

/-- **The radical-pair decomposition of the complementary good-line family.** At the cohomological
point, a scalar test of the complementary good-line family on the radical simplex
`(1, r₁, r₁ r₂)` is the absolutely convergent integral of the finite average of the canonical term
plus the scalar test of the two-coboundary, at the radical pair, of the sum of the integrated
Iwasawa prism cochain and the edge stabilizer cochain of the explicit total primitive. -/
theorem radicalPair_complement_decomposition (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
    (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
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
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (edgeIntegrable : EdgeIntegrable data
      (totalPrimitiveEdge data trivial basis primitive relative regular))
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (goodLineRealGroupCochain n (goodLineComplementFamily standard cohomologicalPoint)
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      ∫ u, tensorAverage data functional
          (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂)
          ∂((volume : Measure ℝ).prod volume) +
        functional (twoBoundaryCycle (goodLineCoefficientRep n)
          (prismStabilizerCochain data source cocycle +
            edgeStabilizerCochain data
              (totalPrimitiveEdge data trivial basis primitive relative regular))
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
  have five : 5 ≤ n := by omega
  have literal : functional (goodLineComplementFamily standard cohomologicalPoint
      (radicalVertices r₁ r₂)) = ∫ u, simplexFiniteFamily data source cocycle
        (radicalVertices r₁ r₂) functional cohomologicalPoint u
        ∂((volume : Measure ℝ).prod volume) :=
    simplex_endpoint_eq_integral large local_entry data trivial source cocycle flat
      standard sections endpoint support continuations analytic (radicalVertices r₁ r₂) functional
  have iwasawa := (integral_simplexFiniteFamily_radical_iwasawa five data trivial source cocycle
    r₁ r₂ functional).2
  have canonical := (integral_radicalProjectedAverage_canonical five data trivial basis source
    cocycle primitive relative formula regular edgeIntegrable r₁ r₂ functional).2
  change functional (goodLineComplementFamily standard cohomologicalPoint
      (goodLineRealVertices (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂))) =
    _ + (functional.comp (goodLineCoefficientPolynomial n)) (twoBoundaryCycle
      (goodLineCoefficientRep n) (prismStabilizerCochain data source cocycle +
        edgeStabilizerCochain data
          (totalPrimitiveEdge data trivial basis primitive relative regular))
      (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂))
  rw [goodLineRealVertices_radical, literal, iwasawa, canonical, twoBoundaryCycle_add_apply,
    map_add]
  ring

/-- **The radical-pair decomposition, with the edge integrability discharged.** The same identity
as `radicalPair_complement_decomposition`, with `EdgeIntegrable` supplied by
`totalPrimitiveEdge_edgeIntegrable` from the analyticity of Codexiom's radical primitive. -/
theorem radicalPair_complement_decomposition_of_analytic (large : 9 ≤ n)
    (local_entry : LocalBadPlaneEntry)
    (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
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
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (goodLineRealGroupCochain n (goodLineComplementFamily standard cohomologicalPoint)
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      ∫ u, tensorAverage data functional
          (radicalCanonicalTerm data trivial basis relative regular u r₁ r₂)
          ∂((volume : Measure ℝ).prod volume) +
        functional (twoBoundaryCycle (goodLineCoefficientRep n)
          (prismStabilizerCochain data source cocycle +
            edgeStabilizerCochain data
              (totalPrimitiveEdge data trivial basis primitive relative regular))
          (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) :=
  radicalPair_complement_decomposition large local_entry data trivial basis source cocycle flat
    standard sections endpoint support continuations analytic primitive relative formula regular
    (TernaryPeriodPolynomials.EdgeControl.totalPrimitiveEdge_edgeIntegrable (by omega)
      data trivial basis source cocycle primitive primitive_analytic relative formula regular)
    r₁ r₂ functional

end TernaryPeriodPolynomials.AnalyticClasses
