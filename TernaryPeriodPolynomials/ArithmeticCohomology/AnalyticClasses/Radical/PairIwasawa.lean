module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Radical.PairLiteral
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.CanonicalReduction

@[expose] public section


/-!
# The Iwasawa prism transfer on one radical simplex

For a radical simplex `(1, r₁, r₁ r₂)` of the good-line stabilizer, the source cusp values at
`g(u)` split, through the Gram–Schmidt vertex map, into the source on the projected
(plane-parabolic) simplex and three prism edges. All three edge averages are absolutely
integrable at `s = -3/2`, and by radical equivariance their integrals combine into the scalar test
of the two-coboundary of the integrated prism cochain at the radical pair. Hence

`∫ FinAvg(source on (1, r₁, r₁ r₂) at g(u)) = ∫ FinAvg(projected part) + ℓ(δ f (r₁, r₂))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

/-- The real vertices `(1, r₁, r₁ r₂)` of a radical simplex. -/
def radicalVertices (r₁ r₂ : RadicalLattice) : Fin 3 → RealGL3 :=
  ![1, edgeRadical r₁, edgeRadical r₁ * edgeRadical r₂]

theorem edgeRadical_mul (r₁ r₂ : RadicalLattice) :
    edgeRadical (r₁ * r₂) = edgeRadical r₁ * edgeRadical r₂ := by
  simp only [edgeRadical, map_mul]

theorem goodLineRealVertices_radical (r₁ r₂ : RadicalLattice) :
    goodLineRealVertices (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂) =
      radicalVertices r₁ r₂ := by
  funext index
  fin_cases index
  · simp [goodLineRealVertices, radicalVertices]
  · rfl
  · change GeneralLinearGroup.map (algebraMap ℚ ℝ)
      ((goodLineRadicalInclusion r₁).val * (goodLineRadicalInclusion r₂).val) = _
    rw [map_mul]
    rfl

theorem edgeRadicalPair_eq (r₁ r₂ : RadicalLattice) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (goodLineRadicalInclusion r₁ * goodLineRadicalInclusion r₂).val =
      edgeRadical r₁ * edgeRadical r₂ := by
  rw [Subgroup.coe_mul, map_mul]
  rfl

theorem corner_radical_pair (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) :
    (standardGoodLineRealArgument u * (edgeRadical r₁ * edgeRadical r₂)).val 2 2 ≠ 0 := by
  rw [← mul_assoc, standardGoodLineRealArgument_radical]
  exact corner_radical _ r₂

/-- The projected part of a radical simplex: the source on its Gram–Schmidt simplex,
transported back by the real good-line argument. -/
def radicalProjectedTerm (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) :
    cuspidalTensorValues data.cusp (HomogeneousPoly n) :=
  cuspidalTensorMap data.cusp
    (realCoefficientComponent n data.chi (standardGoodLineRealArgument u)⁻¹)
    (sourcePlaneCuspidalValues data source cocycle
      (fun index => gsVertex (standardGoodLineRealArgument u * radicalVertices r₁ r₂ index)) 1)

theorem radicalProjectedTerm_finiteLevel (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (r₁ r₂ : RadicalLattice) :
    radicalProjectedTerm data source cocycle u r₁ r₂ ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) := by
  have hone : atInfinity (1 : RealGL3) = 1 := AveragingSmooth.atInfinity_one
  have member := sourcePlaneCuspidalValues_finiteLevel data source cocycle
    (fun index => gsVertex (standardGoodLineRealArgument u * radicalVertices r₁ r₂ index)) 1
  rw [hone] at member
  exact cuspidalTensorMap_finiteLevel _ _ _ member

/-- **Pointwise Iwasawa prism decomposition of a radical simplex.** -/
theorem sourcePlaneCuspidalValues_radical_iwasawa (data : InducingData n)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ)
    (r₁ r₂ : RadicalLattice) :
    sourcePlaneCuspidalValues data source cocycle (radicalVertices r₁ r₂)
        (atInfinity (standardGoodLineRealArgument u)) =
      radicalProjectedTerm data source cocycle u r₁ r₂ +
        (goodLineIwasawaPrism data source cocycle u
            ![edgeRadical r₁, edgeRadical r₁ * edgeRadical r₂] -
          goodLineIwasawaPrism data source cocycle u ![1, edgeRadical r₁ * edgeRadical r₂] +
          goodLineIwasawaPrism data source cocycle u ![1, edgeRadical r₁]) := by
  have differential := sourceCuspidalVertexPrism_differential data source cocycle
    gsVertex (standardGoodLineRealArgument u) 1 (radicalVertices r₁ r₂)
  rw [sourceCuspidalRealTranslate_atInfinity] at differential
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  rw [← sub_eq_iff_eq_add', radicalProjectedTerm]
  exact differential

/-- **Pointwise decomposition of the finite average of a radical simplex.** -/
theorem simplexFiniteFamily_radical_decomposition (large : 3 < n) (data : InducingData n)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (r₁ r₂ : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) :
    simplexFiniteFamily data source cocycle (radicalVertices r₁ r₂) functional
        cohomologicalPoint u =
      tensorAverage data functional (radicalProjectedTerm data source cocycle u r₁ r₂) +
        (prismEdgeAverage data source cocycle functional (edgeRadical r₁)
            (edgeRadical r₁ * edgeRadical r₂) u -
          prismEdgeAverage data source cocycle functional 1 (edgeRadical r₁ * edgeRadical r₂) u +
          prismEdgeAverage data source cocycle functional 1 (edgeRadical r₁) u) := by
  have P (edge : Fin 2 → RealGL3) := goodLineIwasawaPrism_finiteLevel data source cocycle u edge
  have C := radicalProjectedTerm_finiteLevel data source cocycle u r₁ r₂
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  change tensorAverage data functional (sourcePlaneCuspidalValues data source cocycle
    (radicalVertices r₁ r₂) (atInfinity (standardGoodLineRealArgument u))) = _
  rw [sourcePlaneCuspidalValues_radical_iwasawa,
    tensorAverage_add large data functional _ _ C
      (Submodule.add_mem _ (Submodule.sub_mem _ (P _) (P _)) (P _)),
    tensorAverage_add large data functional _ _ (Submodule.sub_mem _ (P _) (P _)) (P _),
    tensorAverage_sub large data functional _ _ (P _) (P _)]
  rfl

/-- **Integrability of the finite average of one simplex at the cohomological point.** -/
theorem simplexFiniteFamily_endpoint_integrable (large : 5 ≤ n) (data : InducingData n)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (V : Fin 3 → RealGL3) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (simplexFiniteFamily data source cocycle V functional cohomologicalPoint)
      ((volume : Measure ℝ).prod volume) := by
  have three : 3 < n := by omega
  have convergent : 3 < (finiteExponent n cohomologicalPoint).re := by
    rw [finiteExponent_re]
    have : (3 : ℝ) < n := by exact_mod_cast three
    norm_num [cohomologicalPoint]
    linarith
  have continuity : Continuous
      (simplexFiniteFamily data source cocycle V functional cohomologicalPoint) :=
    finiteAverage_continuous three data.cusp (simplexTestVector data source cocycle V functional)
      (simplexTestVector_spherical data source cocycle V functional)
      (sourceValues_boundedRealization_continuous data source cocycle functional V)
  obtain ⟨C, hC0, hC⟩ := simplexTestVector_decay data source cocycle V functional
  have dominating : Integrable (fun u => weightMass (finiteExponent n cohomologicalPoint).re *
      (kernelBase u ^ (-(((n : ℝ) + 3) / 4)) * C)) ((volume : Measure ℝ).prod volume) :=
    ((kernelBase_decay_integrable large).mul_const C).const_mul _
  refine dominating.mono' continuity.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  exact norm_goodLineFiniteVectorIntegral_le data.cusp cohomologicalPoint convergent _
    (simplexTestVector_spherical data source cocycle V functional u) _ (hC u)

/-- The finite average of the projected part of a radical simplex. -/
abbrev radicalProjectedAverage (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r₁ r₂ : RadicalLattice) (u : ℝ × ℝ) : ℂ :=
  tensorAverage data functional (radicalProjectedTerm data source cocycle u r₁ r₂)

/-- The scalar test of the two-coboundary of the integrated prism cochain at a radical pair. -/
theorem functional_prism_twoBoundary_radical (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r₁ r₂ : RadicalLattice) :
    (functional.comp (goodLineCoefficientPolynomial n)) (twoBoundaryCycle (goodLineCoefficientRep n)
        (prismStabilizerCochain data source cocycle)
        (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) =
      prismEdgeIntegral data source cocycle functional (edgeRadical r₁)
          (edgeRadical r₁ * edgeRadical r₂) -
        prismEdgeIntegral data source cocycle functional 1 (edgeRadical r₁ * edgeRadical r₂) +
        prismEdgeIntegral data source cocycle functional 1 (edgeRadical r₁) := by
  have three : 3 < n := by omega
  have dual (y : RealGL3) (corner : ∀ u, (standardGoodLineRealArgument u * y).val 2 2 ≠ 0)
      (ℓ : HomogeneousPoly n →ₗ[ℂ] ℂ) :
      ℓ (prismDualVector data source cocycle y) = prismEdgeIntegral data source cocycle ℓ 1 y :=
    functional_prismDualVector three data source cocycle y
      (fun ℓ' => prismEdgeAverage_one_integrable large data trivial source cocycle ℓ' y corner) ℓ
  have radicalEdge : prismEdgeIntegral data source cocycle functional (edgeRadical r₁)
      (edgeRadical r₁ * edgeRadical r₂) =
      prismEdgeIntegral data source cocycle
        (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁))) 1
        (edgeRadical r₂) := by
    have := prismEdgeIntegral_radical data source cocycle functional r₁ 1 (edgeRadical r₂)
    rwa [mul_one] at this
  have termρ (v : goodLineCoefficientRep n) :
      (functional.comp (goodLineCoefficientPolynomial n))
          ((goodLineCoefficientRep n).ρ (goodLineRadicalInclusion r₁) v) =
        (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁))) v := by
    rw [trivial]; rfl
  rw [twoBoundaryCycle_apply, map_add, map_sub, termρ]
  change (functional.comp (realCoefficientComponent n data.chi (edgeRadical r₁)))
      (prismDualVector data source cocycle (edgeRadical r₂)) -
    functional (prismDualVector data source cocycle (GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (goodLineRadicalInclusion r₁ * goodLineRadicalInclusion r₂).val)) +
    functional (prismDualVector data source cocycle (edgeRadical r₁)) = _
  rw [edgeRadicalPair_eq, radicalEdge, dual _ (fun u => corner_radical u r₂),
    dual _ (fun u => corner_radical_pair u r₁ r₂), dual _ (fun u => corner_radical u r₁)]

/-- **Iwasawa reduction of a radical simplex.** At `s = -3/2` the integral of the finite average
of the source on the radical simplex `(1, r₁, r₁ r₂)` moved by `g(u)` is the integral of the
finite average of the projected part plus the scalar test of the two-coboundary of the integrated
prism cochain at the radical pair. -/
theorem integral_simplexFiniteFamily_radical_iwasawa (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (r₁ r₂ : RadicalLattice)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    Integrable (radicalProjectedAverage data source cocycle functional r₁ r₂)
        ((volume : Measure ℝ).prod volume) ∧
      ∫ u, simplexFiniteFamily data source cocycle (radicalVertices r₁ r₂) functional
          cohomologicalPoint u ∂((volume : Measure ℝ).prod volume) =
        ∫ u, radicalProjectedAverage data source cocycle functional r₁ r₂ u
            ∂((volume : Measure ℝ).prod volume) +
          (functional.comp (goodLineCoefficientPolynomial n))
            (twoBoundaryCycle (goodLineCoefficientRep n)
              (prismStabilizerCochain data source cocycle)
              (goodLineRadicalInclusion r₁, goodLineRadicalInclusion r₂)) := by
  have three : 3 < n := by omega
  have hdec := simplexFiniteFamily_radical_decomposition three data source cocycle r₁ r₂
    functional
  have iS := simplexFiniteFamily_endpoint_integrable large data source cocycle
    (radicalVertices r₁ r₂) functional
  have i1 := prismEdgeAverage_radical_integrable large data trivial source cocycle functional r₁
    (edgeRadical r₁ * edgeRadical r₂) (fun u => corner_radical_pair u r₁ r₂)
  have i2 := prismEdgeAverage_one_integrable large data trivial source cocycle functional
    (edgeRadical r₁ * edgeRadical r₂) (fun u => corner_radical_pair u r₁ r₂)
  have i3 := prismEdgeAverage_one_integrable large data trivial source cocycle functional
    (edgeRadical r₁) (fun u => corner_radical u r₁)
  have iP : Integrable (radicalProjectedAverage data source cocycle functional r₁ r₂)
      ((volume : Measure ℝ).prod volume) := by
    refine (iS.sub ((i1.sub i2).add i3)).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply, Pi.add_apply, hdec u]
    ring
  refine ⟨iP, ?_⟩
  have split : (fun u => simplexFiniteFamily data source cocycle (radicalVertices r₁ r₂)
      functional cohomologicalPoint u) = fun u =>
      radicalProjectedAverage data source cocycle functional r₁ r₂ u +
        ((prismEdgeAverage data source cocycle functional (edgeRadical r₁)
            (edgeRadical r₁ * edgeRadical r₂) u -
          prismEdgeAverage data source cocycle functional 1 (edgeRadical r₁ * edgeRadical r₂) u) +
          prismEdgeAverage data source cocycle functional 1 (edgeRadical r₁) u) := funext hdec
  have h1 := integral_add iP ((i1.sub i2).add i3)
  have h2 := integral_add (i1.sub i2) i3
  have h3 := integral_sub i1 i2
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [split, h1, h2, h3, functional_prism_twoBoundary_radical large data trivial source cocycle]
  rfl

end TernaryPeriodPolynomials.AnalyticClasses
