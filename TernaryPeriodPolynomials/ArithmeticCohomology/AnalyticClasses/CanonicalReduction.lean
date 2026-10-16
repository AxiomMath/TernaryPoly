module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ExplicitPrimitiveFinite
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.ProjectedCoboundary

@[expose] public section


/-!
# Reduction of the projected good-line integral to the canonical cocycle

Combining the splitting of the projected term (`goodLineIwasawaProjectedTerm_split`) with the
generic edge transfer (`integral_edgeCombination_eq`), the integral of the finite average of the projected
part is the integral of the finite average of the *canonical* projected term plus the good-line
mixed coordinate of the two-coboundary of the dual stabilizer cochain of the explicit primitive.
The only analytic input taken as a hypothesis here is the integrability of the transported
edges of the explicit primitive (`EdgeIntegrable`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {index : Type} [Fintype index]

theorem goodLineFiniteVectorIntegral_endpoint_add (large : 3 < n) (cusp : CuspidalRepresentation)
    (v w : cusp.smooth) (hv : v.val ∈ cuspSphericalValues cusp)
    (hw : w.val ∈ cuspSphericalValues cusp) :
    goodLineFiniteVectorIntegral n cusp cohomologicalPoint (v + w) =
      goodLineFiniteVectorIntegral n cusp cohomologicalPoint v +
        goodLineFiniteVectorIntegral n cusp cohomologicalPoint w := by
  unfold goodLineFiniteVectorIntegral
  rw [← integral_add (goodLineFiniteVectorIntegrand_endpoint_integrable n large cusp v hv)
    (goodLineFiniteVectorIntegrand_endpoint_integrable n large cusp w hw)]
  congr 1
  funext finite
  rw [map_add, Pi.add_apply, mul_add]

/-- The finite average of a scalar test of a finite-level value. -/
abbrev tensorAverage (data : InducingData n) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (values : cuspidalTensorValues data.cusp (HomogeneousPoly n)) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint
    (cuspidalTensorFunctional data.cusp functional values)

theorem tensorAverage_add (large : 3 < n) (data : InducingData n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (a b : cuspidalTensorValues data.cusp (HomogeneousPoly n))
    (ha : a ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n))
    (hb : b ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n)) :
    tensorAverage data functional (a + b) =
      tensorAverage data functional a + tensorAverage data functional b := by
  unfold tensorAverage
  rw [map_add]
  exact goodLineFiniteVectorIntegral_endpoint_add large data.cusp _ _
    (cuspidalTensorFunctional_spherical data.cusp functional a ha)
    (cuspidalTensorFunctional_spherical data.cusp functional b hb)

theorem tensorAverage_sub (large : 3 < n) (data : InducingData n)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (a b : cuspidalTensorValues data.cusp (HomogeneousPoly n))
    (ha : a ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n))
    (hb : b ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n)) :
    tensorAverage data functional (a - b) =
      tensorAverage data functional a - tensorAverage data functional b := by
  unfold tensorAverage
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  rw [map_sub]
  exact goodLineFiniteVectorIntegral_endpoint_sub large data.cusp _ _
    (cuspidalTensorFunctional_spherical data.cusp functional a ha)
    (cuspidalTensorFunctional_spherical data.cusp functional b hb)

/-- The canonical projected term has finite-level values. -/
theorem canonicalProjectedTerm_finiteLevel (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    canonicalProjectedTerm data trivial basis relative regular u γ r ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) := by
  have simplex (Q : Fin 3 → RealPlaneGroup) :
      canonicalSimplexValue data trivial basis relative regular Q ∈
        cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) :=
    realPlaneCuspidalRep_finiteLevel n data.cusp data.chi _ _
      (realPlaneLevelBinaryRelativeCycle_finiteLevel n data.cusp data.chi trivial basis relative
        regular _)
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  exact cuspidalTensorMap_finiteLevel _ _ _ (Submodule.sub_mem _ (simplex _) (simplex _))

/-- The finite average of the canonical projected part. -/
def canonicalProjectedAverage (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ)
    (u : ℝ × ℝ) : ℂ :=
  tensorAverage data (functional.comp (lowerRadicalLatticeContribution n 0))
      (canonicalProjectedTerm data trivial basis relative regular u γ radicalLatticeFirst) +
    tensorAverage data (functional.comp (lowerRadicalLatticeContribution n 1))
      (canonicalProjectedTerm data trivial basis relative regular u γ radicalLatticeSecond)

/-- One radical contribution of the projected average splits. -/
theorem tensorAverage_projectedTerm_split (large : 3 < n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) :
    tensorAverage data functional (goodLineIwasawaProjectedTerm data source cocycle u γ r) =
      tensorAverage data functional
          (canonicalProjectedTerm data trivial basis relative regular u γ r) +
        edgeCombination data (totalPrimitiveEdge data trivial basis primitive relative regular)
          functional γ r u := by
  set E := totalPrimitiveEdge data trivial basis primitive relative regular
  have finite := totalPrimitiveEdge_finite data trivial basis primitive relative regular
  have T (x y : RealGL3) := edgeTransported_finiteLevel data E finite u x y
  have C := canonicalProjectedTerm_finiteLevel data trivial basis relative regular u γ r
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  rw [goodLineIwasawaProjectedTerm_split data trivial basis source cocycle primitive relative
    formula regular u γ r]
  rw [tensorAverage_add large data functional _ _ C
    (Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _ (T _ _) (T _ _)) (T _ _))
      (T _ _)),
    tensorAverage_sub large data functional _ _
      (Submodule.add_mem _ (Submodule.sub_mem _ (T _ _) (T _ _)) (T _ _)) (T _ _),
    tensorAverage_add large data functional _ _ (Submodule.sub_mem _ (T _ _) (T _ _)) (T _ _),
    tensorAverage_sub large data functional _ _ (T _ _) (T _ _)]
  rfl

/-- Integrability of the projected average (extracted from the round-2 reduction). -/
theorem projectedAverage_integrable (large : 9 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Integrable (projectedAverage data source cocycle γ functional)
      ((volume : Measure ℝ).prod volume) := by
  have three : 3 < n := by omega
  have five : 5 ≤ n := by omega
  have hdec := mixedFiniteFamily_decomposition three data source cocycle γ functional
  have iM := mixedFiniteFamily_endpoint_integrable five data source cocycle γ functional
  have i0 := prismCombination_integrable five data trivial source cocycle
    (functional.comp (lowerRadicalLatticeContribution n 0)) γ radicalLatticeFirst
  have i1 := prismCombination_integrable five data trivial source cocycle
    (functional.comp (lowerRadicalLatticeContribution n 1)) γ radicalLatticeSecond
  refine ((iM.sub i0).sub i1).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.sub_apply, hdec u]
  ring

theorem edgeCombination_integrable (data : InducingData n) (E : EdgeCochain data)
    (integrable : EdgeIntegrable data E) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    Integrable (edgeCombination data E functional γ r) ((volume : Measure ℝ).prod volume) := by
  obtain ⟨i1, i2, i3, i4⟩ := integrable functional γ r
  exact ((i1.sub i2).add i3).sub i4

/-- **The projected good-line integral is the canonical one plus a coboundary coordinate.** -/
theorem integral_projectedAverage_canonical (large : 9 ≤ n) (data : InducingData n)
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
    (γ : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∫ u, projectedAverage data source cocycle γ functional u ∂((volume : Measure ℝ).prod volume) =
      ∫ u, canonicalProjectedAverage data trivial basis relative regular γ functional u
          ∂((volume : Measure ℝ).prod volume) +
        functional (goodLineMixedCoordinate n γ (fun pair =>
          twoBoundaryCycle (goodLineCoefficientRep n)
            (edgeStabilizerCochain data
              (totalPrimitiveEdge data trivial basis primitive relative regular)) pair)) := by
  have three : 3 < n := by omega
  have five : 5 ≤ n := by omega
  set E := totalPrimitiveEdge data trivial basis primitive relative regular with hE
  set ℓ0 := functional.comp (lowerRadicalLatticeContribution n 0)
  set ℓ1 := functional.comp (lowerRadicalLatticeContribution n 1)
  have split (u : ℝ × ℝ) : projectedAverage data source cocycle γ functional u =
      canonicalProjectedAverage data trivial basis relative regular γ functional u +
        edgeCombination data E ℓ0 γ radicalLatticeFirst u +
        edgeCombination data E ℓ1 γ radicalLatticeSecond u := by
    change tensorAverage data ℓ0 (goodLineIwasawaProjectedTerm data source cocycle u γ
        radicalLatticeFirst) +
      tensorAverage data ℓ1 (goodLineIwasawaProjectedTerm data source cocycle u γ
        radicalLatticeSecond) = _
    rw [tensorAverage_projectedTerm_split three data trivial basis source cocycle primitive
        relative formula regular,
      tensorAverage_projectedTerm_split three data trivial basis source cocycle primitive
        relative formula regular]
    unfold canonicalProjectedAverage
    ring
  have iP := projectedAverage_integrable large data trivial source cocycle γ functional
  have i0 := edgeCombination_integrable data E edgeIntegrable ℓ0 γ radicalLatticeFirst
  have i1 := edgeCombination_integrable data E edgeIntegrable ℓ1 γ radicalLatticeSecond
  have iC : Integrable (canonicalProjectedAverage data trivial basis relative regular γ functional)
      ((volume : Measure ℝ).prod volume) := by
    refine ((iP.sub i0).sub i1).congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [Pi.sub_apply, split u]
    ring
  have total : (fun u => projectedAverage data source cocycle γ functional u) =
      fun u => (canonicalProjectedAverage data trivial basis relative regular γ functional u +
        edgeCombination data E ℓ0 γ radicalLatticeFirst u) +
        edgeCombination data E ℓ1 γ radicalLatticeSecond u := funext split
  have hsum1 := integral_add (iC.add i0) i1
  have hsum2 := integral_add iC i0
  simp only [Pi.add_apply] at hsum1 hsum2
  rw [total, hsum1, hsum2,
    integral_edgeCombination_eq five data trivial E
      (totalPrimitiveEdge_finite data trivial basis primitive relative regular)
      (totalPrimitiveEdge_levi data trivial basis primitive relative regular) edgeIntegrable ℓ0 γ
      radicalLatticeFirst,
    integral_edgeCombination_eq five data trivial E
      (totalPrimitiveEdge_finite data trivial basis primitive relative regular)
      (totalPrimitiveEdge_levi data trivial basis primitive relative regular) edgeIntegrable ℓ1 γ
      radicalLatticeSecond,
    goodLineMixedCoordinate_eq_contributions, map_add]
  simp only [ℓ0, ℓ1, LinearMap.comp_apply]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
