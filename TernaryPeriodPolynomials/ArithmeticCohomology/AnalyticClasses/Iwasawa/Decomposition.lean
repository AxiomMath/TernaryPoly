module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.MixedFamilyIntegrability

@[expose] public section


/-!
# The mixed finite family split into its projected and prism parts

At `s = -3/2` the finite good-line average of the mixed cusp values is the sum of the averages of the
projected part (the source on Iwasawa simplices) and of the four prism edges per radical generator.
All the prism averages are absolutely integrable, so the integral splits accordingly.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The finite average of a finite linear combination of spherical vectors. -/
theorem finiteAverage_combination (large : 3 < n) (cusp : CuspidalRepresentation) (w : cusp.smooth)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → cusp.smooth)
    (spherical : ∀ i, (v i).val ∈ cuspSphericalValues cusp)
    (combination : ∀ A, cusp.realize w A = ∑ i ∈ s, c i * cusp.realize (v i) A) :
    goodLineFiniteVectorIntegral n cusp cohomologicalPoint w =
      ∑ i ∈ s, c i * goodLineFiniteVectorIntegral n cusp cohomologicalPoint (v i) := by
  unfold goodLineFiniteVectorIntegral
  simp_rw [combination, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    congr 1
    funext f
    ring
  · intro i _
    have := (goodLineFiniteVectorIntegrand_endpoint_integrable n large cusp (v i) (spherical i)).const_mul (c i)
    refine this.congr (Filter.Eventually.of_forall fun f => ?_)
    ring

/-- The real image of the Levi section. -/
abbrev edgeLevi (γ : GeneralLinearGroup (Fin 2) ℤ) : RealGL3 :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)

/-- The real image of a radical lattice element. -/
abbrev edgeRadical (r : RadicalLattice) : RealGL3 :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)

/-- The four prism edge averages of one radical generator. -/
def prismCombination (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) (u : ℝ × ℝ) : ℂ :=
  prismEdgeAverage data source cocycle functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) u -
    prismEdgeAverage data source cocycle functional (edgeRadical r) (edgeRadical r * edgeLevi γ) u +
    prismEdgeAverage data source cocycle functional 1 (edgeLevi γ) u -
    prismEdgeAverage data source cocycle functional 1 (edgeRadical r) u

/-- The finite average of the projected part. -/
def projectedAverage (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (u : ℝ × ℝ) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint (cuspidalTensorFunctional data.cusp
      (functional.comp (lowerRadicalLatticeContribution n 0))
      (goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeFirst)) +
    goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint (cuspidalTensorFunctional data.cusp
      (functional.comp (lowerRadicalLatticeContribution n 1))
      (goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeSecond))

theorem goodLineIwasawaProjectedTerm_spherical (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (r : RadicalLattice) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaProjectedTerm data source cocycle u γ r)).val ∈
      cuspSphericalValues data.cusp := by
  apply cuspidalTensorFunctional_spherical data.cusp functional
  have hone : atInfinity (1 : RealGL3) = 1 := AveragingSmooth.atInfinity_one
  have member (V : Fin 3 → RealGL3) :
      sourcePlaneCuspidalValues data source cocycle V 1 ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) := by
    have := sourcePlaneCuspidalValues_finiteLevel data source cocycle V 1
    rwa [hone] at this
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  exact Submodule.sub_mem _ (cuspidalTensorMap_finiteLevel _ _ _ (member _))
    (cuspidalTensorMap_finiteLevel _ _ _ (member _))

/-- **Pointwise decomposition of the mixed finite family at the cohomological point.** -/
theorem mixedFiniteFamily_decomposition (large : 3 < n) (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (γ : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (u : ℝ × ℝ) :
    mixedFiniteFamily data source cocycle γ functional cohomologicalPoint u =
      projectedAverage data source cocycle γ functional u +
        prismCombination data source cocycle (functional.comp (lowerRadicalLatticeContribution n 0))
          γ radicalLatticeFirst u +
        prismCombination data source cocycle (functional.comp (lowerRadicalLatticeContribution n 1))
          γ radicalLatticeSecond u := by
  set ℓ0 := functional.comp (lowerRadicalLatticeContribution n 0)
  set ℓ1 := functional.comp (lowerRadicalLatticeContribution n 1)
  let P := goodLineIwasawaPrism data source cocycle u
  let vectors : Fin 10 → data.cusp.smooth := ![
    cuspidalTensorFunctional data.cusp ℓ0 (goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeFirst),
    cuspidalTensorFunctional data.cusp ℓ1 (goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeSecond),
    cuspidalTensorFunctional data.cusp ℓ0 (P ![edgeLevi γ, edgeRadical radicalLatticeFirst * edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ0 (P ![edgeRadical radicalLatticeFirst, edgeRadical radicalLatticeFirst * edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ0 (P ![1, edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ0 (P ![1, edgeRadical radicalLatticeFirst]),
    cuspidalTensorFunctional data.cusp ℓ1 (P ![edgeLevi γ, edgeRadical radicalLatticeSecond * edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ1 (P ![edgeRadical radicalLatticeSecond, edgeRadical radicalLatticeSecond * edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ1 (P ![1, edgeLevi γ]),
    cuspidalTensorFunctional data.cusp ℓ1 (P ![1, edgeRadical radicalLatticeSecond])]
  let coefficients : Fin 10 → ℂ := ![1, 1, 1, -1, 1, -1, 1, -1, 1, -1]
  have spherical : ∀ i, (vectors i).val ∈ cuspSphericalValues data.cusp := by
    intro i
    fin_cases i
    · exact goodLineIwasawaProjectedTerm_spherical data source cocycle u γ _ _
    · exact goodLineIwasawaProjectedTerm_spherical data source cocycle u γ _ _
    all_goals exact goodLineIwasawaPrism_spherical data source cocycle u _ _
  have combination : ∀ A, data.cusp.realize (mixedTestVector data source cocycle γ functional u) A =
      ∑ i, coefficients i * data.cusp.realize (vectors i) A := by
    intro A
    rw [mixedTestVector, cuspidalTensorFunctional_realize, goodLineMixedCuspidalValues_iwasawa]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, vectors, coefficients]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    change functional ((lowerRadicalLatticeContribution n 0)
        ((goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeFirst).val A) +
      (lowerRadicalLatticeContribution n 1)
        ((goodLineIwasawaProjectedTerm data source cocycle u γ radicalLatticeSecond).val A) +
      ((lowerRadicalLatticeContribution n 0)
        ((goodLineCuspidalMixedPrimitiveValue data.cusp P γ radicalLatticeFirst).val A) +
      (lowerRadicalLatticeContribution n 1)
        ((goodLineCuspidalMixedPrimitiveValue data.cusp P γ radicalLatticeSecond).val A))) = _
    simp only [goodLineCuspidalMixedPrimitiveValue]
    change functional ((lowerRadicalLatticeContribution n 0) _ + (lowerRadicalLatticeContribution n 1) _ +
      ((lowerRadicalLatticeContribution n 0) ((P _).val A - (P _).val A + (P _).val A - (P _).val A) +
      (lowerRadicalLatticeContribution n 1) ((P _).val A - (P _).val A + (P _).val A - (P _).val A))) = _
    simp only [map_add, map_sub, ℓ0, ℓ1]
    simp only [cuspidalTensorFunctional_realize, LinearMap.comp_apply]
    ring
  rw [mixedFiniteFamily, finiteAverage_combination large data.cusp _ Finset.univ coefficients vectors
    spherical combination]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, vectors, coefficients, projectedAverage, prismCombination,
    prismEdgeAverage, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

end TernaryPeriodPolynomials.AnalyticClasses
