module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismEquivariance

@[expose] public section


/-!
# Continuity and integrability of the good-line mixed finite family at the cohomological point

The bounded realization of a scalar test of the source cusp values at fixed vertices is a finite
combination of bounded realizations of source-cochain cusp vectors, hence continuous in the real
argument. So the finite good-line average of the mixed cusp values is continuous in the radical
coordinate; with the uniform decay of `SourceValueBounds` it is absolutely integrable at `s = -3/2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.ArchimedeanConstant

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- A coefficient of the source cusp values is a source-cochain cusp vector value. -/
theorem coeff_sourcePlaneCuspidalValues (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (m : Fin 3 →₀ ℕ) (vertices : Fin 3 → RealGL3)
    (g : RealGL3) (A : BinaryAdelicGL) :
    ((sourcePlaneCuspidalValues data source cocycle vertices (atInfinity g)).val A).val.coeff m =
      data.cusp.realize (cochainCuspVector data source cocycle m vertices g) A := by
  unfold cochainCuspVector
  rw [CuspVectors.realize_planeCuspVector, sourcePlaneCuspidalValues_apply,
    binaryInductionExponent_plane_endpoint, Submodule.coe_smul, coeff_smul, smul_eq_mul]

/-- The bounded realization of a scalar test of the source cusp values. -/
theorem boundedRealization_sourceValues (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (vertices : Fin 3 → RealGL3) (g : RealGL3) :
    CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp functional
        (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity g))) =
      ∑ m ∈ degreeMonomials n, functional (monomialVector n m) •
        CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m vertices g) := by
  apply Subtype.ext
  funext A
  change data.cusp.realize _ A = _
  rw [cuspidalTensorFunctional_realize, functional_eq_sum_coeff functional]
  simp only [AddSubgroup.val_finsetSum, lp.coeFn_smul]
  change _ = (∑ m ∈ degreeMonomials n, (functional (monomialVector n m) •
    (CuspSupNorm.boundedRealization data.cusp (cochainCuspVector data source cocycle m vertices g) :
      BinaryAdelicGL → ℂ) : BinaryAdelicGL → ℂ)) A
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro m _
  rw [coeff_sourcePlaneCuspidalValues, mul_comm]
  rfl

theorem sourceValues_boundedRealization_continuous (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (vertices : Fin 3 → RealGL3) :
    Continuous (fun u => CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp functional
      (sourcePlaneCuspidalValues data source cocycle vertices (atInfinity (standardGoodLineRealArgument u))))) := by
  simp_rw [boundedRealization_sourceValues]
  apply continuous_finsetSum
  intro m _
  exact (continuous_const (y := functional (monomialVector n m))).smul
    (cochainCuspVector_comp_continuous data source cocycle m
      (fun _ => vertices) standardGoodLineRealArgument continuous_const continuous_standardGoodLineRealArgument)

/-- The bounded realization of the mixed test vector, through the four source simplices. -/
theorem boundedRealization_mixedTestVector (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (u : ℝ × ℝ) :
    CuspSupNorm.boundedRealization data.cusp (mixedTestVector data source cocycle matrix functional u) =
      (CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp
          (functional.comp (lowerRadicalLatticeContribution n 0))
          (sourcePlaneCuspidalValues data source cocycle (goodLineRealVertices (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeFirst)))
            (atInfinity (standardGoodLineRealArgument u)))) -
        CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp
          (functional.comp (lowerRadicalLatticeContribution n 0))
          (sourcePlaneCuspidalValues data source cocycle (goodLineRealVertices
            (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection matrix))
            (atInfinity (standardGoodLineRealArgument u))))) +
      (CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp
          (functional.comp (lowerRadicalLatticeContribution n 1))
          (sourcePlaneCuspidalValues data source cocycle (goodLineRealVertices (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeSecond)))
            (atInfinity (standardGoodLineRealArgument u)))) -
        CuspSupNorm.boundedRealization data.cusp (cuspidalTensorFunctional data.cusp
          (functional.comp (lowerRadicalLatticeContribution n 1))
          (sourcePlaneCuspidalValues data source cocycle (goodLineRealVertices
            (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection matrix))
            (atInfinity (standardGoodLineRealArgument u))))) := by
  apply Subtype.ext
  funext A
  change data.cusp.realize _ A = _
  rw [mixedTestVector, cuspidalTensorFunctional_realize, goodLineMixedCuspidalValues_apply,
    goodLineMixedRealCoordinate_contributions]
  simp only [map_add, map_sub, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply]
  change _ = (data.cusp.realize _ A - data.cusp.realize _ A) + (data.cusp.realize _ A - data.cusp.realize _ A)
  simp only [cuspidalTensorFunctional_realize, LinearMap.comp_apply]

theorem mixedTestVector_boundedRealization_continuous (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun u => CuspSupNorm.boundedRealization data.cusp
      (mixedTestVector data source cocycle matrix functional u)) := by
  simp_rw [boundedRealization_mixedTestVector]
  exact ((sourceValues_boundedRealization_continuous data source cocycle _ _).sub
    (sourceValues_boundedRealization_continuous data source cocycle _ _)).add
    ((sourceValues_boundedRealization_continuous data source cocycle _ _).sub
    (sourceValues_boundedRealization_continuous data source cocycle _ _))

/-- **Integrability of the mixed finite family at the cohomological point.** -/
theorem mixedFiniteFamily_endpoint_integrable (large : 5 ≤ n) (data : InducingData n)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Integrable (mixedFiniteFamily data source cocycle matrix functional cohomologicalPoint)
      ((volume : Measure ℝ).prod volume) := by
  have three : 3 < n := by omega
  have convergent : 3 < (finiteExponent n cohomologicalPoint).re := by
    rw [finiteExponent_re]
    have : (3 : ℝ) < n := by exact_mod_cast three
    norm_num [cohomologicalPoint]
    linarith
  have continuity : Continuous (mixedFiniteFamily data source cocycle matrix functional cohomologicalPoint) :=
    finiteAverage_continuous three data.cusp (mixedTestVector data source cocycle matrix functional)
      (mixedTestVector_spherical data source cocycle matrix functional)
      (mixedTestVector_boundedRealization_continuous data source cocycle matrix functional)
  obtain ⟨C, hC0, hC⟩ := mixedCuspidalValues_decay data source cocycle matrix functional
  have dominating : Integrable (fun u => weightMass (finiteExponent n cohomologicalPoint).re *
      (kernelBase u ^ (-(((n : ℝ) + 3) / 4)) * C)) ((volume : Measure ℝ).prod volume) :=
    ((kernelBase_decay_integrable large).mul_const C).const_mul _
  refine dominating.mono' continuity.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  exact norm_goodLineFiniteVectorIntegral_le data.cusp cohomologicalPoint convergent _
    (mixedTestVector_spherical data source cocycle matrix functional u) _ (hC u)

end TernaryPeriodPolynomials.AnalyticClasses
