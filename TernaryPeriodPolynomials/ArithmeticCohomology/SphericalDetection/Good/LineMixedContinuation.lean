module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedReal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFunctionalContinuation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineMixedRealCoordinate_continuation {degree : ℕ} (local_entry : LocalBadPlaneEntry)
    (data : InducingData degree) (flat standard : ℂ → SourceCochain degree)
    (flat_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    (∀ parameter, MeromorphicAt (fun parameter => functional
      (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter))) parameter) ∧
    ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      Integrable (fun away => functional (goodLineMixedRealCoordinate degree matrix
        (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away))) radicalAwayThreeMeasure ∧
      functional (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter)) =
        ∫ away, functional (goodLineMixedRealCoordinate degree matrix
          (fun vertices => standardGoodLineAwayPolynomial flat parameter vertices away)) ∂radicalAwayThreeMeasure := by
  let left (coordinate : Fin 2) := goodLineRealVertices (goodLineLeviSection matrix,
    goodLineRadicalInclusion (lowerLeviLatticeInput matrix (radicalLatticeGenerator coordinate)))
  let right (coordinate : Fin 2) :=
    goodLineRealVertices (goodLineRadicalInclusion (radicalLatticeGenerator coordinate), goodLineLeviSection matrix)
  let coefficient (coordinate : Fin 2) := functional.comp (lowerRadicalLatticeContribution degree coordinate)
  have component (coordinate : Fin 2) := scalarIntegralContinuation_sub radicalAwayThreeMeasure
    (fun parameter away => coefficient coordinate (standardGoodLineAwayPolynomial flat parameter (left coordinate) away))
    (fun parameter away => coefficient coordinate (standardGoodLineAwayPolynomial flat parameter (right coordinate) away))
    (fun parameter => coefficient coordinate (goodLineComplementFamily standard parameter (left coordinate)))
    (fun parameter => coefficient coordinate (goodLineComplementFamily standard parameter (right coordinate)))
    (goodLineComplementFamily_functional_continuation local_entry data flat standard flat_sections endpoint_support
      continuations (left coordinate) (coefficient coordinate))
    (goodLineComplementFamily_functional_continuation local_entry data flat standard flat_sections endpoint_support
      continuations (right coordinate) (coefficient coordinate))
  have combined := scalarIntegralContinuation_add radicalAwayThreeMeasure _ _ _ _ (component 0) (component 1)
  have formula (values : (Fin 3 → RealGL3) → HomogeneousPoly degree) :
      functional (goodLineMixedRealCoordinate degree matrix values) =
        (coefficient 0 (values (left 0)) - coefficient 0 (values (right 0))) +
          (coefficient 1 (values (left 1)) - coefficient 1 (values (right 1))) := by
    rw [goodLineMixedRealCoordinate_contributions, map_add, map_sub, map_sub, map_sub, map_sub]
    rfl
  simp_rw [formula]
  exact combined

theorem goodLineMixedRealCoordinate_analytic {degree : ℕ} (standard : ℂ → SourceCochain degree)
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    AnalyticAt ℂ (fun parameter => functional
      (goodLineMixedRealCoordinate degree matrix (goodLineComplementFamily standard parameter))) cohomologicalPoint := by
  simp_rw [goodLineMixedRealCoordinate_contributions, map_add, map_sub]
  exact ((goodLineComplementFamily_functional_analytic standard analytic _
    (functional.comp (lowerRadicalLatticeContribution degree 0))).sub
      (goodLineComplementFamily_functional_analytic standard analytic _
        (functional.comp (lowerRadicalLatticeContribution degree 0)))).add
    ((goodLineComplementFamily_functional_analytic standard analytic _
      (functional.comp (lowerRadicalLatticeContribution degree 1))).sub
        (goodLineComplementFamily_functional_analytic standard analytic _
          (functional.comp (lowerRadicalLatticeContribution degree 1))))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
