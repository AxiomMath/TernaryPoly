module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EdgeControl.EdgeIntegrable

@[expose] public section


/-!
# `EdgeIntegrable` for the edge cochain of the explicit total primitive

The four transported edges of every radical generator of the good-line stabilizer start at `1`, at
a Levi element or at a radical element, and both vertices stay in the big cell. Their radial
coordinates are the identity, the integral Levi transform or a lattice translate of `u`, all
measure preserving. With the control of the explicit total primitive of the chosen relative of a
plane source cocycle this proves `EdgeIntegrable` for `totalPrimitiveEdge`, the analytic input of
`integral_projectedAverage_canonical`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EdgeControl

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

variable {n : ℕ} {index : Type} [Fintype index]

theorem goodLineForm_radicalLevi (u : ℝ × ℝ) (r : RadicalLattice) (γ : GeneralLinearGroup (Fin 2)
    ℤ) :
    GoodLineForm (standardGoodLineRealArgument u * (edgeRadical r * edgeLevi γ)) := by
  rw [← mul_assoc, standardGoodLineRealArgument_radical]
  exact goodLineForm_levi _ γ

theorem corner_one_radius (u : ℝ × ℝ) :
    (gsVertex (standardGoodLineRealArgument u * 1)).val 2 2 = gsRadius (id u) := by
  rw [mul_one, gsVertex_standard, gsUpper_corner]
  rfl

theorem corner_levi_radius (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    (gsVertex (standardGoodLineRealArgument u * edgeLevi γ)).val 2 2 =
      gsRadius (goodLineLeviRealInput γ u) := by
  rw [standardGoodLineRealArgument_levi, goodLineConjugateRealLevi,
    gsVertex_plane_standard (planeLevi_mem _ _), planeLevi_mul_corner, gsUpper_corner]

theorem corner_radical_radius (u : ℝ × ℝ) (r : RadicalLattice) :
    (gsVertex (standardGoodLineRealArgument u * edgeRadical r)).val 2 2 =
      gsRadius (goodLineRadicalRealShift r u) := by
  rw [standardGoodLineRealArgument_radical, gsVertex_standard, gsUpper_corner]

/-- **`EdgeIntegrable` for a controlled homogeneous edge cochain.** -/
theorem homogeneousEdge_edgeIntegrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter)
    (cochain : RealPlaneGroup → realPlaneCuspidalRep n data.cusp data.chi)
    (controlled : OneControlled data.cusp (fun element =>
      (cochain element : cuspidalTensorValues data.cusp (HomogeneousPoly n))))
    (finite : EdgeFinite data (homogeneousEdge data cochain)) :
    EdgeIntegrable data (homogeneousEdge data cochain) := by
  intro functional γ r
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact homogeneousEdge_average_integrable data cochain _ _ large trivial controlled finite
      (fun u => goodLineForm_levi u γ) (fun u => goodLineForm_radicalLevi u r γ)
      (goodLineLeviRealInput γ) (goodLineLeviRealInput_measurePreserving γ)
      (fun u => corner_levi_radius u γ) functional
  · exact homogeneousEdge_average_integrable data cochain _ _ large trivial controlled finite
      (fun u => goodLineForm_radical u r) (fun u => goodLineForm_radicalLevi u r γ)
      (goodLineRadicalRealShift r) (radicalShift_measurePreserving r)
      (fun u => corner_radical_radius u r) functional
  · exact homogeneousEdge_average_integrable data cochain _ _ large trivial controlled finite
      (fun u => goodLineForm_one u) (fun u => goodLineForm_levi u γ) id (MeasurePreserving.id _)
      corner_one_radius functional
  · exact homogeneousEdge_average_integrable data cochain _ _ large trivial controlled finite
      (fun u => goodLineForm_one u) (fun u => goodLineForm_radical u r) id (MeasurePreserving.id _)
      corner_one_radius functional

/-- `EdgeIntegrable` for the explicit total primitive of the chosen relative of any plane source
cocycle. -/
theorem totalPrimitiveEdge_edgeIntegrable_of (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    EdgeIntegrable data (totalPrimitiveEdge data trivial basis primitive relative regular) :=
  homogeneousEdge_edgeIntegrable large data trivial _
    (sourceTotalPrimitive_oneControlled data trivial basis source cocycle primitive analytic
      relative formula regular)
    (totalPrimitiveEdge_finite data trivial basis primitive relative regular)

/-- **`EdgeIntegrable` for `totalPrimitiveEdge`, in the generality of
`integral_projectedAverage_canonical`.** The relative representative is Codexiom's chosen relative
of the determinant-normalized source; `analytic` is the joint analyticity of the Hilbert orbit of
its radical primitive (the first conjunct of
`sourcePlaneLevelGroupCocycle_exists_chosen_relative`). -/
theorem totalPrimitiveEdge_edgeIntegrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly n))
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep n data.cusp data.chi)
    (analytic : ∀ center : Fin 2 → ℝ, AnalyticAt ℝ (fun point : BinaryRealMatrix × (Fin 2 → ℝ) =>
      binaryHilbertTranslation data.cusp (atInfinity (invertibleMatrix point.1))
        (cuspidalTensorHilbertEmbedding data.cusp basis
          (primitive (Multiplicative.ofAdd point.2)).val)) (1, center))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep n data.cusp data.chi))
    (formula : relative.val = sourcePlaneLevelGroupCocycle data (normalizedSource source)
      (normalizedSource_cocycle data trivial source cocycle) -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive))
    (regular : RealPlaneLevelMixedRegular n data.cusp data.chi basis relative) :
    EdgeIntegrable data (totalPrimitiveEdge data trivial basis primitive relative regular) :=
  totalPrimitiveEdge_edgeIntegrable_of large data trivial basis (normalizedSource source)
    (normalizedSource_cocycle data trivial source cocycle) primitive analytic relative formula
    regular

end TernaryPeriodPolynomials.EdgeControl
