module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.Decomposition

@[expose] public section


/-!
# Integrability of the prism edges of the good-line mixed coordinate

Every edge occurring in the prism decomposition of the good-line mixed coordinate (and in the dual
description of the integrated prism cochain) starts at `1`, at a radical element or at a Levi element of
the good-line stabilizer, and both its vertices stay in the big cell. Hence all of their finite
averages are absolutely integrable at `s = -3/2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem planeLevi_standard_corner (B : BinaryRealGL) (v : ℝ × ℝ) :
    (planeLevi B 1 * standardGoodLineRealArgument v).val 2 2 = 1 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, standardGoodLineRealArgument_val]
  simp [planeLevi, planeBlock]

theorem standard_corner (v : ℝ × ℝ) : (standardGoodLineRealArgument v).val 2 2 = 1 := by
  rw [standardGoodLineRealArgument_val]; rfl

theorem corner_one (u : ℝ × ℝ) : (standardGoodLineRealArgument u * 1).val 2 2 ≠ 0 := by
  rw [mul_one, standard_corner]; exact one_ne_zero

theorem corner_levi (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    (standardGoodLineRealArgument u * edgeLevi γ).val 2 2 ≠ 0 := by
  rw [standardGoodLineRealArgument_levi, goodLineConjugateRealLevi, planeLevi_standard_corner]
  exact one_ne_zero

theorem corner_radical (u : ℝ × ℝ) (r : RadicalLattice) :
    (standardGoodLineRealArgument u * edgeRadical r).val 2 2 ≠ 0 := by
  rw [standardGoodLineRealArgument_radical, standard_corner]; exact one_ne_zero

theorem corner_radical_levi (u : ℝ × ℝ) (r : RadicalLattice) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    (standardGoodLineRealArgument u * (edgeRadical r * edgeLevi γ)).val 2 2 ≠ 0 := by
  rw [← mul_assoc, standardGoodLineRealArgument_radical]
  exact corner_levi _ γ

theorem radicalShift_measurePreserving (r : RadicalLattice) :
    MeasurePreserving (goodLineRadicalRealShift r) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have e : goodLineRadicalRealShift r = fun u => u + (3 * (r.toAdd.2 : ℝ), 3 * (r.toAdd.1 : ℝ)) :=
    funext (goodLineRadicalRealShift_eq_add r)
  rw [e]
  exact measurePreserving_add_right _ _

/-- Edges starting at `1`. -/
theorem prismEdgeAverage_one_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (b : RealGL3)
    (cornerB : ∀ u, (standardGoodLineRealArgument u * b).val 2 2 ≠ 0) :
    Integrable (prismEdgeAverage data source cocycle functional 1 b) ((volume : Measure ℝ).prod volume) :=
  prismEdgeAverage_integrable large data trivial source cocycle 1 b functional corner_one cornerB
    prismVertex_one_mem id (MeasurePreserving.id _) upperBlockDet_prismVertex_one

/-- Edges starting at a Levi element. -/
theorem prismEdgeAverage_levi_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (b : RealGL3)
    (cornerB : ∀ u, (standardGoodLineRealArgument u * b).val 2 2 ≠ 0) :
    Integrable (prismEdgeAverage data source cocycle functional (edgeLevi γ) b)
      ((volume : Measure ℝ).prod volume) :=
  prismEdgeAverage_integrable large data trivial source cocycle (edgeLevi γ) b functional
    (fun u => corner_levi u γ) cornerB (fun u => prismVertex_levi_mem u γ) (goodLineLeviRealInput γ)
    (goodLineLeviRealInput_measurePreserving γ) (fun u => upperBlockDet_prismVertex_levi u γ)

/-- Edges starting at a radical element. -/
theorem prismEdgeAverage_radical_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (r : RadicalLattice) (b : RealGL3)
    (cornerB : ∀ u, (standardGoodLineRealArgument u * b).val 2 2 ≠ 0) :
    Integrable (prismEdgeAverage data source cocycle functional (edgeRadical r) b)
      ((volume : Measure ℝ).prod volume) :=
  prismEdgeAverage_integrable large data trivial source cocycle (edgeRadical r) b functional
    (fun u => corner_radical u r) cornerB (fun u => prismVertex_radical_mem u r) (goodLineRadicalRealShift r)
    (radicalShift_measurePreserving r) (fun u => upperBlockDet_prismVertex_radical u r)

theorem prismCombination_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    Integrable (prismCombination data source cocycle functional γ r) ((volume : Measure ℝ).prod volume) :=
  (((prismEdgeAverage_levi_integrable large data trivial source cocycle functional γ _
      (fun u => corner_radical_levi u r γ)).sub
    (prismEdgeAverage_radical_integrable large data trivial source cocycle functional r _
      (fun u => corner_radical_levi u r γ))).add
    (prismEdgeAverage_one_integrable large data trivial source cocycle functional _
      (fun u => corner_levi u γ))).sub
    (prismEdgeAverage_one_integrable large data trivial source cocycle functional _
      (fun u => corner_radical u r))

/-- **The integral of one prism combination is the combination of the edge integrals.** -/
theorem integral_prismCombination (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (γ : GeneralLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    ∫ u, prismCombination data source cocycle functional γ r u ∂((volume : Measure ℝ).prod volume) =
      prismEdgeIntegral data source cocycle functional (edgeLevi γ) (edgeRadical r * edgeLevi γ) -
        prismEdgeIntegral data source cocycle functional (edgeRadical r) (edgeRadical r * edgeLevi γ) +
        prismEdgeIntegral data source cocycle functional 1 (edgeLevi γ) -
        prismEdgeIntegral data source cocycle functional 1 (edgeRadical r) := by
  have i1 := prismEdgeAverage_levi_integrable large data trivial source cocycle functional γ _
    (fun u => corner_radical_levi u r γ)
  have i2 := prismEdgeAverage_radical_integrable large data trivial source cocycle functional r _
    (fun u => corner_radical_levi u r γ)
  have i3 := prismEdgeAverage_one_integrable large data trivial source cocycle functional _
    (fun u => corner_levi u γ)
  have i4 := prismEdgeAverage_one_integrable large data trivial source cocycle functional _
    (fun u => corner_radical u r)
  unfold prismCombination prismEdgeIntegral
  have h1 := integral_sub ((i1.sub i2).add i3) i4
  have h2 := integral_add (i1.sub i2) i3
  have h3 := integral_sub i1 i2
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 h3
  rw [h1, h2, h3]

end TernaryPeriodPolynomials.AnalyticClasses
