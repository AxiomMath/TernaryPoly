module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Iwasawa.PrismContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.MixedEndpointIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLeviMeasure
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorPolynomial

@[expose] public section


/-!
# Absolute integrability of the Iwasawa prism terms at the cohomological point

The prism terms at the edges `(1, ·)`, `(γ, ·)` and `(n_r, ·)` used by the good-line mixed coordinate
have finite good-line averages bounded by `C (1 + |v|²)^{-(n+3)/4}`, with `v` equal to `u`, to the Levi
transform of `u` or to its radical translate. These are absolutely integrable over `ℝ²` (for `n ≥ 5`),
and the averages are continuous in `u`. Hence each prism term of the mixed cusp values contributes an
absolutely convergent integral at `s = -3/2`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.ArchimedeanConstant

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem upperBlockDet_mul {p q : RealGL3} (hq : q ∈ planeParabolic ℝ) :
    upperBlockDet (p * q) = upperBlockDet p * upperBlockDet q := by
  obtain ⟨h0, h1⟩ := hq
  change q.val 2 0 = 0 at h0
  change q.val 2 1 = 0 at h1
  simp only [upperBlockDet, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]
  ring

theorem upperBlockDet_gsUpper (u : ℝ × ℝ) : upperBlockDet (gsUpper u) = (gsRadius u)⁻¹ := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  rw [upperBlockDet, gsUpper_val]
  simp [gsUpperMatrix]
  field_simp

theorem upperBlockDet_planeLevi (B : BinaryRealGL) : upperBlockDet (planeLevi B 1) = B.val.det := by
  simp [upperBlockDet, planeLevi, planeBlock, Matrix.det_fin_two]

theorem abs_upperBlockDet_conjugateLevi (γ : GeneralLinearGroup (Fin 2) ℤ) :
    |upperBlockDet (goodLineConjugateRealLevi γ)| = 1 := by
  rw [goodLineConjugateRealLevi, upperBlockDet_planeLevi]
  have hswap : (binaryPivotSwap : BinaryRealGL).val.det = -1 := by
    simp [binaryPivotSwap, Matrix.det_fin_two]
  have hγ : |(GeneralLinearGroup.map (Int.castRingHom ℝ) γ).val.det| = 1 := by
    have hmap : (GeneralLinearGroup.map (Int.castRingHom ℝ) γ).val.det = ((γ.val.det : ℤ) : ℝ) :=
      ((Int.castRingHom ℝ).map_det γ.val).symm
    have integral : |γ.val.det| = 1 := Int.isUnit_iff_abs_eq.mp (GeneralLinearGroup.det γ).isUnit
    rw [hmap]
    exact_mod_cast integral
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hswap, abs_mul, abs_mul, hγ]
  norm_num

theorem gsRadius_inv_rpow (u : ℝ × ℝ) (e : ℝ) :
    |(gsRadius u)⁻¹| ^ e = kernelBase u ^ (-(e / 2)) := by
  rw [abs_of_pos (inv_pos.mpr (gsRadius_pos u)), gsRadius, ← Real.sqrt_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (inv_nonneg.mpr (by positivity)), Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  unfold kernelBase
  congr 1
  ring

/-- The `GL₂` block of the Iwasawa vertex at `g(u) a` for the three kinds of first vertex. -/
theorem upperBlockDet_prismVertex_one (u : ℝ × ℝ) :
    |upperBlockDet (gsVertex (standardGoodLineRealArgument u * 1))| = |(gsRadius u)⁻¹| := by
  rw [mul_one, gsVertex_standard, upperBlockDet_gsUpper]

theorem upperBlockDet_prismVertex_levi (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    |upperBlockDet (gsVertex (standardGoodLineRealArgument u *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)))| =
      |(gsRadius (goodLineLeviRealInput γ u))⁻¹| := by
  rw [standardGoodLineRealArgument_levi, goodLineConjugateRealLevi, gsVertex_plane_standard (planeLevi_mem _ _),
    upperBlockDet_mul (gsUpper_mem_planeParabolic _), abs_mul, ← goodLineConjugateRealLevi,
    abs_upperBlockDet_conjugateLevi, one_mul,
    upperBlockDet_gsUpper]

theorem upperBlockDet_prismVertex_radical (u : ℝ × ℝ) (r : RadicalLattice) :
    |upperBlockDet (gsVertex (standardGoodLineRealArgument u *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)))| =
      |(gsRadius (goodLineRadicalRealShift r u))⁻¹| := by
  rw [standardGoodLineRealArgument_radical, gsVertex_standard, upperBlockDet_gsUpper]

theorem prismVertex_one_mem (u : ℝ × ℝ) :
    gsVertex (standardGoodLineRealArgument u * 1) ∈ planeParabolic ℝ := by
  rw [mul_one, gsVertex_standard]; exact gsUpper_mem_planeParabolic u

theorem prismVertex_levi_mem (u : ℝ × ℝ) (γ : GeneralLinearGroup (Fin 2) ℤ) :
    gsVertex (standardGoodLineRealArgument u *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (arithmeticLevi γ)) ∈ planeParabolic ℝ := by
  rw [standardGoodLineRealArgument_levi, goodLineConjugateRealLevi]
  exact gsVertex_plane_standard_mem (planeLevi_mem _ _) _

theorem prismVertex_radical_mem (u : ℝ × ℝ) (r : RadicalLattice) :
    gsVertex (standardGoodLineRealArgument u *
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (lowerRadicalLattice r)) ∈ planeParabolic ℝ := by
  rw [standardGoodLineRealArgument_radical, gsVertex_standard]
  exact gsUpper_mem_planeParabolic _

/-- The decay profile is integrable. -/
theorem kernelBase_decay_integrable (large : 5 ≤ n) :
    Integrable (fun u : ℝ × ℝ => kernelBase u ^ (-(((n : ℝ) + 3) / 4))) := by
  refine kernelBase_rpow_neg_two_integrable.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (Continuous.rpow_const (by unfold kernelBase; fun_prop)
      (fun u => Or.inl (kernelBase_pos u).ne')).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (kernelBase_pos u).le _)]
    apply Real.rpow_le_rpow_of_exponent_le (kernelBase_one_le u)
    have : (5 : ℝ) ≤ n := by exact_mod_cast large
    linarith

end TernaryPeriodPolynomials.AnalyticClasses

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem goodLineIwasawaPrism_finiteLevel (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (edge : Fin 2 → RealGL3) :
    goodLineIwasawaPrism data source cocycle u edge ∈
      cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) := by
  have hone : atInfinity (1 : RealGL3) = 1 := AveragingSmooth.atInfinity_one
  have member (V : Fin 3 → RealGL3) :
      sourcePlaneCuspidalValues data source cocycle V 1 ∈ cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly n) := by
    have := sourcePlaneCuspidalValues_finiteLevel data source cocycle V 1
    rwa [hone] at this
  unfold goodLineIwasawaPrism sourceCuspidalVertexPrism homogeneousVertexPrism
  apply cuspidalTensorMap_finiteLevel
  let _ : AddCommGroup (cuspidalTensorValues data.cusp (HomogeneousPoly n)) :=
    (cuspidalTensorValues data.cusp (HomogeneousPoly n)).addCommGroup
  exact Submodule.sub_mem _ (member _) (member _)

theorem goodLineIwasawaPrism_spherical (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (u : ℝ × ℝ) (edge : Fin 2 → RealGL3)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u edge)).val ∈
      cuspSphericalValues data.cusp :=
  cuspidalTensorFunctional_spherical data.cusp functional _
    (goodLineIwasawaPrism_finiteLevel data source cocycle u edge)

/-- **Absolute integrability of one Iwasawa prism edge at the cohomological point.** -/
theorem prismEdgeAverage_integrable (large : 5 ≤ n) (data : InducingData n)
    (trivial : data.chi = trivialCharacter) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (a b : RealGL3)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (cornerA : ∀ u, (standardGoodLineRealArgument u * a).val 2 2 ≠ 0)
    (cornerB : ∀ u, (standardGoodLineRealArgument u * b).val 2 2 ≠ 0)
    (bigCell : ∀ u, gsVertex (standardGoodLineRealArgument u * a) ∈ planeParabolic ℝ)
    (transform : ℝ × ℝ → ℝ × ℝ)
    (preserving : MeasurePreserving transform ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume))
    (determinant : ∀ u, |upperBlockDet (gsVertex (standardGoodLineRealArgument u * a))| =
      |(gsRadius (transform u))⁻¹|) :
    Integrable (fun u => goodLineFiniteVectorIntegral n data.cusp cohomologicalPoint
      (cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u ![a, b])))
      ((volume : Measure ℝ).prod volume) := by
  have three : 3 < n := by omega
  have convergent : 3 < (finiteExponent n cohomologicalPoint).re := by
    rw [finiteExponent_re]
    have : (3 : ℝ) < n := by exact_mod_cast three
    norm_num [cohomologicalPoint]
    linarith
  obtain ⟨C, hC0, hC⟩ := goodLineIwasawaPrism_bound data trivial source cocycle a b bigCell functional
  have continuity := finiteAverage_continuous three data.cusp
    (fun u => cuspidalTensorFunctional data.cusp functional (goodLineIwasawaPrism data source cocycle u ![a, b]))
    (fun u => goodLineIwasawaPrism_spherical data source cocycle u ![a, b] functional)
    (prism_boundedRealization_continuous data trivial source cocycle a b functional cornerA cornerB)
  have dominating : Integrable (fun u => weightMass (finiteExponent n cohomologicalPoint).re * C *
      kernelBase (transform u) ^ (-(((n : ℝ) + 3) / 4))) ((volume : Measure ℝ).prod volume) :=
    ((preserving.integrable_comp_of_integrable (kernelBase_decay_integrable large)).const_mul _)
  refine dominating.mono' continuity.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  have pointwise : ∀ A, ‖data.cusp.realize (cuspidalTensorFunctional data.cusp functional
      (goodLineIwasawaPrism data source cocycle u ![a, b])) A‖ ≤
      kernelBase (transform u) ^ (-(((n : ℝ) + 3) / 4)) * C := by
    intro A
    rw [cuspidalTensorFunctional_realize]
    refine (hC u A).trans (le_of_eq ?_)
    rw [determinant, gsRadius_inv_rpow]
    congr 2
    ring
  refine (norm_goodLineFiniteVectorIntegral_le data.cusp cohomologicalPoint convergent _
    (goodLineIwasawaPrism_spherical data source cocycle u ![a, b] functional) _ pointwise).trans (le_of_eq ?_)
  ring

end TernaryPeriodPolynomials.AnalyticClasses
