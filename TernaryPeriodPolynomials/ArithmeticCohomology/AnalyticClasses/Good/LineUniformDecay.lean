module

public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.InducedDecay
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Scalar
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.RotationTypes
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Admissibility

@[expose] public section


/-!
# Uniform decay of plane cusp lifts along the good-line argument

`ArchimedeanConstant.goodLine_induced_decay` bounds a plane-induced section along the
good-line argument `g(u) = p(u) k(u)` by `(1+|u|²)^{-(n+3)/4}` times a constant depending on
the compact factor `k(u)`. Admissibility of the cuspidal datum (finite-dimensional rotation
modes, `PlaneEisensteinContinuation.EndpointAdmissibility`) makes the analytic-stage
realizations continuous, which gives a bound for the cusp lifts uniform over the whole
maximal compact subgroup (`PlaneEisensteinContinuation.AnalyticScalar.maximalCompact_bound`).
Combining the two gives a constant independent of `u`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.PlaneEisensteinContinuation

variable {n : ℕ}

/-- Every cohomological cuspidal datum has continuous analytic-stage realizations. -/
theorem continuousStages (data : InducingData n) : AnalyticScalar.ContinuousStages data.cusp :=
  FiniteRotationTypes.continuousStages_of_finite_types data.cusp
    (EndpointAdmissibility.all_finiteDimensional data)

/-- Left multiplication by a real orthogonal matrix preserves the maximal compact subgroup. -/
theorem inMaximalCompact_atInfinity_mul {k : RealGL3} (hk : k.val.transpose * k.val = 1)
    {h : AdelicGL} (hh : inMaximalCompact h) : inMaximalCompact (atInfinity k * h) := by
  refine ⟨?_, ?_⟩
  · rw [map_mul, EisensteinRegularization.Helpers.realGroup_atInfinity]
    simp only [Units.val_mul, Matrix.transpose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (k.val.transpose), hk, Matrix.one_mul]
    exact hh.1
  · rw [map_mul, EisensteinRegularization.Helpers.finiteGroup_atInfinity, one_mul]
    exact hh.2

/-- **Uniform decay of plane cusp lifts along the good line.** For a plane-induced section at
the cohomological point there is one constant `C` with
`‖φ_{g(u) h}‖_∞ ≤ (1+|u|²)^{-(n+3)/4} C` for every `u` and every `h` in the maximal compact. -/
theorem goodLine_cuspSupNorm_decay (D : InducingData n) {f : AdelicGL → ℂ}
    (hf : IsInduced D .plane cohomologicalPoint f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (h : AdelicGL), inMaximalCompact h →
      CuspSupNorm.cuspSupNorm (CuspVectors.planeCuspVector hf
        (atInfinity (SphericalDetection.Helpers.standardGoodLineRealArgument u) * h)) ≤
      (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  obtain ⟨C, hC0, hC⟩ := AnalyticScalar.maximalCompact_bound hf (continuousStages D)
  refine ⟨C, hC0, fun u h hh => ?_⟩
  obtain ⟨p, k, hk, hg, hsq, hdet⟩ := ArchimedeanConstant.goodLine_iwasawa u
  obtain ⟨a, b, s, B, hp⟩ := SphericalDetection.Helpers.planeParabolic_exists_decomposition p
  have hY := hC _ (inMaximalCompact_atInfinity_mul hk hh)
  have hsplit : atInfinity (SphericalDetection.Helpers.standardGoodLineRealArgument u) * h =
      planeUnipotent ((a, 0) : Adeles) ((b, 0) : Adeles) *
        (planeLevi 1 (realAdeleUnit s) *
          (planeLevi (atInfinity B) 1 * (atInfinity k * h))) := by
    rw [hg, hp, EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_mul,
      EisensteinRegularization.Helpers.atInfinity_planeUnipotent,
      EisensteinRegularization.Helpers.atInfinity_planeLevi,
      EisensteinRegularization.Helpers.atInfinity_planeLevi]
    have h1 : atInfinity (1 : BinaryRealGL) = 1 := by
      apply Units.ext
      refine Matrix.ext fun i j => Prod.ext ?_ ?_ <;> by_cases hij : i = j <;>
        simp [atInfinity, combineGL, pairMatrix, hij]
    have h2 : realAdeleUnit (1 : ℝˣ) = 1 := by
      apply Units.ext; rfl
    rw [h1, h2]
    simp only [mul_assoc]
  rw [hsplit, CuspVectors.planeCuspVector_unipotent, CuspVectors.planeCuspVector_scalar,
    CuspSupNorm.cuspSupNorm_smul, CuspVectors.planeCuspVector_binaryLevi,
    CuspSupNorm.cuspSupNorm_smul, CuspSupNorm.cuspSupNorm_translate]
  -- the scalar factor has norm one
  have hscalar : ‖D.chi.toMonoidHom (realAdeleUnit s) *
      normPower (realAdeleUnit s) (-2 * inductionExponent .plane cohomologicalPoint)‖ = 1 := by
    rw [ArchimedeanConstant.plane_exponent_cohomological, mul_zero,
      SphericalDetection.Helpers.normPower_zero_exponent, mul_one, D.chi.unitary]
  -- the block determinant
  have hval : p.val.val = (planeUnipotent a b * (planeLevi 1 s * planeLevi B 1)).val := by
    rw [hp]
  have hentries : p.val.val 0 0 * p.val.val 1 1 - p.val.val 0 1 * p.val.val 1 0 = B.val.det ∧
      p.val.val 2 2 = s.val := by
    rw [hval]
    refine ⟨?_, ?_⟩ <;>
      simp [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.det_fin_two]
  have hpos : (0 : ℝ) < 1 + u.1 ^ 2 + u.2 ^ 2 := by positivity
  have h22 : |p.val.val 2 2| = Real.sqrt (1 + u.1 ^ 2 + u.2 ^ 2) := by
    rw [← hsq, Real.sqrt_sq_eq_abs]
  have hBdet : |B.val.det| = (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(1 / 2 : ℝ)) := by
    have e1 : |B.val.det| * Real.sqrt (1 + u.1 ^ 2 + u.2 ^ 2) = 1 := by
      rw [← h22, ← hentries.1]; exact hdet
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow]
    exact eq_inv_of_mul_eq_one_left e1
  have hlevi : ‖normPower (GeneralLinearGroup.det (atInfinity B))
      (binaryInductionExponent n .plane cohomologicalPoint)‖ =
      (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) := by
    rw [Helpers.norm_normPower,
      EisensteinRegularization.Helpers.det_atInfinity_binary,
      EisensteinRegularization.Helpers.adeleNorm_realAdeleUnit]
    have hexp : (binaryInductionExponent n .plane cohomologicalPoint).re = ((n : ℝ) + 3) / 2 := by
      simp only [binaryInductionExponent, ArchimedeanConstant.plane_exponent_cohomological, add_zero]
      simp
    rw [hexp]
    change Real.exp (((n : ℝ) + 3) / 2 * Real.log |B.val.det|) = _
    have hBpos : 0 < |B.val.det| := by
      rw [hBdet]; exact Real.rpow_pos_of_pos hpos _
    rw [mul_comm, ← Real.rpow_def_of_pos hBpos, hBdet, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [hscalar, one_mul, hlevi]
  exact mul_le_mul_of_nonneg_left hY (Real.rpow_nonneg hpos.le _)

end TernaryPeriodPolynomials.AnalyticClasses
