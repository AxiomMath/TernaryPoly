module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FiniteFamilyBounds
public import TernaryPeriodPolynomials.EisensteinSeries.ArchimedeanConstant.KernelAnalytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedContinuation

@[expose] public section


/-!
# The good-line mixed coordinate at the cohomological point is a literal integral

For Re s large, the mixed good-line coordinate of the continued standard family is the
iterated real-and-finite integral of the actual source cusp values
(`goodLineMixedRealCoordinate_finite_vector_continuation`). With the uniform decay of
`SourceValueBounds` and the holomorphic finite families of `FiniteFamilyBounds`, the integrand is
dominated on a half-plane containing the cohomological point, so the meromorphic continuation at
`s = -3/2` equals the absolutely convergent literal integral.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Metric Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

section Integrability

/-- `(1 + |u|²)^(-2)` is integrable on the plane. -/
theorem kernelBase_rpow_neg_two_integrable :
    Integrable (fun u : ℝ × ℝ => kernelBase u ^ (-2 : ℝ)) := by
  have base : Integrable (fun u : ℝ × ℝ => (1 + ‖u‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine (base.const_mul 4).mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact (Continuous.rpow_const (by unfold kernelBase; fun_prop)
      (fun u => Or.inl (kernelBase_pos u).ne')).aestronglyMeasurable
  · have hpos := kernelBase_pos u
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
    have hm : 0 ≤ ‖u‖ := norm_nonneg _
    have hsq : (1 + ‖u‖) ^ 2 ≤ 2 * kernelBase u := by
      have h1 : |u.1| ≤ ‖u‖ := by simpa using norm_fst_le u
      have h2 : |u.2| ≤ ‖u‖ := by simpa using norm_snd_le u
      have hmax : ‖u‖ = max ‖u.1‖ ‖u.2‖ := Prod.norm_def u
      have hsq' : ‖u‖ ^ 2 ≤ u.1 ^ 2 + u.2 ^ 2 := by
        rcases le_total ‖u.1‖ ‖u.2‖ with h | h
        · rw [hmax, max_eq_right h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg u.1]
        · rw [hmax, max_eq_left h, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg u.2]
      unfold kernelBase
      nlinarith [sq_nonneg (1 - ‖u‖)]
    have hpos' : 0 < (1 + ‖u‖) := by linarith
    -- kernelBase^(-2) ≤ ((1+m)^2/2)^(-2) = 4 (1+m)^(-4)
    have step : kernelBase u ^ (-2 : ℝ) ≤ ((1 + ‖u‖) ^ 2 / 2) ^ (-2 : ℝ) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    refine step.trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul hpos'.le]
    rw [show (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 by norm_num [Real.rpow_neg, Real.rpow_two]]
    norm_num
    ring_nf

end Integrability

section Family

variable (data : InducingData n) (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
  (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ)

/-- The spherical test vector of the mixed good-line cusp values at `g(u)`. -/
def mixedTestVector (u : ℝ × ℝ) : data.cusp.smooth :=
  cuspidalTensorFunctional data.cusp functional
    (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity (standardGoodLineRealArgument u)))

theorem mixedTestVector_spherical (u : ℝ × ℝ) :
    (mixedTestVector data source cocycle matrix functional u).val ∈ cuspSphericalValues data.cusp :=
  goodLineMixedCuspidalValues_functional_spherical data source cocycle matrix _ functional

/-- The finite integrand values in exponential coordinates. -/
def mixedFiniteValue (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) : ℂ :=
  data.cusp.realize (mixedTestVector data source cocycle matrix functional pair.1)
    (atFinite (standardGoodLineFinitePadicCoordinates pair.2).block)

theorem cuspidalProductIntegrand_eq (s : ℂ) (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) :
    goodLineCuspidalProductIntegrand data source cocycle s matrix functional pair =
      standardGoodLineRealKernel s pair.1 *
        (Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm pair.2 : ℂ)) *
          mixedFiniteValue data source cocycle matrix functional pair) := by
  rw [goodLineCuspidalProductIntegrand]
  congr 1
  rw [← cuspidalTensorFunctional_realize]
  exact (goodLineFinitePadicIntegrand_eq n data.cusp s _
    (mixedTestVector_spherical data source cocycle matrix functional pair.1) pair.2).trans
      (goodLineFinitePadicIntegrand_eq_exp data.cusp _ _ pair.2)

/-- The finite integral as a function of the real coordinate. -/
def mixedFiniteFamily (s : ℂ) (u : ℝ × ℝ) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp s (mixedTestVector data source cocycle matrix functional u)

theorem mixedFiniteFamily_eq (s : ℂ) (u : ℝ × ℝ) :
    mixedFiniteFamily data source cocycle matrix functional s u =
      ∫ f, Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm f : ℂ)) *
        mixedFiniteValue data source cocycle matrix functional (u, f)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  goodLineFiniteVectorIntegral_eq_exp data.cusp s _
    (mixedTestVector_spherical data source cocycle matrix functional u)

/-- Product measurability of the finite values, from the integrability of the actual
standard integrand at one large parameter. -/
theorem mixedFiniteValue_aestronglyMeasurable (s₁ : ℂ)
    (integrable : Integrable (goodLineCuspidalProductIntegrand data source cocycle s₁ matrix functional)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) :
    AEStronglyMeasurable (mixedFiniteValue data source cocycle matrix functional)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
  have hL : AEMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      goodLineFiniteLogNorm pair.2)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    goodLineFiniteLogNorm_aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hfactor : AEStronglyMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      (standardGoodLineRealKernel s₁ pair.1 *
        Complex.exp (finiteExponent n s₁ * (goodLineFiniteLogNorm pair.2 : ℂ)))⁻¹)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.inv
    apply AEMeasurable.mul
    · exact ((kernel_continuous s₁).comp continuous_fst).aemeasurable
    · exact (Complex.measurable_exp.comp_aemeasurable
        (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable hL)))
  have equality : mixedFiniteValue data source cocycle matrix functional =
      fun pair => goodLineCuspidalProductIntegrand data source cocycle s₁ matrix functional pair *
        (standardGoodLineRealKernel s₁ pair.1 *
          Complex.exp (finiteExponent n s₁ * (goodLineFiniteLogNorm pair.2 : ℂ)))⁻¹ := by
    funext pair
    rw [cuspidalProductIntegrand_eq, ← mul_assoc, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (standardGoodLineRealKernel_ne_zero _ _) (Complex.exp_ne_zero _)),
      one_mul]
  rw [equality]
  exact integrable.aestronglyMeasurable.mul hfactor

theorem mixedFiniteFamily_aestronglyMeasurable (s₁ : ℂ)
    (integrable : Integrable (goodLineCuspidalProductIntegrand data source cocycle s₁ matrix functional)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)))
    (s : ℂ) :
    AEStronglyMeasurable (mixedFiniteFamily data source cocycle matrix functional s)
      ((volume : Measure ℝ).prod volume) := by
  have hL : AEMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      goodLineFiniteLogNorm pair.2)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    goodLineFiniteLogNorm_aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hF : AEStronglyMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm pair.2 : ℂ)) *
        mixedFiniteValue data source cocycle matrix functional pair)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    (Complex.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable hL))).aestronglyMeasurable.mul
      (mixedFiniteValue_aestronglyMeasurable data source cocycle matrix functional s₁ integrable)
  have key := hF.integral_prod_right'
  have equality : mixedFiniteFamily data source cocycle matrix functional s = fun u =>
      ∫ f, Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm f : ℂ)) *
        mixedFiniteValue data source cocycle matrix functional (u, f)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    funext u
    exact mixedFiniteFamily_eq data source cocycle matrix functional s u
  rw [equality]
  exact key

end Family

/-- Difference quotients along `1/(k+1)` converge to the derivative. -/
theorem tendsto_slope_seq {f : ℂ → ℂ} {f' : ℂ} {s : ℂ} (h : HasDerivAt f f' s) :
    Tendsto (fun k : ℕ => ((1 : ℂ) / ((k : ℂ) + 1))⁻¹ * (f (s + (1 : ℂ) / ((k : ℂ) + 1)) - f s))
      atTop (𝓝 f') := by
  have slope := hasDerivAt_iff_tendsto_slope_zero.mp h
  have seq : Tendsto (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have hreal : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
      simpa [Function.comp_def] using hcast
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero k
  simpa only [smul_eq_mul, Function.comp_def] using slope.comp seq

/-- Parameter derivatives of measurable holomorphic families are measurable. -/
theorem aestronglyMeasurable_deriv {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℂ → α → ℂ} (meas : ∀ s, AEStronglyMeasurable (F s) μ) (s : ℂ)
    (h : ∀ u, HasDerivAt (fun z => F z u) (deriv (fun z => F z u) s) s) :
    AEStronglyMeasurable (fun u => deriv (fun z => F z u) s) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (k : ℕ) (u : α) =>
    ((1 : ℂ) / ((k : ℂ) + 1))⁻¹ * (F (s + (1 : ℂ) / ((k : ℂ) + 1)) u - F s u)) ?_ ?_
  · intro k
    exact ((meas _).sub (meas s)).const_mul _
  · refine Eventually.of_forall fun u => ?_
    have := tendsto_slope_seq (h u)
    exact this

/-- **The mixed good-line coordinate at the cohomological point is the literal integral.**
At `s = -3/2` the meromorphic continuation of the mixed coordinate equals the absolutely
convergent real integral of the finite good-line integrals of the actual source cusp values. -/
theorem mixedReal_endpoint_eq_integral (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
    (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (standard parameter vertices argument).val.coeff monomial))
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial)
        cohomologicalPoint)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    functional (goodLineMixedRealCoordinate n matrix (goodLineComplementFamily standard cohomologicalPoint)) =
      ∫ u : ℝ × ℝ, mixedFiniteFamily data source cocycle matrix functional cohomologicalPoint u := by
  have endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (flat cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]; exact support
  obtain ⟨meromorphic, threshold, formula⟩ := goodLineMixedRealCoordinate_continuation local_entry data flat
    standard sections endpoint_support continuations matrix functional
  obtain ⟨threshold', agreement⟩ := goodLineMixedRealCoordinate_finite_vector_continuation local_entry data
    trivial source cocycle flat standard sections endpoint support continuations matrix functional
  set s₁ : ℂ := ((max threshold 0 + 1 : ℝ) : ℂ) with hs₁def
  have hs₁ : threshold < s₁.re := by
    rw [hs₁def, Complex.ofReal_re]; linarith [le_max_left threshold 0]
  have product : Integrable (goodLineCuspidalProductIntegrand data source cocycle s₁ matrix functional)
      (((volume : Measure ℝ).prod volume).prod (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    have lifted := awayRadicalJoin_measurePreserving.integrable_comp_of_integrable (formula s₁ hs₁).1
    have equality : ((fun away => functional (goodLineMixedRealCoordinate n matrix
        (fun vertices => standardGoodLineAwayPolynomial flat s₁ vertices away))) ∘ awayRadicalJoin) =
        goodLineCuspidalProductIntegrand data source cocycle s₁ matrix functional := by
      funext pair
      exact goodLineMixedAway_cuspidalProduct data trivial source cocycle flat sections endpoint s₁ matrix
        functional pair
    rwa [equality] at lifted
  obtain ⟨C, hC0, hC⟩ := mixedCuspidalValues_decay data source cocycle matrix functional
  obtain ⟨G, hG⟩ : ∃ G, G = mixedFiniteFamily data source cocycle matrix functional := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G' : ℂ → ℝ × ℝ → ℂ, G' = fun s u =>
      if 3 < (finiteExponent n s).re then deriv (fun z => G z u) s else 0 := ⟨_, rfl⟩
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast large
  have halfplane (s : ℂ) (hs : -(3 : ℝ) / 2 - 2 * 1 < s.re) : 4 < (finiteExponent n s).re := by
    rw [finiteExponent_re]; linarith
  have hasDeriv (s : ℂ) (u : ℝ × ℝ) (hs : 3 < (finiteExponent n s).re) :
      HasDerivAt (fun z => G z u) (deriv (fun z => G z u) s) s := by
    rw [hG]
    exact (goodLineFiniteVectorIntegral_analyticAt' data.cusp _
      (mixedTestVector_spherical data source cocycle matrix functional u) s hs).differentiableAt.hasDerivAt
  have meas (s : ℂ) : AEStronglyMeasurable (G s) (volume : Measure (ℝ × ℝ)) := by
    rw [hG]
    exact mixedFiniteFamily_aestronglyMeasurable data source cocycle matrix functional s₁ product s
  have meas' (s : ℂ) : AEStronglyMeasurable (G' s) (volume : Measure (ℝ × ℝ)) := by
    by_cases hs : 3 < (finiteExponent n s).re
    · have equality : G' s = fun u => deriv (fun z => G z u) s := by
        funext u; rw [hG']; simp only [ite_eq_left hs]
      rw [equality]
      exact aestronglyMeasurable_deriv meas s (fun u => hasDeriv s u hs)
    · have equality : G' s = fun _ => 0 := by
        funext u; rw [hG']; simp only [ite_eq_right hs]
      rw [equality]
      exact aestronglyMeasurable_const
  have derivs (s : ℂ) (u : ℝ × ℝ) (hs : -(3 : ℝ) / 2 - 2 * 1 < s.re) :
      HasDerivAt (fun z => G z u) (G' s u) s := by
    have h3 : 3 < (finiteExponent n s).re := by linarith [halfplane s hs]
    rw [hG']
    simp only [ite_eq_left h3]
    exact hasDeriv s u h3
  have dominated : ∀ s₀ : ℂ, -(3 : ℝ) / 2 - 2 * 1 < s₀.re → ∃ ε > 0, ∃ b : ℝ × ℝ → ℝ,
      Integrable (fun u => kernelBase u ^ (1 : ℝ) * b u) (volume : Measure (ℝ × ℝ)) ∧
      ∀ u, ∀ s ∈ ball s₀ ε, ‖G s u‖ ≤ b u ∧ ‖G' s u‖ ≤ b u := by
    intro s₀ hs₀
    set e := (finiteExponent n s₀).re with he
    have he4 : 4 < e := halfplane s₀ hs₀
    set ρ := (e - 3) / 4 with hρ
    have hρpos : 0 < ρ := by rw [hρ]; linarith
    set M := weightMass (e - ρ) + weightMass (e + ρ) +
      (weightMass (e - 2 * ρ) + weightMass (e + 2 * ρ)) / ρ with hM
    have hM0 : 0 ≤ M := by
      have := weightMass_nonneg (e - ρ); have := weightMass_nonneg (e + ρ)
      have := weightMass_nonneg (e - 2 * ρ); have := weightMass_nonneg (e + 2 * ρ)
      positivity
    refine ⟨ρ, hρpos, fun u => M * ((1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C), ?_, ?_⟩
    · have base := (kernelBase_rpow_neg_two_integrable.const_mul (M * C))
      refine base.mono' ?_ (Eventually.of_forall fun u => ?_)
      · exact ((Continuous.rpow_const (by unfold kernelBase; fun_prop)
          (fun u => Or.inl (kernelBase_pos u).ne')).mul (continuous_const.mul
            ((Continuous.rpow_const (by fun_prop) (fun u => Or.inl (by positivity))).mul
              continuous_const))).aestronglyMeasurable
      · have hpos := kernelBase_pos u
        have hB : (1 + u.1 ^ 2 + u.2 ^ 2) = kernelBase u := rfl
        dsimp only
        rw [hB]
        rw [Real.norm_of_nonneg (by positivity)]
        have hexp : kernelBase u ^ (1 : ℝ) * kernelBase u ^ (-(((n : ℝ) + 3) / 4)) ≤
            kernelBase u ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hpos]
          exact Real.rpow_le_rpow_of_exponent_le (kernelBase_one_le u) (by linarith)
        calc kernelBase u ^ (1 : ℝ) * (M * (kernelBase u ^ (-(((n : ℝ) + 3) / 4)) * C)) =
            (M * C) * (kernelBase u ^ (1 : ℝ) * kernelBase u ^ (-(((n : ℝ) + 3) / 4))) := by ring
          _ ≤ (M * C) * kernelBase u ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hM0 hC0)
    · intro u s hs
      have hsc : s ∈ closedBall s₀ ρ := ball_subset_closedBall hs
      have hD0 : 0 ≤ (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) hC0
      have bounded := hC u
      have b1 := norm_goodLineFiniteVectorIntegral_le_ball data.cusp s₀ ρ (by rw [← he]; linarith) _
        (mixedTestVector_spherical data source cocycle matrix functional u) _ hD0 bounded s hsc
      have hre : |s.re - s₀.re| ≤ ρ := by
        calc |s.re - s₀.re| = |(s - s₀).re| := by simp
          _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
          _ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hsc
      have h3 : 3 < (finiteExponent n s).re := by
        rw [finiteExponent_re]; rw [he, finiteExponent_re] at hρ
        have := (abs_le.mp hre).1
        rw [he, finiteExponent_re] at he4
        linarith
      have b2 := norm_deriv_goodLineFiniteVectorIntegral_le data.cusp s₀ ρ hρpos (by rw [← he]; linarith) _
        (mixedTestVector_spherical data source cocycle matrix functional u) _ hD0 bounded s hsc
      have w1 := weightMass_nonneg (e - ρ); have w2 := weightMass_nonneg (e + ρ)
      have w3 := weightMass_nonneg (e - 2 * ρ); have w4 := weightMass_nonneg (e + 2 * ρ)
      rw [hG', hG]
      simp only [ite_eq_left h3]
      constructor
      · refine b1.trans ?_
        rw [← he]
        apply mul_le_mul_of_nonneg_right _ hD0
        rw [hM]
        have : 0 ≤ (weightMass (e - 2 * ρ) + weightMass (e + 2 * ρ)) / ρ := by positivity
        linarith
      · refine b2.trans ?_
        rw [← he, mul_div_right_comm]
        apply mul_le_mul_of_nonneg_right _ hD0
        rw [hM]
        linarith
  have hJ : MeromorphicOn (fun s => functional (goodLineMixedRealCoordinate n matrix
      (goodLineComplementFamily standard s))) {s : ℂ | -(3 : ℝ) / 2 - 2 * 1 < s.re} :=
    fun s _ => meromorphic s
  have agree : ∀ s : ℂ, threshold' < s.re →
      functional (goodLineMixedRealCoordinate n matrix (goodLineComplementFamily standard s)) =
        ∫ u, standardGoodLineRealKernel s u * G s u := by
    intro s hs; rw [hG]; exact (agreement s hs).2
  rw [← hG]
  exact continuation_eq_integral_family G G' 1 one_pos meas meas' derivs dominated _ hJ threshold' agree
    (goodLineMixedRealCoordinate_analytic standard analytic matrix functional)

end TernaryPeriodPolynomials.AnalyticClasses
