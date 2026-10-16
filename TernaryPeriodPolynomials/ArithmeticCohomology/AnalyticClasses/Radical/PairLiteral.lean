module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.MixedEndpointIntegral

@[expose] public section


/-!
# One good-line simplex at the cohomological point is a literal integral

The per-simplex analogue of `mixedReal_endpoint_eq_integral`. For a fixed vertex triple `V` and
a linear functional `ℓ` on the coefficients, Codexiom's functional continuation of the
complementary good-line family, the finite-vector Fubini identity and the uniform decay of the
source cusp values show that, at `s = -3/2`,

`ℓ(complement(V)) = ∫_u FinAvg(ℓ̃ (source cusp values on V at g(u))) du`,

an absolutely convergent literal integral. Specialized to the radical simplices
`(1, r₁, r₁ r₂)` of the good-line stabilizer.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Metric Filter Topology

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.ArchimedeanConstant

variable {n : ℕ}

section Family

variable (data : InducingData n) (source : SourceCochain n)
  (cocycle : IsSourceCocycle data .plane source) (V : Fin 3 → RealGL3)
  (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)

/-- The spherical test vector of the source cusp values on one simplex at `g(u)`. -/
def simplexTestVector (u : ℝ × ℝ) : data.cusp.smooth :=
  cuspidalTensorFunctional data.cusp functional
    (sourcePlaneCuspidalValues data source cocycle V (atInfinity (standardGoodLineRealArgument u)))

theorem simplexTestVector_spherical (u : ℝ × ℝ) :
    (simplexTestVector data source cocycle V functional u).val ∈ cuspSphericalValues data.cusp :=
  cuspidalTensorFunctional_spherical data.cusp functional _
    (sourcePlaneCuspidalValues_finiteLevel data source cocycle V _)

/-- The finite integrand values of one simplex in exponential coordinates. -/
def simplexFiniteValue (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) : ℂ :=
  data.cusp.realize (simplexTestVector data source cocycle V functional pair.1)
    (atFinite (standardGoodLineFinitePadicCoordinates pair.2).block)

/-- The real-and-finite product integrand of one simplex. -/
def simplexProductIntegrand (s : ℂ) (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) : ℂ :=
  standardGoodLineRealKernel s pair.1 *
    (standardGoodLineFiniteCuspWeight n s pair.2 *
      functional ((sourcePlaneCuspidalValues data source cocycle V
        (atInfinity (standardGoodLineRealArgument pair.1))).val
          (atFinite (standardGoodLineFiniteCoordinates pair.2).block)))

theorem simplexProductIntegrand_eq (s : ℂ)
    (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) :
    simplexProductIntegrand data source cocycle V functional s pair =
      standardGoodLineRealKernel s pair.1 *
        (Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm pair.2 : ℂ)) *
          simplexFiniteValue data source cocycle V functional pair) := by
  rw [simplexProductIntegrand]
  congr 1
  rw [← cuspidalTensorFunctional_realize]
  exact (goodLineFinitePadicIntegrand_eq n data.cusp s _
    (simplexTestVector_spherical data source cocycle V functional pair.1) pair.2).trans
      (goodLineFinitePadicIntegrand_eq_exp data.cusp _ _ pair.2)

/-- The finite integral of one simplex as a function of the real coordinate. -/
def simplexFiniteFamily (s : ℂ) (u : ℝ × ℝ) : ℂ :=
  goodLineFiniteVectorIntegral n data.cusp s (simplexTestVector data source cocycle V functional u)

theorem simplexFiniteFamily_eq (s : ℂ) (u : ℝ × ℝ) :
    simplexFiniteFamily data source cocycle V functional s u =
      ∫ f, Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm f : ℂ)) *
        simplexFiniteValue data source cocycle V functional (u, f)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  goodLineFiniteVectorIntegral_eq_exp data.cusp s _
    (simplexTestVector_spherical data source cocycle V functional u)

/-- Product measurability of the finite values, from integrability of the product integrand. -/
theorem simplexFiniteValue_aestronglyMeasurable (s₁ : ℂ)
    (integrable : Integrable (simplexProductIntegrand data source cocycle V functional s₁)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) :
    AEStronglyMeasurable (simplexFiniteValue data source cocycle V functional)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
  have hL : AEMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      goodLineFiniteLogNorm pair.2)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    goodLineFiniteLogNorm_aemeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hfactor : AEStronglyMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      (standardGoodLineRealKernel s₁ pair.1 *
        Complex.exp (finiteExponent n s₁ * (goodLineFiniteLogNorm pair.2 : ℂ)))⁻¹)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.inv
    apply AEMeasurable.mul
    · exact ((kernel_continuous s₁).comp continuous_fst).aemeasurable
    · exact (Complex.measurable_exp.comp_aemeasurable
        (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable hL)))
  have equality : simplexFiniteValue data source cocycle V functional =
      fun pair => simplexProductIntegrand data source cocycle V functional s₁ pair *
        (standardGoodLineRealKernel s₁ pair.1 *
          Complex.exp (finiteExponent n s₁ * (goodLineFiniteLogNorm pair.2 : ℂ)))⁻¹ := by
    funext pair
    rw [simplexProductIntegrand_eq, ← mul_assoc, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (standardGoodLineRealKernel_ne_zero _ _)
        (Complex.exp_ne_zero _)), one_mul]
  rw [equality]
  exact integrable.aestronglyMeasurable.mul hfactor

theorem simplexFiniteFamily_aestronglyMeasurable (s₁ : ℂ)
    (integrable : Integrable (simplexProductIntegrand data source cocycle V functional s₁)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)))
    (s : ℂ) :
    AEStronglyMeasurable (simplexFiniteFamily data source cocycle V functional s)
      ((volume : Measure ℝ).prod volume) := by
  have hL : AEMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      goodLineFiniteLogNorm pair.2)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    goodLineFiniteLogNorm_aemeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hF : AEStronglyMeasurable (fun pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree) =>
      Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm pair.2 : ℂ)) *
        simplexFiniteValue data source cocycle V functional pair)
      (((volume : Measure ℝ).prod volume).prod
        (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :=
    (Complex.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul
        (Complex.measurable_ofReal.comp_aemeasurable hL))).aestronglyMeasurable.mul
      (simplexFiniteValue_aestronglyMeasurable data source cocycle V functional s₁ integrable)
  have equality : simplexFiniteFamily data source cocycle V functional s = fun u =>
      ∫ f, Complex.exp (finiteExponent n s * (goodLineFiniteLogNorm f : ℂ)) *
        simplexFiniteValue data source cocycle V functional (u, f)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    funext u
    exact simplexFiniteFamily_eq data source cocycle V functional s u
  rw [equality]
  exact hF.integral_prod_right'

/-- The away-three integrand of one simplex is the product integrand. -/
theorem simplexAway_cuspidalProduct (trivial : data.chi = trivialCharacter)
    (flat : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source) (s : ℂ)
    (pair : (ℝ × ℝ) × (FiniteAwayThree × FiniteAwayThree)) :
    functional (standardGoodLineAwayPolynomial flat s V (awayRadicalJoin pair)) =
      simplexProductIntegrand data source cocycle V functional s pair := by
  have value : standardGoodLineAwayPolynomial flat s V (awayRadicalJoin pair) =
      (standardGoodLineRealKernel s pair.1 * standardGoodLineFiniteCuspWeight n s pair.2) •
        (sourcePlaneCuspidalValues data source cocycle V
          (atInfinity (standardGoodLineRealArgument pair.1))).val
            (atFinite (standardGoodLineFiniteCoordinates pair.2).block) := by
    change flat s V (weyl⁻¹ * lineUnipotent (adeleAwayThreeScalar (awayRadicalJoin pair).1)
      (adeleAwayThreeScalar (awayRadicalJoin pair).2) * rationalGroup rationalGoodLine) = _
    exact (congrArg (flat s V) (standardGoodLineArgument_combine pair.1 pair.2)).trans
      (polynomialFlatSection_standardGoodLine_cuspidal data trivial source cocycle flat sections
        endpoint s V pair.1 pair.2)
  rw [value, map_smul, smul_eq_mul, simplexProductIntegrand, mul_assoc]

/-- The standard continuation of one simplex is the real kernel applied to finite averages of
actual spherical cusp vectors, and the product integrand is integrable. -/
theorem simplex_finite_vector_continuation (local_entry : LocalBadPlaneEntry)
    (trivial : data.chi = trivialCharacter) (flat standard : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument =>
        (standard parameter vertices argument).val.coeff monomial)) :
    (∀ s, MeromorphicAt (fun s => functional (goodLineComplementFamily standard s V)) s) ∧
    ∃ threshold : ℝ, ∀ s : ℂ, threshold < s.re →
      Integrable (simplexProductIntegrand data source cocycle V functional s)
        (((volume : Measure ℝ).prod volume).prod
          (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) ∧
      functional (goodLineComplementFamily standard s V) =
        ∫ u, standardGoodLineRealKernel s u *
          simplexFiniteFamily data source cocycle V functional s u
          ∂((volume : Measure ℝ).prod volume) := by
  have endpoint_support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument =>
        (flat cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]
    exact support
  obtain ⟨meromorphic, threshold, formula⟩ := goodLineComplementFamily_functional_continuation
    local_entry data flat standard sections endpoint_support continuations V functional
  refine ⟨meromorphic, threshold, fun s hs => ?_⟩
  obtain ⟨integrable, value⟩ := formula s hs
  have lifted := awayRadicalJoin_measurePreserving.integrable_comp_of_integrable integrable
  have equality : ((fun away => functional (standardGoodLineAwayPolynomial flat s V away)) ∘
      awayRadicalJoin) = simplexProductIntegrand data source cocycle V functional s := by
    funext pair
    exact simplexAway_cuspidalProduct data source cocycle V functional trivial flat sections
      endpoint s pair
  rw [equality] at lifted
  refine ⟨lifted, ?_⟩
  have inner : (fun u : ℝ × ℝ => ∫ f,
      simplexProductIntegrand data source cocycle V functional s (u, f)
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) =
      fun u => standardGoodLineRealKernel s u *
        simplexFiniteFamily data source cocycle V functional s u := by
    funext u
    simp only [simplexProductIntegrand, simplexFiniteFamily, goodLineFiniteVectorIntegral,
      simplexTestVector, cuspidalTensorFunctional_realize]
    rw [integral_const_mul]
  rw [value, ← awayRadicalJoin_measurePreserving.integral_comp
    awayRadicalJoin.measurableEmbedding]
  change (∫ pair, (((fun away => functional (standardGoodLineAwayPolynomial flat s V away)) ∘
    awayRadicalJoin) pair) ∂(((volume : Measure ℝ).prod volume).prod
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure))) = _
  rw [equality, integral_prod _ lifted]
  exact congrArg (fun function : (ℝ × ℝ) → ℂ =>
    ∫ u, function u ∂((volume : Measure ℝ).prod volume)) inner

/-- Uniform decay of the scalar tests of one simplex. -/
theorem simplexTestVector_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (argument : BinaryAdelicGL),
      ‖data.cusp.realize (simplexTestVector data source cocycle V functional u) argument‖ ≤
        (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  obtain ⟨C, hC0, hC⟩ := sourceCuspidalValues_functional_decay data source cocycle V functional
  refine ⟨C, hC0, fun u argument => ?_⟩
  rw [simplexTestVector, cuspidalTensorFunctional_realize]
  exact hC u argument

end Family

/-- **One good-line simplex at the cohomological point is the literal integral.** At
`s = -3/2` the meromorphic continuation of a scalar test of the complementary good-line family on
a fixed simplex equals the absolutely convergent real integral of the finite good-line averages
of the actual source cusp values on that simplex. -/
theorem simplex_endpoint_eq_integral (large : 9 ≤ n) (local_entry : LocalBadPlaneEntry)
    (data : InducingData n) (trivial : data.chi = trivialCharacter)
    (source : SourceCochain n) (cocycle : IsSourceCocycle data .plane source)
    (flat standard : ℂ → SourceCochain n)
    (sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument =>
        (flat parameter vertices argument).val.coeff monomial))
    (endpoint : flat cohomologicalPoint = source)
    (support : ∀ vertices monomial, LocalThreePlaneSupport
      (fun argument => (source vertices argument).val.coeff monomial))
    (continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument =>
        (standard parameter vertices argument).val.coeff monomial))
    (analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (standard parameter vertices argument).val.coeff monomial)
        cohomologicalPoint)
    (V : Fin 3 → RealGL3) (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    functional (goodLineComplementFamily standard cohomologicalPoint V) =
      ∫ u : ℝ × ℝ, simplexFiniteFamily data source cocycle V functional cohomologicalPoint u := by
  obtain ⟨meromorphic, threshold, formula⟩ := simplex_finite_vector_continuation data source
    cocycle V functional local_entry trivial flat standard sections endpoint support continuations
  set s₁ : ℂ := ((max threshold 0 + 1 : ℝ) : ℂ) with hs₁def
  have hs₁ : threshold < s₁.re := by
    rw [hs₁def, Complex.ofReal_re]; linarith [le_max_left threshold 0]
  have product := (formula s₁ hs₁).1
  obtain ⟨C, hC0, hC⟩ := simplexTestVector_decay data source cocycle V functional
  obtain ⟨G, hG⟩ : ∃ G, G = simplexFiniteFamily data source cocycle V functional := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G' : ℂ → ℝ × ℝ → ℂ, G' = fun s u =>
      if 3 < (finiteExponent n s).re then deriv (fun z => G z u) s else 0 := ⟨_, rfl⟩
  have hn : (9 : ℝ) ≤ n := by exact_mod_cast large
  have halfplane (s : ℂ) (hs : -(3 : ℝ) / 2 - 2 * 1 < s.re) : 4 < (finiteExponent n s).re := by
    rw [finiteExponent_re]; linarith
  have hasDeriv (s : ℂ) (u : ℝ × ℝ) (hs : 3 < (finiteExponent n s).re) :
      HasDerivAt (fun z => G z u) (deriv (fun z => G z u) s) s := by
    rw [hG]
    exact (goodLineFiniteVectorIntegral_analyticAt' data.cusp _
      (simplexTestVector_spherical data source cocycle V functional u) s
        hs).differentiableAt.hasDerivAt
  have meas (s : ℂ) : AEStronglyMeasurable (G s) (volume : Measure (ℝ × ℝ)) := by
    rw [hG]
    exact simplexFiniteFamily_aestronglyMeasurable data source cocycle V functional s₁ product s
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
    refine ⟨ρ, hρpos, fun u => M * ((1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C),
      ?_, ?_⟩
    · have base := (kernelBase_rpow_neg_two_integrable.const_mul (M * C))
      refine base.mono' ?_ (Eventually.of_forall fun u => ?_)
      · exact ((Continuous.rpow_const (by unfold kernelBase; fun_prop)
          (fun u => Or.inl (kernelBase_pos u).ne')).mul (continuous_const.mul
            ((Continuous.rpow_const (by fun_prop) (fun u => Or.inl (by positivity))).mul
              continuous_const))).aestronglyMeasurable
      · have hpos := kernelBase_pos u
        have hB : (1 + u.1 ^ 2 + u.2 ^ 2) = kernelBase u := rfl
        dsimp only
        rw [hB, Real.norm_of_nonneg (by positivity)]
        have hexp : kernelBase u ^ (1 : ℝ) * kernelBase u ^ (-(((n : ℝ) + 3) / 4)) ≤
            kernelBase u ^ (-2 : ℝ) := by
          rw [← Real.rpow_add hpos]
          exact Real.rpow_le_rpow_of_exponent_le (kernelBase_one_le u) (by linarith)
        calc kernelBase u ^ (1 : ℝ) * (M * (kernelBase u ^ (-(((n : ℝ) + 3) / 4)) * C)) =
            (M * C) * (kernelBase u ^ (1 : ℝ) * kernelBase u ^ (-(((n : ℝ) + 3) / 4))) := by
              ring
          _ ≤ (M * C) * kernelBase u ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg hM0 hC0)
    · intro u s hs
      have hsc : s ∈ closedBall s₀ ρ := ball_subset_closedBall hs
      have hD0 : 0 ≤ (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C :=
        mul_nonneg (Real.rpow_nonneg (by positivity) _) hC0
      have bounded := hC u
      have b1 := norm_goodLineFiniteVectorIntegral_le_ball data.cusp s₀ ρ
        (by rw [← he]; linarith) _ (simplexTestVector_spherical data source cocycle V functional u)
        _ hD0 bounded s hsc
      have hre : |s.re - s₀.re| ≤ ρ := by
        calc |s.re - s₀.re| = |(s - s₀).re| := by simp
          _ ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
          _ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.mp hsc
      have h3 : 3 < (finiteExponent n s).re := by
        rw [finiteExponent_re]; rw [he, finiteExponent_re] at hρ
        have := (abs_le.mp hre).1
        rw [he, finiteExponent_re] at he4
        linarith
      have b2 := norm_deriv_goodLineFiniteVectorIntegral_le data.cusp s₀ ρ hρpos
        (by rw [← he]; linarith) _ (simplexTestVector_spherical data source cocycle V functional u)
        _ hD0 bounded s hsc
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
  have hJ : MeromorphicOn (fun s => functional (goodLineComplementFamily standard s V))
      {s : ℂ | -(3 : ℝ) / 2 - 2 * 1 < s.re} :=
    fun s _ => meromorphic s
  have agree : ∀ s : ℂ, threshold < s.re →
      functional (goodLineComplementFamily standard s V) =
        ∫ u, standardGoodLineRealKernel s u * G s u := by
    intro s hs; rw [hG]; exact (formula s hs).2
  rw [← hG]
  exact continuation_eq_integral_family G G' 1 one_pos meas meas' derivs dominated _ hJ threshold
    agree (goodLineComplementFamily_functional_analytic standard analytic V functional)

end TernaryPeriodPolynomials.AnalyticClasses
