module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FinitePeriodDetection

@[expose] public section


/-!
# The finite good-line average of binary-valued functions

For a function `f : GL₂(𝔸) → Sym^{n+1}` the finite good-line average is
`∑ⱼ (∫ ‖det b‖^s · coordⱼ (f b) d(f₁, f₂)) • eⱼ`, where `b = b(f₁, f₂)` is the block of the finite
plane coordinates of the finite radical pair `(f₁, f₂)` away from `3` and `eⱼ` is the weight basis.
It commutes with linear maps of the coefficients. The good-line integrand of a spherical vector
is locally constant in the finite pair, uniformly in the vector. Consequently the average of the
Eichler period of the scalar weighted realization of a classical vector `v` is the straight-line
integral of the finite average `cuspClassicalFiniteAverage v` of `v` along the path.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The average -/

/-- The block of the finite plane coordinates of a finite radical pair away from `3`. -/
def finiteAverageBlock (pair : FiniteAwayThree × FiniteAwayThree) : BinaryFiniteGL :=
  (finitePadicPlaneCoordinates pair.1.val pair.2.val).block

/-- The determinant weight `‖det b‖^s` of the finite good-line average. -/
def finiteAverageWeight (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) : ℂ :=
  normPower (GeneralLinearGroup.det (atFinite (finiteAverageBlock pair))) exponent

/-- **The finite good-line average** of a binary-valued function on `GL₂(𝔸)`, taken
coordinatewise in the weight basis. -/
def finiteAverageBinary (exponent : ℂ) (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    Binary.HomogeneousPoly (n + 1) :=
  ∑ j, (∫ pair, finiteAverageWeight exponent pair *
      (binaryWeightBasis (n + 1)).coord j (f (atFinite (finiteAverageBlock pair)))
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) • binaryWeightBasis (n + 1) j

/-- Integrability of every weighted coordinate of `f` along the finite good-line average. -/
def FiniteAverageIntegrable (exponent : ℂ)
    (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) : Prop :=
  ∀ j, Integrable (fun pair => finiteAverageWeight exponent pair *
    (binaryWeightBasis (n + 1)).coord j (f (atFinite (finiteAverageBlock pair))))
    (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

theorem goodLineFinitePadicIntegrand_eq_weight (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) :
    goodLineFinitePadicIntegrand cusp vector exponent pair =
      finiteAverageWeight exponent pair *
        cusp.realize vector (atFinite (finiteAverageBlock pair)) :=
  rfl

theorem coord_finiteAverageBinary (exponent : ℂ)
    (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) (j : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord j (finiteAverageBinary exponent f) =
      ∫ pair, finiteAverageWeight exponent pair *
        (binaryWeightBasis (n + 1)).coord j (f (atFinite (finiteAverageBlock pair)))
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  rw [finiteAverageBinary, Module.Basis.coord_apply, Module.Basis.repr_sum_self]

theorem FiniteAverageIntegrable.functional {exponent : ℂ}
    {f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (integrable : FiniteAverageIntegrable exponent f)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Integrable (fun pair => finiteAverageWeight exponent pair *
      functional (f (atFinite (finiteAverageBlock pair))))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have expansion : (fun pair => finiteAverageWeight exponent pair *
      functional (f (atFinite (finiteAverageBlock pair)))) = fun pair =>
      ∑ j, finiteAverageWeight exponent pair *
        (binaryWeightBasis (n + 1)).coord j (f (atFinite (finiteAverageBlock pair))) *
          functional (binaryWeightBasis (n + 1) j) := by
    funext pair
    rw [functional_eq_sum_coord functional, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expansion]
  exact integrable_finsetSum _ fun j _ => (integrable j).mul_const _

/-- A linear functional of the average is the average of the functional. -/
theorem functional_finiteAverageBinary {exponent : ℂ}
    {f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (integrable : FiniteAverageIntegrable exponent f)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    functional (finiteAverageBinary exponent f) =
      ∫ pair, finiteAverageWeight exponent pair *
        functional (f (atFinite (finiteAverageBlock pair)))
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have expansion : (fun pair => finiteAverageWeight exponent pair *
      functional (f (atFinite (finiteAverageBlock pair)))) = fun pair =>
      ∑ j, finiteAverageWeight exponent pair *
        (binaryWeightBasis (n + 1)).coord j (f (atFinite (finiteAverageBlock pair))) *
          functional (binaryWeightBasis (n + 1) j) := by
    funext pair
    rw [functional_eq_sum_coord functional, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [expansion, integral_finsetSum _ fun j _ => (integrable j).mul_const _,
    functional_eq_sum_coord functional]
  exact Finset.sum_congr rfl fun j _ => by rw [coord_finiteAverageBinary, integral_mul_const]

/-- The average of `L₁ ∘ f₁ - L₂ ∘ f₂` for linear maps `L₁`, `L₂` of the coefficients. -/
theorem finiteAverageBinary_map_sub {exponent : ℂ}
    {first second : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (first_integrable : FiniteAverageIntegrable exponent first)
    (second_integrable : FiniteAverageIntegrable exponent second)
    (left right : Module.End ℂ (Binary.HomogeneousPoly (n + 1))) :
    finiteAverageBinary exponent (fun h => left (first h) - right (second h)) =
      left (finiteAverageBinary exponent first) - right (finiteAverageBinary exponent second) := by
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, coord_finiteAverageBinary, map_sub]
  change _ = ((binaryWeightBasis (n + 1)).coord j ∘ₗ left) (finiteAverageBinary exponent first) -
    ((binaryWeightBasis (n + 1)).coord j ∘ₗ right) (finiteAverageBinary exponent second)
  rw [functional_finiteAverageBinary first_integrable,
    functional_finiteAverageBinary second_integrable,
    ← integral_sub (first_integrable.functional _) (second_integrable.functional _)]
  apply integral_congr_ae
  filter_upwards [] with pair
  simp only [map_sub, LinearMap.comp_apply, mul_sub]

/-! ### Local constancy of the finite integrand -/

theorem goodLineFinitePadicIntegrand_eq_comp (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) :
    goodLineFinitePadicIntegrand cusp vector exponent =
      finiteSphericalPlaneFunction cusp vector exponent ∘ standardGoodLineFiniteArgument := by
  funext pair
  have independent := finiteSphericalPlaneValue_independent cusp vector spherical exponent _
    (standardGoodLineFinitePadicCoordinates pair) (finitePlaneInductionCoordinates _)
  change normPower (GeneralLinearGroup.det
    (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) exponent *
    cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block) = _
  rw [binary_det_atFinite]
  exact independent

/-- **The finite good-line integrand is locally constant**, uniformly in the spherical vector. -/
theorem goodLineFinitePadicIntegrand_eventually_eq (cusp : CuspidalRepresentation)
    (exponent : ℂ) (base : FiniteAwayThree × FiniteAwayThree) :
    ∀ᶠ pair in nhds base, ∀ vector : cusp.smooth, vector.val ∈ cuspSphericalValues cusp →
      goodLineFinitePadicIntegrand cusp vector exponent pair =
        goodLineFinitePadicIntegrand cusp vector exponent base := by
  have near : ∀ᶠ pair in nhds base, (standardGoodLineFiniteArgument base)⁻¹ *
      standardGoodLineFiniteArgument pair ∈ finiteIntegralGLLevel 3 :=
    (continuous_const.mul standardGoodLineFiniteArgument_continuous).continuousAt.eventually
      ((finiteIntegralGLLevel_isOpen 3).mem_nhds (by
        change (standardGoodLineFiniteArgument base)⁻¹ * standardGoodLineFiniteArgument base ∈ _
        rw [inv_mul_cancel]
        exact (finiteIntegralGLLevel 3).one_mem))
  filter_upwards [near] with pair member vector spherical
  obtain ⟨compact, equality⟩ := member
  have factors : standardGoodLineFiniteArgument pair = standardGoodLineFiniteArgument base *
      GeneralLinearGroup.map integralEmbedding compact := by
    rw [equality, mul_inv_cancel_left]
  rw [goodLineFinitePadicIntegrand_eq_comp cusp vector spherical, Function.comp_apply,
    Function.comp_apply, factors, finiteSphericalPlaneFunction_right cusp vector spherical]

/-! ### The averaged path integrand -/

section Path

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (exponent : ℂ) (A : BinaryRealGL) (z : ℂ) (j : Fin (n + 2))

/-- The finite good-line integrand of the real translate of `vector` along the clamped straight
path from `i` to `z`, weighted by the Eichler coefficient. -/
def averagedPathIntegrand (point : (FiniteAwayThree × FiniteAwayThree) × ℝ) : ℂ :=
  endpointCoefficient n halfWeight z j point.2 * (finiteAverageWeight exponent point.1 *
    cuspScalarAffineRealization cusp vector (atFinite (finiteAverageBlock point.1) * atInfinity A)
      (clampedPath z point.2))

theorem averagedPathIntegrand_eq_clamped (pair : FiniteAwayThree × FiniteAwayThree) (t : ℝ) :
    averagedPathIntegrand cusp halfWeight vector exponent A z j (pair, t) =
      finiteAverageWeight exponent pair * clampedIntegrand n
        (cuspScalarWeightedRealization cusp halfWeight vector) z
        (atFinite (finiteAverageBlock pair) * atInfinity A) j t := by
  simp only [averagedPathIntegrand, clampedIntegrand, cuspScalarWeightedRealization,
    endpointCoefficient, Complex.real_smul]
  ring

theorem cuspScalarAffineRealization_eq_integrand (pair : FiniteAwayThree × FiniteAwayThree)
    (point : ℂ) :
    finiteAverageWeight exponent pair *
        cuspScalarAffineRealization cusp vector (atFinite (finiteAverageBlock pair) * atInfinity A)
          point =
      goodLineFinitePadicIntegrand cusp (cuspSmoothAction cusp
        (atInfinity (A * invertibleMatrix (binaryUpperSectionMatrix point))) vector)
        exponent pair := by
  rw [goodLineFinitePadicIntegrand_eq_weight, cuspSmoothAction_realize, atInfinity_mul,
    cuspScalarAffineRealization, mul_assoc]

theorem averagedPathIntegrand_continuous (positive : 0 < z.im)
    (spherical : vector.val ∈ cuspSphericalValues cusp) :
    Continuous (averagedPathIntegrand cusp halfWeight vector exponent A z j) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨base, time⟩
  have near := (goodLineFinitePadicIntegrand_eventually_eq cusp exponent base).prod_inl_nhds time
  have local_eq : averagedPathIntegrand cusp halfWeight vector exponent A z j =ᶠ[nhds (base, time)]
      fun point => endpointCoefficient n halfWeight z j point.2 *
        (finiteAverageWeight exponent base * cuspScalarAffineRealization cusp vector
          (atFinite (finiteAverageBlock base) * atInfinity A) (clampedPath z point.2)) := by
    filter_upwards [near] with point constant
    simp only [averagedPathIntegrand, cuspScalarAffineRealization_eq_integrand]
    rw [constant _ (cuspSmoothAction_real_spherical cusp vector spherical _)]
  refine ContinuousAt.congr ?_ local_eq.symm
  have affine : Continuous (fun t => cuspScalarAffineRealization cusp vector
      (atFinite (finiteAverageBlock base) * atInfinity A) (clampedPath z t)) :=
    (cuspScalarAffineRealization_analytic cusp vector _).continuousOn.comp_continuous
      (clampedPath_continuous z) (fun t => clampedPath_im_pos z positive t)
  exact (((endpointCoefficient_continuous n halfWeight z positive j).mul
    (continuous_const.mul affine)).comp continuous_snd).continuousAt

theorem endpointCoefficient_projIcc (t : ℝ) :
    endpointCoefficient n halfWeight z j (projIcc (0 : ℝ) 1 zero_le_one t) =
      endpointCoefficient n halfWeight z j t := by
  simp only [endpointCoefficient, clampedPath, projIcc_val]

theorem endpointCoefficient_bound (positive : 0 < z.im) :
    ∃ C : ℝ, ∀ t, ‖endpointCoefficient n halfWeight z j t‖ ≤ C := by
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (endpointCoefficient_continuous n halfWeight z positive j).continuousOn
    (s := Icc (0 : ℝ) 1)
  refine ⟨C, fun t => ?_⟩
  rw [← endpointCoefficient_projIcc]
  exact bound _ (projIcc (0 : ℝ) 1 zero_le_one t).property

theorem averagedPathIntegrand_integrable (positive : 0 < z.im)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (convergent : 3 < exponent.re) :
    Integrable (averagedPathIntegrand cusp halfWeight vector exponent A z j)
      ((finiteAwayThreeMeasure.prod finiteAwayThreeMeasure).prod
        ((volume : Measure ℝ).restrict (Ioc 0 1))) := by
  obtain ⟨C, coefficient_bound⟩ := endpointCoefficient_bound halfWeight z j positive
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  have dominating : Integrable (fun point : (FiniteAwayThree × FiniteAwayThree) × ℝ =>
      C * (goodLinePositiveWeight exponent point.1 * bound))
      ((finiteAwayThreeMeasure.prod finiteAwayThreeMeasure).prod
        ((volume : Measure ℝ).restrict (Ioc 0 1))) :=
    (((goodLinePositiveWeight_integrable exponent convergent).mul_const bound).const_mul C).comp_fst
      _
  refine dominating.mono'
    (averagedPathIntegrand_continuous cusp halfWeight vector exponent A z j positive
      spherical).aestronglyMeasurable (Filter.Eventually.of_forall fun point => ?_)
  rw [averagedPathIntegrand, norm_mul, norm_mul]
  exact mul_le_mul (coefficient_bound _) (mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ((norm_nonneg _).trans (coefficient_bound 0))

end Path

/-! ### The average of the Eichler period -/

/-- **The finite average of the Eichler period** of the scalar weighted realization of a
classical vector `v`, translated on the right by `A`, is the straight-line integral of the
finite average of `v` translated by `A`. -/
theorem coord_finiteAverageBinary_eichlerPeriod (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cuspClassicalVectors cusp halfWeight) (exponent : ℂ) (convergent : 3 < exponent.re)
    (A : BinaryRealGL) {z : ℂ} (positive : 0 < z.im) (j : Fin (n + 2)) :
    FiniteAverageIntegrable exponent
        (fun h => eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector.val) z
          (h * atInfinity A)) ∧
      (binaryWeightBasis (n + 1)).coord j (finiteAverageBinary exponent (fun h =>
        eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector.val) z
          (h * atInfinity A))) =
        ∫ t in (0 : ℝ)..1, endpointCoefficient n halfWeight z j t *
          cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector
            (A * invertibleMatrix (binaryUpperSectionMatrix (clampedPath z t))) := by
  have product (position : Fin (n + 2)) := averagedPathIntegrand_integrable cusp halfWeight
    vector.val exponent A z position positive vector.property.1 convergent
  have inner (position : Fin (n + 2)) (pair : FiniteAwayThree × FiniteAwayThree) :
      ∫ t, averagedPathIntegrand cusp halfWeight vector.val exponent A z position (pair, t)
        ∂((volume : Measure ℝ).restrict (Ioc 0 1)) =
      finiteAverageWeight exponent pair * (binaryWeightBasis (n + 1)).coord position
        (eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector.val) z
          (atFinite (finiteAverageBlock pair) * atInfinity A)) := by
    simp only [averagedPathIntegrand_eq_clamped]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      coord_eichlerPeriod_clamped]
  refine ⟨fun position => ?_, ?_⟩
  · have integrable := (product position).integral_prod_left
    simp only [inner] at integrable
    exact integrable
  · rw [coord_finiteAverageBinary]
    simp only [← inner]
    rw [integral_integral_swap (f := fun pair t =>
      averagedPathIntegrand cusp halfWeight vector.val exponent A z j (pair, t)) (product j),
      intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [averagedPathIntegrand, cuspScalarAffineRealization_eq_integrand]
    rw [integral_const_mul]
    rfl

end TernaryPeriodPolynomials.AnalyticClasses
