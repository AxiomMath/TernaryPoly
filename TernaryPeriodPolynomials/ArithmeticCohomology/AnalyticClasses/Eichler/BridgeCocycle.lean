module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Real.LineTransferBounds

@[expose] public section


/-!
# The pointwise Eichler normal form as a regular pointwise binary cocycle

The pointwise Eichler normal form `N_F` of the scalar weighted realization of a classical
endpoint vanishes on the stabilizer of `i` (in particular on the rotations and on `J`). When
the binary cocycle is reconstructed from `N_F` and a finite-level correction `κ`, the identity
`original = N_F + δκ` shows that `N_F` is a pointwise binary cocycle. Its functionals are
continuous in the matrix and bounded on compact sets uniformly in the adelic point, so it is a
`BinaryPointCocycle`. The lift `κ` of the correction is uniformly bounded and its translates
are continuous.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Set
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### Vanishing on the stabilizer of `i` -/

theorem eichlerPeriod_I (F : BinaryAdelicGL → ℂ → ℂ) : eichlerPeriod n F Complex.I = 0 := by
  funext h
  simp only [eichlerPeriod, eichlerIntegrand, sub_self, zero_mul, intervalIntegral.integral_zero,
    zero_smul, Finset.sum_const_zero, Pi.zero_apply]

/-- The pointwise Eichler normal form vanishes on the stabilizer of `i`. -/
theorem eichlerNormal_of_smul_I (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL)
    (fixes : A • UpperHalfPlane.I = UpperHalfPlane.I) : eichlerNormal n F A = 0 := by
  have base : basePoint A = Complex.I := by
    rw [basePoint, fixes, UpperHalfPlane.coe_I]
  funext h
  rw [eichlerNormal_def, base, binaryComplexReflection_basepoint, eichlerPeriod_I, map_zero,
    Pi.zero_apply, add_zero, smul_zero]

/-- **The pointwise Eichler normal form vanishes on the rotations.** -/
theorem eichlerNormal_rotation (F : BinaryAdelicGL → ℂ → ℂ) (angle : Circle) :
    eichlerNormal n F (binaryRotations angle) = 0 :=
  eichlerNormal_of_smul_I F _ (binaryRotations_smul_I angle)

/-- **The pointwise Eichler normal form vanishes at the reflection `J`.** -/
theorem eichlerNormal_J (F : BinaryAdelicGL → ℂ → ℂ) :
    eichlerNormal n F UpperHalfPlane.J = 0 :=
  eichlerNormal_of_smul_I F _ binaryReflection_smul_I

/-! ### The cocycle identity -/

theorem coboundary_pointCocycle (lift : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    IsBinaryPointCocycle (fun A => binaryAmbientRepresentation n A lift - lift) := by
  intro A C
  dsimp only
  rw [map_mul, Module.End.mul_apply, map_sub]
  abel

theorem original_pointCocycle (cusp : CuspidalRepresentation)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n)) :
    IsBinaryPointCocycle (n := n) (fun A => (original A).val) := by
  intro A C
  have equality := (groupCohomology.mem_cocycles₁_iff _).mp original.property A C
  exact (congrArg Subtype.val equality).trans (add_comm _ _)

theorem pointCocycle_sub {first second : BinaryRealGL → BinaryAdelicGL →
    Binary.HomogeneousPoly (n + 1)}
    (first_cocycle : IsBinaryPointCocycle first) (second_cocycle : IsBinaryPointCocycle second) :
    IsBinaryPointCocycle (fun A => first A - second A) := by
  intro A C
  dsimp only
  rw [first_cocycle, second_cocycle, map_sub]
  abel

/-- **The pointwise Eichler normal form is a pointwise binary cocycle.** -/
theorem eichlerNormal_pointCocycle (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction)) :
    IsBinaryPointCocycle (eichlerNormal n (endpointScalar cusp halfWeight vector)) := by
  have equality : eichlerNormal n (endpointScalar cusp halfWeight vector) = fun A =>
      (original A).val - (binaryAmbientRepresentation n A (hilbertLift cusp n correction) -
        hilbertLift cusp n correction) := by
    funext A h
    rw [Pi.sub_apply, Pi.sub_apply, original_eq_eichlerNormal_add_of_smooth cusp stages
      halfWeight vector fixed original correction correction_smooth reconstruction A h,
      add_sub_cancel_right]
  rw [equality]
  exact pointCocycle_sub (original_pointCocycle cusp original)
    (coboundary_pointCocycle (hilbertLift cusp n correction))

/-! ### Regularity of the scalar Eichler period -/

/-- The scalar Eichler integrand along the clamped straight path. -/
def clampedIntegrand (n : ℕ) (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (position : Fin (n + 2)) (t : ℝ) : ℂ :=
  (z - Complex.I) * F h (clampedPath z t) *
    (binaryWeightBasis (n + 1)).coord position (binaryPointPower (n + 1) (clampedPath z t))

theorem coord_eichlerPeriod_clamped (F : BinaryAdelicGL → ℂ → ℂ) (z : ℂ) (h : BinaryAdelicGL)
    (position : Fin (n + 2)) :
    (binaryWeightBasis (n + 1)).coord position (eichlerPeriod n F z h) =
      ∫ t in (0 : ℝ)..1, clampedIntegrand n F z h position t := by
  rw [eichlerPeriod, Module.Basis.coord_apply, Module.Basis.repr_sum_self]
  apply intervalIntegral.integral_congr
  intro t member
  have path : clampedPath z t = eichlerPath z t := clampedPath_eqOn z member
  simp only [eichlerIntegrand, clampedIntegrand, path]

theorem clampedPath_upper_continuous :
    Continuous (fun point : UpperHalfPlane × ℝ => clampedPath (point.1 : ℂ) point.2) := by
  unfold clampedPath
  exact continuous_const.add ((continuous_subtype_val.comp (continuous_projIcc.comp
    continuous_snd)).smul ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
      continuous_const))

theorem pointPower_coord_continuous (position : Fin (n + 2)) :
    Continuous (fun point : ℂ =>
      (binaryWeightBasis (n + 1)).coord position (binaryPointPower (n + 1) point)) :=
  continuous_iff_continuousAt.mpr fun point =>
    (binaryPointPower_functional_analytic (n + 1)
      ((binaryWeightBasis (n + 1)).coord position) point).continuousAt

theorem clampedIntegrand_continuous (F : BinaryAdelicGL → ℂ → ℂ)
    (regular : ∀ h, ContinuousOn (F h) UpperHalfPlane.upperHalfPlaneSet)
    (h : BinaryAdelicGL) (position : Fin (n + 2)) :
    Continuous (fun point : UpperHalfPlane × ℝ =>
      clampedIntegrand n F point.1 h position point.2) := by
  have values : Continuous (fun point : UpperHalfPlane × ℝ =>
      F h (clampedPath (point.1 : ℂ) point.2)) :=
    (regular h).comp_continuous clampedPath_upper_continuous
      (fun point => clampedPath_im_pos _ point.1.im_pos point.2)
  exact (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub continuous_const).mul
    values).mul ((pointPower_coord_continuous position).comp clampedPath_upper_continuous)

/-- **Continuity of the scalar Eichler period in its endpoint.** -/
theorem eichlerPeriod_coord_continuous (F : BinaryAdelicGL → ℂ → ℂ)
    (regular : ∀ h, ContinuousOn (F h) UpperHalfPlane.upperHalfPlaneSet)
    (h : BinaryAdelicGL) (position : Fin (n + 2)) :
    Continuous (fun point : UpperHalfPlane =>
      (binaryWeightBasis (n + 1)).coord position (eichlerPeriod n F point h)) := by
  simp only [coord_eichlerPeriod_clamped]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (clampedIntegrand_continuous F regular h position) 0 1

/-- **Uniform bound of the scalar Eichler period on compact sets of endpoints.** -/
theorem eichlerPeriod_coord_bound (F : BinaryAdelicGL → ℂ → ℂ) (halfWeight : ℤ)
    (bounded : ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (h : BinaryAdelicGL) (point : UpperHalfPlane),
      ‖F h point‖ ≤ point.im ^ halfWeight * bound)
    (endpoints : Set UpperHalfPlane) (compact : IsCompact endpoints) (position : Fin (n + 2)) :
    ∃ C : ℝ, ∀ point ∈ endpoints, ∀ h,
      ‖(binaryWeightBasis (n + 1)).coord position (eichlerPeriod n F point h)‖ ≤ C := by
  obtain ⟨bound, bound_nonneg, value_bound⟩ := bounded
  let weight : UpperHalfPlane × ℝ → ℝ := fun point =>
    ‖(point.1 : ℂ) - Complex.I‖ * (clampedPath (point.1 : ℂ) point.2).im ^ halfWeight *
      ‖(binaryWeightBasis (n + 1)).coord position
        (binaryPointPower (n + 1) (clampedPath (point.1 : ℂ) point.2))‖
  have weight_continuous : Continuous weight := by
    have imaginary := Complex.continuous_im.comp clampedPath_upper_continuous
    exact (((UpperHalfPlane.continuous_coe.comp continuous_fst).sub continuous_const).norm.mul
      (imaginary.zpow₀ halfWeight fun point =>
        Or.inl (clampedPath_im_pos _ point.1.im_pos point.2).ne')).mul
      ((pointPower_coord_continuous position).comp clampedPath_upper_continuous).norm
  obtain ⟨maximum, maximum_bound⟩ := (compact.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := endpoints ×ˢ Icc (0 : ℝ) 1) weight_continuous.continuousOn
  refine ⟨bound * maximum * |1 - 0|, fun point member h => ?_⟩
  rw [coord_eichlerPeriod_clamped]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t inside
  have interval : t ∈ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one] at inside
    exact ⟨inside.1.le, inside.2⟩
  have local_bound := maximum_bound (point, t) ⟨member, interval⟩
  let upper : UpperHalfPlane := ⟨clampedPath point t, clampedPath_im_pos _ point.im_pos t⟩
  have value := value_bound h upper
  have upper_im : upper.im = (clampedPath point t).im := rfl
  have weight_nonneg : 0 ≤ weight (point, t) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (zpow_pos (clampedPath_im_pos _ point.im_pos t)
      halfWeight).le) (norm_nonneg _)
  rw [Real.norm_of_nonneg weight_nonneg] at local_bound
  calc ‖clampedIntegrand n F point h position t‖
      = bound⁻¹ * 0 + ‖(point : ℂ) - Complex.I‖ * ‖F h upper‖ *
          ‖(binaryWeightBasis (n + 1)).coord position
            (binaryPointPower (n + 1) (clampedPath point t))‖ := by
        rw [mul_zero, zero_add, clampedIntegrand, norm_mul, norm_mul]
    _ ≤ bound⁻¹ * 0 + ‖(point : ℂ) - Complex.I‖ * (upper.im ^ halfWeight * bound) *
          ‖(binaryWeightBasis (n + 1)).coord position
            (binaryPointPower (n + 1) (clampedPath point t))‖ := by
        gcongr
    _ = bound * weight (point, t) := by
        simp only [weight, mul_zero, zero_add, upper_im]
        ring
    _ ≤ bound * maximum := mul_le_mul_of_nonneg_left local_bound bound_nonneg

/-! ### Functionals on the binary coefficients -/

theorem functional_eq_sum_coord (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ)
    (polynomial : Binary.HomogeneousPoly (n + 1)) :
    functional polynomial = ∑ position, (binaryWeightBasis (n + 1)).coord position polynomial *
      functional (binaryWeightBasis (n + 1) position) := by
  calc functional polynomial = functional (∑ position,
      (binaryWeightBasis (n + 1)).coord position polynomial •
        binaryWeightBasis (n + 1) position) := by
        simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    _ = _ := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun position _ => by rw [map_smul, smul_eq_mul]

theorem continuous_functional_of_coord {X : Type} [TopologicalSpace X]
    (values : X → Binary.HomogeneousPoly (n + 1))
    (regular : ∀ position, Continuous (fun point =>
      (binaryWeightBasis (n + 1)).coord position (values point)))
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun point => functional (values point)) := by
  have expansion : (fun point => functional (values point)) = fun point =>
      ∑ position, (binaryWeightBasis (n + 1)).coord position (values point) *
        functional (binaryWeightBasis (n + 1) position) :=
    funext fun point => functional_eq_sum_coord functional (values point)
  rw [expansion]
  exact continuous_finsetSum _ fun position _ => (regular position).mul continuous_const

theorem bound_functional_of_coord {X : Type} (values : X → Binary.HomogeneousPoly (n + 1))
    (domain : Set X)
    (bounded : ∀ position, ∃ C : ℝ, ∀ point ∈ domain,
      ‖(binaryWeightBasis (n + 1)).coord position (values point)‖ ≤ C)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, ∀ point ∈ domain, ‖functional (values point)‖ ≤ C := by
  choose C hC using bounded
  refine ⟨∑ position, C position * ‖functional (binaryWeightBasis (n + 1) position)‖,
    fun point member => ?_⟩
  rw [functional_eq_sum_coord functional]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun position _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hC position point member) (norm_nonneg _)

/-! ### Regularity of the pointwise Eichler normal form -/

/-- The reflection `z ↦ -conj z` of the upper half plane. -/
def reflectUpper (point : UpperHalfPlane) : UpperHalfPlane :=
  ⟨binaryComplexReflection point, by rw [binaryComplexReflection_im]; exact point.im_pos⟩

theorem reflectUpper_continuous : Continuous reflectUpper := by
  apply UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.mpr
  exact binaryComplexReflection.continuous.comp UpperHalfPlane.continuous_coe

theorem smul_I_continuous : Continuous (fun A : BinaryRealGL => A • UpperHalfPlane.I) :=
  continuous_id.smul continuous_const

/-- The reflection action on coefficients, followed by a functional. -/
def reflectedFunctional (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ :=
  functional.comp (normPower (Matrix.GeneralLinearGroup.det (atInfinity UpperHalfPlane.J))
    (((n : ℂ) + 3) / 2) • binaryCoefficient n UpperHalfPlane.J)

theorem functional_eichlerNormal (F : BinaryAdelicGL → ℂ → ℂ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) (A : BinaryRealGL)
    (h : BinaryAdelicGL) :
    functional (eichlerNormal n F A h) = (2 : ℂ)⁻¹ *
      (functional (eichlerPeriod n F ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) h) +
        reflectedFunctional functional (eichlerPeriod n F
          (reflectUpper (A • UpperHalfPlane.I) : ℂ) (h * atInfinity UpperHalfPlane.J))) := by
  rw [eichlerNormal_def, map_smul, map_add, smul_eq_mul]
  rfl

/-- **Continuity of the pointwise Eichler normal form.** -/
theorem eichlerNormal_continuous (F : BinaryAdelicGL → ℂ → ℂ)
    (regular : ∀ h, ContinuousOn (F h) UpperHalfPlane.upperHalfPlaneSet)
    (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun A => functional (eichlerNormal n F A h)) := by
  simp only [functional_eichlerNormal]
  have direct := continuous_functional_of_coord
    (fun point : UpperHalfPlane => eichlerPeriod n F point h)
    (eichlerPeriod_coord_continuous F regular h) functional
  have reflected := continuous_functional_of_coord
    (fun point : UpperHalfPlane => eichlerPeriod n F point (h * atInfinity UpperHalfPlane.J))
    (eichlerPeriod_coord_continuous F regular _) (reflectedFunctional functional)
  exact continuous_const.mul ((direct.comp smul_I_continuous).add
    (reflected.comp (reflectUpper_continuous.comp smul_I_continuous)))

/-- **Uniform bound of the pointwise Eichler normal form on compact sets.** -/
theorem eichlerNormal_bounded (F : BinaryAdelicGL → ℂ → ℂ) (halfWeight : ℤ)
    (bounded : ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (h : BinaryAdelicGL) (point : UpperHalfPlane),
      ‖F h point‖ ≤ point.im ^ halfWeight * bound)
    (K : Set BinaryRealGL) (compact : IsCompact K)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (eichlerNormal n F A h)‖ ≤ C := by
  let endpoints := (fun A : BinaryRealGL => A • UpperHalfPlane.I) '' K
  have endpoints_compact : IsCompact endpoints := compact.image smul_I_continuous
  have reflected_compact : IsCompact (reflectUpper '' endpoints) :=
    endpoints_compact.image reflectUpper_continuous
  obtain ⟨first, first_bound⟩ := bound_functional_of_coord
    (fun point : UpperHalfPlane × BinaryAdelicGL => eichlerPeriod n F point.1 point.2)
    (endpoints ×ˢ univ) (fun position => by
      obtain ⟨C, hC⟩ := eichlerPeriod_coord_bound F halfWeight bounded endpoints
        endpoints_compact position
      exact ⟨C, fun point member => hC point.1 member.1 point.2⟩) functional
  obtain ⟨second, second_bound⟩ := bound_functional_of_coord
    (fun point : UpperHalfPlane × BinaryAdelicGL => eichlerPeriod n F point.1 point.2)
    ((reflectUpper '' endpoints) ×ˢ univ) (fun position => by
      obtain ⟨C, hC⟩ := eichlerPeriod_coord_bound F halfWeight bounded _
        reflected_compact position
      exact ⟨C, fun point member => hC point.1 member.1 point.2⟩)
    (reflectedFunctional functional)
  refine ⟨‖(2 : ℂ)⁻¹‖ * (first + second), fun A member h => ?_⟩
  have endpoint_mem : A • UpperHalfPlane.I ∈ endpoints := ⟨A, member, rfl⟩
  rw [functional_eichlerNormal, norm_mul]
  gcongr
  exact (norm_add_le _ _).trans (add_le_add
    (first_bound (A • UpperHalfPlane.I, h) ⟨endpoint_mem, mem_univ _⟩)
    (second_bound (reflectUpper (A • UpperHalfPlane.I), h * atInfinity UpperHalfPlane.J)
      ⟨⟨_, endpoint_mem, rfl⟩, mem_univ _⟩))

/-! ### The scalar weighted realization -/

theorem endpointScalar_continuousOn (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (h : BinaryAdelicGL) :
    ContinuousOn (endpointScalar cusp halfWeight vector h) UpperHalfPlane.upperHalfPlaneSet :=
  (cuspScalarWeightedRealization_analytic cusp halfWeight vector h).continuousOn

/-- **The bound** `‖F h z‖ ≤ C · (Im z)^k` of the scalar weighted realization. -/
theorem endpointScalar_bound (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (h : BinaryAdelicGL) (point : UpperHalfPlane),
      ‖endpointScalar cusp halfWeight vector h point‖ ≤ point.im ^ halfWeight * bound :=
  cuspScalarWeightedRealization_bound cusp halfWeight vector

/-- **Holomorphy of the scalar weighted realization** of a spherical vector of rotation weight
`2k` whose weighted affine orbit is holomorphic. -/
theorem endpointScalar_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (h : BinaryAdelicGL) :
    DifferentiableOn ℂ (endpointScalar cusp halfWeight vector h)
      UpperHalfPlane.upperHalfPlaneSet :=
  cuspScalarWeightedRealization_holomorphic cusp halfWeight vector spherical rotation holomorphic h

/-- Spherical vectors are fixed by the finite congruence level. -/
theorem spherical_mem_fixedSubspace (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp) :
    vector ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence := by
  rintro ⟨element, compact, _, rfl⟩
  exact spherical compact

/-! ### The packaged pointwise binary cocycle -/

/-- **The pointwise Eichler normal form of the classical endpoint as a `BinaryPointCocycle`.** -/
def eichlerNormalPointCocycle (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction)) :
    BinaryPointCocycle n where
  value := eichlerNormal n (endpointScalar cusp halfWeight vector)
  cocycle := eichlerNormal_pointCocycle cusp stages halfWeight vector fixed original correction
    correction_smooth reconstruction
  continuous := eichlerNormal_continuous _ (endpointScalar_continuousOn cusp halfWeight vector)
  bounded := fun K compact functional =>
    eichlerNormal_bounded _ halfWeight (endpointScalar_bound cusp halfWeight vector) K compact
      functional

theorem eichlerNormalPointCocycle_value (cusp : CuspidalRepresentation)
    (stages : AnalyticScalar.ContinuousStages cusp) (halfWeight : ℤ) (vector : cusp.smooth)
    (fixed : vector.val ∈ BinaryLevel.fixedSubspace cusp BinaryLevel.finiteCongruence)
    (original : groupCohomology.cocycles₁ (binaryCuspidalRep cusp n))
    (correction : Fin (n + 2) → cusp.H)
    (correction_smooth : ∀ position, correction position ∈ cusp.smooth)
    (reconstruction : ∀ A : BinaryRealGL,
      binaryHilbertEmbedding cusp (binaryWeightBasis (n + 1)) (original A) =
        (2 : ℂ)⁻¹ • (binaryEndpointPeriod cusp n halfWeight vector.val
          ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
          binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) UpperHalfPlane.J
            (binaryEndpointPeriod cusp n halfWeight vector.val
              (binaryComplexReflection ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)))) +
        (binaryHilbertOperator cusp (binaryWeightBasis (n + 1)) A correction - correction)) :
    (eichlerNormalPointCocycle cusp stages halfWeight vector fixed original correction
      correction_smooth reconstruction).value =
        eichlerNormal n (endpointScalar cusp halfWeight vector) := rfl

/-! ### The lift of the correction -/

/-- **The lift of a smooth tuple is uniformly bounded.** -/
theorem hilbertLift_coord_bound (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth) :
    ∃ C : ℝ, ∀ h position,
      ‖(binaryWeightBasis (n + 1)).coord position (hilbertLift cusp n vectors h)‖ ≤ C := by
  choose C hC using fun position => cusp.bounded ⟨vectors position, smooth position⟩
  refine ⟨∑ position, |C position|, fun h position => ?_⟩
  rw [coord_hilbertLift, smoothRealize_of_mem cusp ⟨_, smooth position⟩]
  exact ((hC position h).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun position => |C position|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ position))

theorem hilbertLift_translate_continuous (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (h : BinaryAdelicGL) (position : Fin (n + 2)) :
    Continuous (fun A : BinaryRealGL =>
      smoothRealize cusp (vectors position) (h * atInfinity A)) := by
  rw [smoothRealize_of_mem cusp ⟨_, smooth position⟩]
  have regular := smooth_continuous (cusp.scalarSmooth ⟨_, smooth position⟩ h)
  exact regular.comp (continuous_pi fun _ => continuous_id)

/-- **The translates of the lift of a smooth tuple are continuous.** -/
theorem hilbertLift_ambient_continuous (cusp : CuspidalRepresentation)
    (vectors : Fin (n + 2) → cusp.H) (smooth : ∀ position, vectors position ∈ cusp.smooth)
    (h : BinaryAdelicGL) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    Continuous (fun A =>
      functional (binaryAmbientRepresentation n A (hilbertLift cusp n vectors) h)) := by
  have scalar : Continuous (fun A : BinaryRealGL =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2)) := by
    apply realGL_continuous_of_contDiffOn
    apply binary_normalizingFactor_contDiffOn (fun matrix => matrix) _ (fun _ member => member)
    intro row column
    fun_prop
  have coefficients (position : Fin (n + 2)) : Continuous (fun A : BinaryRealGL =>
      functional (binaryCoefficient n A (binaryWeightBasis (n + 1) position))) := by
    apply realGL_continuous_of_contDiffOn
    apply binaryCoefficient_functional_contDiffOn (fun matrix => matrix) _
      (fun _ member => member) (binaryWeightBasis (n + 1) position) functional
    intro row column
    fun_prop
  have expansion (A : BinaryRealGL) :
      functional (binaryAmbientRepresentation n A (hilbertLift cusp n vectors) h) =
        normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) *
          ∑ position, smoothRealize cusp (vectors position) (h * atInfinity A) *
            functional (binaryCoefficient n A (binaryWeightBasis (n + 1) position)) := by
    change functional
      (normPower (Matrix.GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
        binaryCoefficient n A (hilbertLift cusp n vectors (h * atInfinity A))) = _
    rw [map_smul, smul_eq_mul, hilbertLift, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  simp only [expansion]
  exact scalar.mul (continuous_finsetSum _ fun position _ =>
    (hilbertLift_translate_continuous cusp vectors smooth h position).mul
      (coefficients position))

end TernaryPeriodPolynomials.AnalyticClasses
