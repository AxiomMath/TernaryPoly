module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CentralCharacter

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem adeleMeasure_additiveDomain : adeleMeasure additiveDomain = 1 := by
  rw [adeleMeasure, additiveDomain, Measure.prod_prod,
    finiteMeasure_integralLattice, Real.volume_Ico]
  norm_num

theorem adeleNorm_mul_preimage (idele : Adelesˣ) (domain : Set Adeles) :
    (adeleNorm idele : ENNReal) *
      adeleMeasure ((fun element => idele.val * element) ⁻¹' domain) =
        adeleMeasure domain := by
  have scaling := addEquivAddHaarChar_smul_preimage adeleMeasure
    (X := domain) (ContinuousAddEquiv.mulLeft idele)
  change (adeleNorm idele : ENNReal) *
    adeleMeasure ((fun element => idele.val * element) ⁻¹' domain) =
      adeleMeasure domain at scaling
  exact scaling

theorem adeleNorm_realAdeleUnit (scalar : ℝˣ) :
    (adeleNorm (realAdeleUnit scalar) : ℝ) = |scalar.val| := by
  have preimage_domain :
      (fun element => (realAdeleUnit scalar).val * element) ⁻¹' additiveDomain =
      ((fun element : ℝ => scalar.val * element) ⁻¹' Set.Ico 0 1) ×ˢ
        Set.range integralEmbedding := by
    ext element
    simp only [Set.mem_preimage, additiveDomain, Set.mem_prod, realAdeleUnit,
      Prod.fst_mul, Prod.snd_mul, one_mul]
  have norm_identity := adeleNorm_mul_preimage (realAdeleUnit scalar) additiveDomain
  rw [preimage_domain, adeleMeasure_additiveDomain, adeleMeasure,
    Measure.prod_prod, finiteMeasure_integralLattice,
    Real.volume_preimage_mul_left (Units.ne_zero scalar), Real.volume_Ico] at norm_identity
  norm_num only [sub_zero, ENNReal.ofReal_one, mul_one] at norm_identity
  have real_identity := congrArg ENNReal.toReal norm_identity
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_one, abs_inv] at real_identity
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))] at real_identity
  have scalar_ne : |scalar.val| ≠ 0 := abs_ne_zero.mpr (Units.ne_zero scalar)
  calc
    (adeleNorm (realAdeleUnit scalar) : ℝ) =
        ((adeleNorm (realAdeleUnit scalar) : ℝ) * |scalar.val|⁻¹) * |scalar.val| := by
      rw [mul_assoc, inv_mul_cancel₀ scalar_ne, mul_one]
    _ = |scalar.val| := by rw [real_identity, one_mul]

theorem integral_unit_mul_mem_lattice (unit : IntegralAdelesˣ) (element : FiniteAdeles) :
    integralEmbedding unit.val * element ∈ Set.range integralEmbedding ↔
      element ∈ Set.range integralEmbedding := by
  constructor
  · rintro ⟨integralElement, product_eq⟩
    refine ⟨unit.inv * integralElement, ?_⟩
    rw [map_mul, product_eq, ← mul_assoc, ← map_mul, unit.inv_val, map_one, one_mul]
  · rintro ⟨integralElement, rfl⟩
    exact ⟨unit.val * integralElement, map_mul _ _ _⟩

theorem adeleNorm_integralAdeleUnit (unit : IntegralAdelesˣ) :
    adeleNorm (integralAdeleUnit unit) = 1 := by
  have preimage_domain :
      (fun element => (integralAdeleUnit unit).val * element) ⁻¹' additiveDomain =
        additiveDomain := by
    ext element
    simp only [Set.mem_preimage, additiveDomain, Set.mem_prod, integralAdeleUnit,
      Prod.fst_mul, Prod.snd_mul, one_mul, integral_unit_mul_mem_lattice]
  have norm_identity := adeleNorm_mul_preimage (integralAdeleUnit unit) additiveDomain
  rw [preimage_domain, adeleMeasure_additiveDomain, mul_one] at norm_identity
  exact ENNReal.coe_injective norm_identity

theorem normPower_integralAdeleUnit (unit : IntegralAdelesˣ) (exponent : ℂ) :
    normPower (integralAdeleUnit unit) exponent = 1 := by
  simp [normPower, adeleNorm_integralAdeleUnit]

theorem normPower_realAdeleUnit (scalar : ℝˣ) (exponent : ℂ) :
    normPower (realAdeleUnit scalar) exponent =
      Complex.exp (exponent * (Real.log |scalar.val| : ℂ)) := by
  rw [normPower, adeleNorm_realAdeleUnit]

theorem det_split_of_integral_finite
    (groupElement : AdelicGL)
    (integralElement : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (finite_integral : GeneralLinearGroup.map integralEmbedding integralElement =
      finiteGroup groupElement) :
    GeneralLinearGroup.det groupElement =
      realAdeleUnit (GeneralLinearGroup.det (realGroup groupElement)) *
        integralAdeleUnit (GeneralLinearGroup.det integralElement) := by
  have real_det := GeneralLinearGroup.map_det
    (RingHom.fst ℝ FiniteAdeles) groupElement
  have finite_det := GeneralLinearGroup.map_det
    (RingHom.snd ℝ FiniteAdeles) groupElement
  have integral_det := GeneralLinearGroup.map_det integralEmbedding integralElement
  rw [finite_integral] at integral_det
  apply Units.ext
  apply Prod.ext
  · change (GeneralLinearGroup.det groupElement).val.1 =
      (GeneralLinearGroup.det (realGroup groupElement)).val * 1
    rw [mul_one]
    exact (congrArg Units.val real_det).symm
  · change (GeneralLinearGroup.det groupElement).val.2 =
      1 * integralEmbedding (GeneralLinearGroup.det integralElement).val
    rw [one_mul]
    exact (congrArg Units.val finite_det).symm.trans (congrArg Units.val integral_det)

theorem adeleNorm_det_compact (groupElement : AdelicGL)
    (compact_spec : inMaximalCompact groupElement) :
    adeleNorm (GeneralLinearGroup.det groupElement) = 1 := by
  obtain ⟨orthogonal, integralElement, finite_integral⟩ := compact_spec
  rw [det_split_of_integral_finite groupElement integralElement finite_integral,
    map_mul, adeleNorm_integralAdeleUnit, mul_one]
  apply NNReal.coe_injective
  rw [adeleNorm_realAdeleUnit]
  have det_square := congrArg Matrix.det orthogonal
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at det_square
  change |(realGroup groupElement).val.det| = 1
  have abs_square : |(realGroup groupElement).val.det| ^ 2 = 1 := by
    rw [sq_abs, pow_two, det_square]
  nlinarith [abs_nonneg (realGroup groupElement).val.det]

theorem normPower_det_compact (groupElement : AdelicGL)
    (compact_spec : inMaximalCompact groupElement) (exponent : ℂ) :
    normPower (GeneralLinearGroup.det groupElement) exponent = 1 := by
  simp [normPower, adeleNorm_det_compact groupElement compact_spec]

theorem realGroup_atFinite (finiteElement : FiniteGL) :
    realGroup (atFinite finiteElement) = 1 := by
  apply Units.ext
  rfl

theorem finiteGroup_atFinite (finiteElement : FiniteGL) :
    finiteGroup (atFinite finiteElement) = finiteElement := by
  apply Units.ext
  rfl

theorem atFinite_level_compact (levelElement : finiteLevel) :
    inMaximalCompact (atFinite levelElement.val) := by
  constructor
  · rw [realGroup_atFinite]
    simp
  · rw [finiteGroup_atFinite]
    obtain ⟨integralElement, _, finite_integral⟩ := levelElement.property
    exact ⟨integralElement, finite_integral⟩

theorem det_atInfinity (realElement : RealGL3) :
    GeneralLinearGroup.det (atInfinity realElement) =
      realAdeleUnit (GeneralLinearGroup.det realElement) := by
  have finite_integral : GeneralLinearGroup.map integralEmbedding
      (1 : GeneralLinearGroup (Fin 3) IntegralAdeles) = finiteGroup (atInfinity realElement) := by
    rw [map_one]
    apply Units.ext
    rfl
  have real_projection : realGroup (atInfinity realElement) = realElement := by
    apply Units.ext
    rfl
  rw [det_split_of_integral_finite (atInfinity realElement) 1 finite_integral,
    real_projection, map_one]
  have integral_one : integralAdeleUnit 1 = 1 := by
    apply Units.ext
    simp [integralAdeleUnit]
  rw [integral_one, mul_one]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
