module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HeightProperties
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Scalar.Parameter
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.HeightProperties

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight

theorem finite_height_locallyConstant : IsLocallyConstant (fun matrix : FiniteGL => height (atFinite matrix)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro matrix
  let neighborhood : Set FiniteGL :=
    (fun value => matrix⁻¹ * value) ⁻¹' (TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact : Set FiniteGL)
  refine ⟨neighborhood, TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact_isOpen.preimage
    (continuous_const.mul continuous_id), ?_, ?_⟩
  · change matrix⁻¹ * matrix ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro value membership
    have compactness := TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact_atFinite
      (⟨matrix⁻¹ * value, membership⟩ : TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact)
    have equality := height_mul_compact (atFinite matrix) (atFinite (matrix⁻¹ * value)) compactness
    rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_mul, mul_inv_cancel_left] at equality
    exact equality

theorem finite_height_continuous : Continuous (fun matrix : FiniteGL => height (atFinite matrix)) :=
  finite_height_locallyConstant.continuous

theorem finite_height_bound (basePoint : FiniteGL) :
    ∃ bound : ℝ, ∀ matrix ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact,
      height (atFinite (matrix * basePoint)) ≤ bound := by
  obtain ⟨bound, boundProperty⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.MaximalCompact.finiteCompact_isCompact.exists_bound_of_continuousOn
      (finite_height_continuous.comp (continuous_id.mul continuous_const)).continuousOn
  exact ⟨bound, fun matrix membership => (le_abs_self _).trans (boundProperty matrix membership)⟩

theorem height_real_finite (realMatrix : RealGL3) (finiteMatrix : FiniteGL) :
    height (atInfinity realMatrix * atFinite finiteMatrix) =
      height (atInfinity realMatrix) + height (atFinite finiteMatrix) := by
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, _⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  have realFactorization : atInfinity realMatrix =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement).val * atInfinity orthogonalElement := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
    rfl
  have compactness := (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.inMaximalCompact_atInfinity orthogonalElement).mpr orthogonality
  have realHeight := height_of_factorization (atInfinity realMatrix)
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement) (atInfinity orthogonalElement)
    realFactorization compactness
  conv_lhs => rw [realFactorization, mul_assoc, height_plane_mul,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, height_mul_compact _ _ compactness]
  rw [realHeight]

theorem height_atInfinity (realMatrix : RealGL3) :
    height (atInfinity realMatrix) = Real.log |realMatrix.val.det| / 3 -
      Real.log ‖(WithLp.toLp 2 (fun column => realMatrix.val 2 column) : EuclideanSpace ℝ (Fin 3))‖ := by
  obtain ⟨parabolicElement, orthogonalElement, factorization, orthogonality, cornerValue⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal realMatrix
  have realFactorization : atInfinity realMatrix =
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeParabolicAtInfinity parabolicElement).val * atInfinity orthogonalElement := by
    rw [factorization, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
    rfl
  rw [height_of_factorization _ _ _ realFactorization
    ((TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.inMaximalCompact_atInfinity orthogonalElement).mpr orthogonality),
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.planeHeightLog_atInfinity,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.real_heightLog_formula realMatrix parabolicElement orthogonalElement
      factorization orthogonality cornerValue]

theorem planeHeightLog_rational (element : planeParabolic ℚ) :
    planeHeightLog (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element) = 0 := by
  rw [planeHeightLog_eq_det_corner, TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.corner_rational]
  have determinantNorm : adeleNorm
      (GeneralLinearGroup.det (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element).val) = 1 := by
    change adeleNorm (GeneralLinearGroup.det (GeneralLinearGroup.map rationalAdele element.val)) = 1
    rw [GeneralLinearGroup.map_det]
    exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.adeleNorm_rational _
  rw [determinantNorm, TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProductFormula.adeleNorm_rational, NNReal.coe_one,
    Real.log_one, zero_div, sub_self]

theorem height_rational_plane (element : planeParabolic ℚ) (basePoint : AdelicGL) :
    height (rationalGroup element.val * basePoint) = height basePoint := by
  have equality := height_plane_mul (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RationalInvariance.rationalPlane element) basePoint
  rw [planeHeightLog_rational, zero_add] at equality
  exact equality

theorem height_eq_of_flag (first second : RationalGL3)
    (sameFlag : (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second)
    (basePoint : AdelicGL) :
    height (rationalGroup first⁻¹ * basePoint) = height (rationalGroup second⁻¹ * basePoint) := by
  have parabolicMembership : first⁻¹ * second ∈ planeParabolic ℚ := QuotientGroup.eq.mp sameFlag
  have equality := height_rational_plane ⟨first⁻¹ * second, parabolicMembership⟩
    (rationalGroup second⁻¹ * basePoint)
  change height (rationalGroup (first⁻¹ * second) * (rationalGroup second⁻¹ * basePoint)) = _ at equality
  rw [← mul_assoc, ← map_mul, mul_inv_cancel_right] at equality
  exact equality

theorem integral_product_eq_components (integralMatrix : IntegralGL3) (basePoint : AdelicGL) :
    rationalGroup (integralRational integralMatrix) * basePoint =
      atInfinity (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix * realGroup basePoint) *
        atFinite (integralFinite integralMatrix * finiteGroup basePoint) := by
  calc
    rationalGroup (integralRational integralMatrix) * basePoint =
        combineGL (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix)
            (integralFinite integralMatrix) * combineGL (realGroup basePoint) (finiteGroup basePoint) := by
      rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul,
        ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralGroup_eq_mul, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul]
    _ = combineGL (GeneralLinearGroup.map (Int.castRingHom ℝ) integralMatrix * realGroup basePoint)
        (integralFinite integralMatrix * finiteGroup basePoint) :=
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition.combineGL_mul _ _ _ _).symm
    _ = _ := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul _ _

theorem height_integral_product (integralMatrix : IntegralGL3) (basePoint : AdelicGL) :
    height (rationalGroup (integralRational integralMatrix) * basePoint) =
      Real.log |(realGroup basePoint).val.det| / 3 -
        Real.log ‖(WithLp.toLp 2 ((fun column => (integralMatrix.val 2 column : ℝ)) ᵥ*
          (realGroup basePoint).val) : EuclideanSpace ℝ (Fin 3))‖ +
        height (atFinite (integralFinite integralMatrix * finiteGroup basePoint)) := by
  rw [integral_product_eq_components, height_real_finite, height_atInfinity,
    Units.val_mul, Matrix.det_mul, abs_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.abs_det_integral_real, one_mul]
  rfl

theorem height_integral_product_bound (basePoint : AdelicGL) :
    ∃ bound : ℝ, ∀ integralMatrix : IntegralGL3,
      height (rationalGroup (integralRational integralMatrix) * basePoint) ≤
        Real.log |(realGroup basePoint).val.det| / 3 -
          Real.log ‖(WithLp.toLp 2 ((fun column => (integralMatrix.val 2 column : ℝ)) ᵥ*
            (realGroup basePoint).val) : EuclideanSpace ℝ (Fin 3))‖ + bound := by
  obtain ⟨bound, boundProperty⟩ := finite_height_bound (finiteGroup basePoint)
  refine ⟨bound, fun integralMatrix => ?_⟩
  rw [height_integral_product]
  apply add_le_add_right
  apply boundProperty
  exact ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integralMatrix,
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralFinite_eq_map integralMatrix).symm⟩

theorem height_flag_bound (basePoint : AdelicGL) :
    ∃ bound : ℝ, ∀ flag : Flags .plane,
      height (rationalGroup flag.out⁻¹ * basePoint) ≤
        TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter.flagHeight (realGroup basePoint) flag + bound := by
  obtain ⟨bound, boundProperty⟩ := height_integral_product_bound basePoint
  refine ⟨bound, fun flag => ?_⟩
  have sameFlag : (QuotientGroup.mk flag.out : Flags .plane) = QuotientGroup.mk
      (integralRational (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)) := by
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative_mk]
    exact Quotient.out_eq flag
  rw [height_eq_of_flag _ _ sameFlag, ← map_inv]
  exact boundProperty (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRepresentative flag)⁻¹

theorem height_flag_boundedAbove (basePoint : AdelicGL) :
    ∃ bound : ℝ, ∀ flag : Flags .plane, height (rationalGroup flag.out⁻¹ * basePoint) ≤ bound := by
  obtain ⟨finiteBound, finiteProperty⟩ := height_flag_bound basePoint
  obtain ⟨realBound, _, realProperty⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarParameter.flagHeight_boundedAbove (realGroup basePoint)
  exact ⟨realBound + finiteBound, fun flag =>
    (finiteProperty flag).trans (add_le_add_left (realProperty flag) finiteBound)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicHeight
