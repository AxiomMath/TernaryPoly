module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.PeriodClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.FinAvgLeviInvariance

@[expose] public section


/-!
# The finite average of the twisted Eichler normal form and the arithmetic period class

Let `v` be a classical vector of rotation weight `2k = -(n + 3)`, let `w` be its finite good-line
average at the exponent `s`, and let `f` be the cusp form of `w`. The finite average of the
twisted Eichler normal form `N⁻` of the scalar weighted realization of `v` is the parity-zero
arithmetic cocycle of `f` on all of `GL₂(ℤ)`: on `SL₂(ℤ)` it is `½ (c_f(γ) + R c_f(ε γ ε))`, where
`c_f` is the classical period cocycle, `R` the reflection `(X, Y) ↦ (X, -Y)` and
`ε = diag(-1, 1)`, and it is unchanged by right multiplication by `ε`. Hence, at
`s = n/2 + 3 + s₀`, if the finite average of `N⁻` is a coboundary of `GL₂(ℤ)` acting on
`Sym^{n+1}` without determinant twist, then the arithmetic period class of `w` vanishes.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-! ### The realization of the finite average -/

theorem realize_cuspClassicalFiniteAverageFamily (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL) :
    cusp.realize (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
        exponent vector).val (atInfinity real) =
      cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector real := by
  rw [cuspClassicalFiniteAverageFamily_apply cusp central_positive halfWeight negative exponent
    convergent]
  exact congrFun (cuspClassicalFiniteAverageOperator_realization cusp central_positive halfWeight
    negative exponent convergent vector) real

/-- The integral matrix `ε = diag(-1, 1)` is `J` in `GL₂(ℝ)`. -/
theorem map_integralDeterminantSection_neg_one :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (integralDeterminantSection (-1)) =
      UpperHalfPlane.J := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, integralDeterminantSection]

theorem finiteLeviMatrix_section_mul_self :
    finiteLeviMatrix (integralDeterminantSection (-1)) *
      finiteLeviMatrix (integralDeterminantSection (-1)) = 1 := by
  unfold finiteLeviMatrix
  rw [← map_mul, ← map_mul, Int.units_mul_self, map_one, map_one]

theorem cuspSpherical_realize_mul_finiteLevi (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (A : GeneralLinearGroup (Fin 2) ℤ) (point : BinaryAdelicGL) :
    cusp.realize vector (point * atFinite (finiteLeviMatrix A)) = cusp.realize vector point := by
  have fixed : (⟨cusp.π (atFinite (finiteLeviMatrix A)) vector.val,
      cusp.smooth_stable _ _ vector.property⟩ : cusp.smooth) = vector := by
    apply Subtype.ext
    change cusp.π (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) A)) vector.val =
      vector.val
    rw [← map_integralEmbedding_intCast]
    exact spherical _
  rw [← cusp.equivariant, fixed]

/-- **Spherical vectors are invariant under `J` at the real place**, by automorphy under the
rational matrix `ε = diag(-1, 1)`. -/
theorem cuspSpherical_realize_J_mul (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (real : BinaryRealGL) :
    cusp.realize vector (atInfinity (UpperHalfPlane.J * real)) =
      cusp.realize vector (atInfinity real) := by
  set section_finite := finiteLeviMatrix (integralDeterminantSection (-1))
  have product : atInfinity (UpperHalfPlane.J * real) =
      GeneralLinearGroup.map rationalAdele
          (GeneralLinearGroup.map (Int.castRingHom ℚ) (integralDeterminantSection (-1))) *
        (atInfinity real * atFinite section_finite) := by
    rw [rationalAdele_intMatrix]
    change atInfinity (UpperHalfPlane.J * real) = atInfinity (GeneralLinearGroup.map
      (Int.castRingHom ℝ) (integralDeterminantSection (-1))) * atFinite section_finite *
        (atInfinity real * atFinite section_finite)
    rw [map_integralDeterminantSection_neg_one, ← mul_assoc,
      mul_assoc (atInfinity UpperHalfPlane.J),
      ← (atInfinity_commute_atFinite real section_finite).eq, ← mul_assoc, mul_assoc,
      ← atFinite_mul, finiteLeviMatrix_section_mul_self, atFinite_one, mul_one, atInfinity_mul]
  rw [product, cusp.leftRational, cuspSpherical_realize_mul_finiteLevi cusp vector spherical]

/-! ### The Eichler period of a cusp form -/

/-- The Eichler period of a cusp form is its holomorphic primitive vanishing at `i`. -/
theorem eichlerPeriod_cuspForm {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    {z : ℂ} (positive : 0 < z.im) (h : BinaryAdelicGL) :
    eichlerPeriod n (fun _ point => form (UpperHalfPlane.ofComplex point)) z h =
      classicalBinaryPrimitive form (n + 1) z := by
  have holomorphic : ∀ base : BinaryAdelicGL, DifferentiableOn ℂ
      ((fun (_ : BinaryAdelicGL) point => form (UpperHalfPlane.ofComplex point)) base)
      {w : ℂ | 0 < w.im} :=
    fun _ => UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo form)
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  set L := (binaryWeightBasis (n + 1)).coord j
  set Φ : ℂ → ℂ := fun w =>
    L (eichlerPeriod n (fun _ point => form (UpperHalfPlane.ofComplex point)) w h) -
      L (classicalBinaryPrimitive form (n + 1) w)
  have derivative : ∀ w : ℂ, 0 < w.im → HasDerivAt Φ 0 w := by
    intro w hw
    refine ((hasDerivAt_coord_eichlerPeriod _ holomorphic hw h j).sub
      (classicalBinaryPrimitive_hasDerivAt form (n + 1) L w hw)).congr_deriv ?_
    rw [classicalBinaryForm, map_smul, smul_eq_mul, sub_self]
  have constant := eichlerUpperSet_isOpen.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun w hw => (derivative w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (derivative w hw).deriv) (x := z) (y := Complex.I) positive (by simp)
  simp only [Φ, eichlerPeriod_I_eq_zero, classicalBinaryPrimitive_basepoint, Pi.zero_apply,
    map_zero, sub_zero] at constant
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply]
  exact sub_eq_zero.mp constant

/-! ### The finite average of the Eichler period -/

theorem eichlerTwisted_eq_map_sub (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerTwisted n F C = fun h =>
      ((2 : ℂ)⁻¹ • LinearMap.id : Module.End ℂ (Binary.HomogeneousPoly (n + 1)))
          (eichlerPeriod n F (basePoint C) (h * atInfinity 1)) -
        ((2 : ℂ)⁻¹ • binaryCoefficient n UpperHalfPlane.J)
          (eichlerPeriod n F (binaryComplexReflection (basePoint C))
            (h * atInfinity UpperHalfPlane.J)) := by
  funext h
  have unimodular : |(UpperHalfPlane.J : BinaryRealGL).val.det| = 1 := by
    rw [det_upperJ]
    norm_num
  rw [eichlerTwisted, eichlerHolomorphic, eichlerAntiholomorphic,
    binaryAmbientRepresentation_apply_of_unimodular unimodular, atInfinity_one, mul_one]
  rfl

section Average

variable (cusp : CuspidalRepresentation)
  (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
  (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cuspClassicalVectors cusp halfWeight)
  (exponent : ℂ) (convergent : 3 < exponent.re)

include convergent

/-- **The finite average of the Eichler period** of the scalar weighted realization of `v`,
translated on the right by a real matrix `A` that fixes the realization of the finite average
`w` of `v`, is the holomorphic primitive of the cusp form of `w`. -/
theorem finiteAverageBinary_eichlerPeriod (A : BinaryRealGL)
    (invariant : ∀ real, cusp.realize (cuspClassicalFiniteAverageFamily cusp central_positive
      halfWeight negative exponent vector).val (atInfinity (A * real)) =
        cusp.realize (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
          exponent vector).val (atInfinity real))
    {z : ℂ} (positive : 0 < z.im) :
    FiniteAverageIntegrable exponent (fun h =>
        eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector.val) z
          (h * atInfinity A)) ∧
      finiteAverageBinary exponent (fun h =>
        eichlerPeriod n (cuspScalarWeightedRealization cusp halfWeight vector.val) z
          (h * atInfinity A)) =
        classicalBinaryPrimitive (cuspClassicalFormMap cusp halfWeight negative
          (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
            vector)) (n + 1) z := by
  refine ⟨fun j => (coord_finiteAverageBinary_eichlerPeriod cusp halfWeight vector exponent
    convergent A positive j).1 j, ?_⟩
  rw [← eichlerPeriod_cuspForm _ positive 1]
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply,
    (coord_finiteAverageBinary_eichlerPeriod cusp halfWeight vector exponent convergent A
      positive j).2, coord_eichlerPeriod_clamped]
  apply intervalIntegral.integral_congr
  intro t _
  have upper := clampedPath_im_pos z positive t
  dsimp only
  rw [← realize_cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative
    exponent convergent, invariant]
  have value := congrFun (cuspClassicalFormMap_coe cusp halfWeight negative
    (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent vector))
    (UpperHalfPlane.ofComplex (clampedPath z t))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos upper] at value
  simp only [clampedIntegrand, endpointCoefficient]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos upper, value]
  change _ = _ * (((clampedPath z t).im ^ halfWeight : ℝ) • cusp.realize _
    (1 * atInfinity (invertibleMatrix (binaryUpperSectionMatrix (clampedPath z t))))) * _
  rw [one_mul, Complex.real_smul]
  ring

/-- **The finite average of the twisted Eichler normal form**
`½ Per(C · i) - ½ J · Per(-conj(C · i))`. -/
theorem finiteAverageBinary_eichlerTwisted (C : BinaryRealGL) :
    finiteAverageBinary exponent
        (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val) C) =
      (2 : ℂ)⁻¹ • classicalBinaryPrimitive (cuspClassicalFormMap cusp halfWeight negative
          (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
            vector)) (n + 1) (basePoint C) -
        (2 : ℂ)⁻¹ • binaryCoefficient n UpperHalfPlane.J
          (classicalBinaryPrimitive (cuspClassicalFormMap cusp halfWeight negative
            (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
              vector)) (n + 1) (binaryComplexReflection (basePoint C))) := by
  have holomorphic := finiteAverageBinary_eichlerPeriod (n := n) cusp central_positive halfWeight
    negative vector exponent convergent 1 (fun real => by rw [one_mul]) (basePoint_im_pos C)
  have antiholomorphic := finiteAverageBinary_eichlerPeriod (n := n) cusp central_positive
    halfWeight negative vector exponent convergent UpperHalfPlane.J
    (fun real => cuspSpherical_realize_J_mul cusp _ (cuspClassicalFiniteAverageFamily cusp
      central_positive halfWeight negative exponent vector).property.1 real)
    (by rw [binaryComplexReflection_im]; exact basePoint_im_pos C)
  rw [eichlerTwisted_eq_map_sub, finiteAverageBinary_map_sub holomorphic.1 antiholomorphic.1,
    holomorphic.2, antiholomorphic.2]
  rfl

end Average

/-! ### Identification with the arithmetic period cocycle -/

theorem binaryCoefficient_J_apply (even : Even (n + 1))
    (polynomial : Binary.HomogeneousPoly (n + 1)) :
    binaryCoefficient n UpperHalfPlane.J polynomial =
      -binaryParityReflection (n + 1) polynomial := by
  have equality : binaryCoefficient n UpperHalfPlane.J =
      (arithmeticBinaryRep (n + 1) (-1)).ρ (integralDeterminantSection (-1)) := by
    change Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J) =
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (integralDeterminantSection (-1)))
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, integralDeterminantSection]
  rw [equality]
  exact @Eq.trans (Binary.HomogeneousPoly (n + 1)) _ _ _
    (arithmeticBinaryRep_section_neg_one (n + 1) (-1) even polynomial)
    (by
      rw [_root_.zpow_neg, zpow_one, inv_neg, inv_one]
      exact neg_one_smul ℂ (binaryParityReflection (n + 1) polynomial))

theorem map_toGL_eq_mapGL (special : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special) =
      SpecialLinearGroup.mapGL ℝ special := by
  apply Units.ext
  ext i j
  simp [SpecialLinearGroup.mapGL]

theorem map_toGL_modularReflection (special : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℝ)
        (SpecialLinearGroup.toGL (modularReflection special)) =
      UpperHalfPlane.J *
        GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special) *
        UpperHalfPlane.J := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, modularReflection_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]

section Cocycle

variable (cusp : CuspidalRepresentation)
  (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
  (halfWeight : ℤ) (negative : halfWeight < 0) (vector : cuspClassicalVectors cusp halfWeight)
  (exponent : ℂ) (convergent : 3 < exponent.re)
  (weight_eq : -2 * halfWeight = ((n + 1 : ℕ) : ℤ) + 2) (even : Even (n + 1))
  (sign : (-1 : ℂ) ^ (0 : ℤ) = (-1 : ℂ) ^ (0 : ℕ))

include convergent

theorem finiteAverageBinary_eichlerTwisted_specialLinear (special : SpecialLinearGroup (Fin 2) ℤ) :
    finiteAverageBinary exponent
        (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
          (GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special))) =
      classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
          (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
            vector)) (n + 1) weight_eq even 0 0 sign (SpecialLinearGroup.toGL special) := by
  have base : basePoint (GeneralLinearGroup.map (Int.castRingHom ℝ)
      (SpecialLinearGroup.toGL special)) =
      ((SpecialLinearGroup.mapGL ℝ special • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
    rw [basePoint, map_toGL_eq_mapGL]
  have reflected : binaryComplexReflection (basePoint (GeneralLinearGroup.map (Int.castRingHom ℝ)
      (SpecialLinearGroup.toGL special))) =
      ((SpecialLinearGroup.mapGL ℝ (modularReflection special) • UpperHalfPlane.I :
        UpperHalfPlane) : ℂ) := by
    rw [← map_toGL_eq_mapGL, ← basePoint, map_toGL_modularReflection, basePoint_mul_J,
      basePoint_J_mul]
  have value : classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
        vector)) (n + 1) weight_eq even 0 0 sign (SpecialLinearGroup.toGL special) =
      (2 : ℂ)⁻¹ • (classicalBinaryPrimitive (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
          vector)) (n + 1) ((SpecialLinearGroup.mapGL ℝ special • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ) +
        binaryParityReflection (n + 1) (classicalBinaryPrimitive (cuspClassicalFormMap cusp
          halfWeight negative (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight
            negative exponent vector)) (n + 1)
          ((SpecialLinearGroup.mapGL ℝ (modularReflection special) • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ))) := by
    rw [classicalArithmeticCocycle, arithmeticParityCocycle_specialLinear,
      modularCocycleParity_apply]
    simp only [pow_zero, one_smul]
    rfl
  rw [finiteAverageBinary_eichlerTwisted cusp central_positive halfWeight negative vector exponent
    convergent, reflected, base, binaryCoefficient_J_apply even]
  refine Eq.trans ?_ value.symm
  simp only [smul_neg, sub_neg_eq_add, smul_add]

/-- **The finite average of the twisted Eichler normal form is the parity-zero arithmetic
cocycle** of the cusp form of the finite average on all of `GL₂(ℤ)`. -/
theorem finiteAverageBinary_eichlerTwisted_eq_cocycle (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    finiteAverageBinary exponent
        (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
          (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix)) =
      classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
          (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
            vector)) (n + 1) weight_eq even 0 0 sign matrix := by
  obtain ⟨special, unit, rfl⟩ := split_exists_pair integralDeterminantSplitting matrix
  change finiteAverageBinary exponent
      (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
        (GeneralLinearGroup.map (Int.castRingHom ℝ)
          (SpecialLinearGroup.toGL special * integralDeterminantSection unit))) =
    classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
          vector)) (n + 1) weight_eq even 0 0 sign
      (SpecialLinearGroup.toGL special * integralDeterminantSection unit)
  have section_zero : classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
        vector)) (n + 1) weight_eq even 0 0 sign (integralDeterminantSection unit) = 0 :=
    arithmeticParityCocycle_section (n + 1) 0 even 0 sign _ unit
  have law : classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
        vector)) (n + 1) weight_eq even 0 0 sign
        (SpecialLinearGroup.toGL special * integralDeterminantSection unit) =
      (arithmeticBinaryRep (n + 1) 0).ρ (SpecialLinearGroup.toGL special)
        (classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
          (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
            vector)) (n + 1) weight_eq even 0 0 sign (integralDeterminantSection unit)) +
      classicalArithmeticCocycle (cuspClassicalFormMap cusp halfWeight negative
        (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight negative exponent
          vector)) (n + 1) weight_eq even 0 0 sign (SpecialLinearGroup.toGL special) :=
    (groupCohomology.mem_cocycles₁_iff _).mp (classicalArithmeticCocycle _ (n + 1) weight_eq
      even 0 0 sign).property _ _
  rw [section_zero, map_zero, zero_add] at law
  have average : finiteAverageBinary exponent
      (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
        (GeneralLinearGroup.map (Int.castRingHom ℝ)
          (SpecialLinearGroup.toGL special * integralDeterminantSection unit))) =
      finiteAverageBinary exponent
        (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
          (GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special))) := by
    rcases Int.units_eq_one_or unit with rfl | rfl
    · rw [map_one, mul_one]
    · rw [map_mul, map_integralDeterminantSection_neg_one, eichlerTwisted_mul_J]
  exact average.trans ((finiteAverageBinary_eichlerTwisted_specialLinear cusp central_positive
    halfWeight negative vector exponent convergent weight_eq even sign special).trans law.symm)

end Cocycle

/-- **Vanishing of the arithmetic period class of the finite average.** If the finite average,
at `s = n/2 + 3 + s₀`, of the twisted Eichler normal form of the scalar weighted realization of
a classical vector `v` of rotation weight `-(n + 3)` is a coboundary of `GL₂(ℤ)` acting on
`Sym^{n+1}` without determinant twist, then the parity-zero arithmetic period class of the
finite average of `v` vanishes. -/
theorem cuspClassicalArithmeticPeriodMap_finiteAverage_eq_zero (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val →
      cusp.centralCharacter (realAdeleUnit unit) = 1)
    (large : 9 ≤ n) (odd : Odd n) (halfWeight : ℤ) (weight : 2 * halfWeight = -((n : ℤ) + 3))
    (vector : cuspClassicalVectors cusp halfWeight)
    (coboundary : ∃ potential : arithmeticBinaryRep (n + 1) 0,
      ∀ matrix : GeneralLinearGroup (Fin 2) ℤ,
        finiteAverageBinary ((n : ℂ) / 2 + 3 + cohomologicalPoint)
            (eichlerTwisted n (cuspScalarWeightedRealization cusp halfWeight vector.val)
              (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix)) =
          (arithmeticBinaryRep (n + 1) 0).ρ matrix potential - potential) :
    cuspClassicalArithmeticPeriodMap cusp halfWeight (by omega) (n + 1) (by omega)
      (by obtain ⟨half, equality⟩ := odd; exact ⟨half + 1, by omega⟩) 0 0 (by norm_num)
      (cuspClassicalFiniteAverageFamily cusp central_positive halfWeight (by omega)
        ((n : ℂ) / 2 + 3 + cohomologicalPoint) vector) = 0 := by
  have convergent : 3 < ((n : ℂ) / 2 + 3 + cohomologicalPoint).re := by
    have degree_large : (9 : ℝ) ≤ n := by exact_mod_cast large
    norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
    linarith
  obtain ⟨potential, boundary⟩ := coboundary
  rw [cuspClassicalArithmeticPeriodMap_apply, groupCohomology.H1π_eq_zero_iff]
  refine ⟨potential, funext fun matrix => ?_⟩
  exact (groupCohomology.d₀₁_hom_apply _ _ _).trans ((boundary matrix).symm.trans
    (finiteAverageBinary_eichlerTwisted_eq_cocycle cusp central_positive halfWeight (by omega)
      vector _ convergent _ _ _ matrix))

end TernaryPeriodPolynomials.AnalyticClasses
