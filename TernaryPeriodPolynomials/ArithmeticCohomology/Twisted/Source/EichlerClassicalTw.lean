module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerTwLift
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Averaged.PeriodClassCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodInjective

@[expose] public section


/-!
# The twisted Eichler cocycle on `GL₂(ℤ)` is the classical period cocycle

For an Eichler input `D` (a spherical holomorphic lowest-weight vector) let `f` be the cusp form
of level one attached to `D.vector`.  The twisted Eichler cocycle `eichlerCocycleTw D`, evaluated at
the adelic point `1` and on an integral matrix `m ∈ GL₂(ℤ)`, is the parity-zero arithmetic period
cocycle of `f`.  Consequently its class in `H¹(GL₂(ℤ), Sym^{n+1})` is nonzero, because the
arithmetic period map is injective on classical vectors.

The pointwise identification is the evaluation at the adelic point `1` of the argument used for
the finite average: the Eichler periods of the scalar realization and of `f` agree at the points
`1` and `atInfinity J`, by sphericality, and the twisted normal form of a cusp form on `GL₂(ℤ)` is
the arithmetic cocycle on `SL₂(ℤ)` and is invariant under right multiplication by `J`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.TwistedSource

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

section CuspForm

variable {n : ℕ} {weight : ℤ}
  (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)

/-- The twisted Eichler normal form of the constant family given by a cusp form is the
antisymmetrised period of the cusp form. -/
theorem eichlerTwisted_cuspForm (C : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point)) C h =
      (2 : ℂ)⁻¹ • classicalBinaryPrimitive form (n + 1) (basePoint C) -
        (2 : ℂ)⁻¹ • binaryCoefficient n UpperHalfPlane.J
          (classicalBinaryPrimitive form (n + 1) (binaryComplexReflection (basePoint C))) := by
  have positive := basePoint_im_pos C
  have reflected : 0 < (binaryComplexReflection (basePoint C)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  rw [eichlerTwisted_eq_map_sub]
  beta_reduce
  rw [eichlerPeriod_cuspForm form positive, eichlerPeriod_cuspForm form reflected]
  rfl

/-- On `SL₂(ℤ)` the twisted normal form of a cusp form is the parity-zero arithmetic cocycle. -/
theorem eichlerTwisted_cuspForm_specialLinear (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2)
    (even : Even (n + 1)) (sign : (-1 : ℂ) ^ (0 : ℤ) = (-1 : ℂ) ^ (0 : ℕ))
    (special : SpecialLinearGroup (Fin 2) ℤ) (h : BinaryAdelicGL) :
    eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point))
        (GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special)) h =
      classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
        (SpecialLinearGroup.toGL special) := by
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
  have value : classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
      (SpecialLinearGroup.toGL special) =
      (2 : ℂ)⁻¹ • (classicalBinaryPrimitive form (n + 1)
          ((SpecialLinearGroup.mapGL ℝ special • UpperHalfPlane.I : UpperHalfPlane) : ℂ) +
        binaryParityReflection (n + 1) (classicalBinaryPrimitive form (n + 1)
          ((SpecialLinearGroup.mapGL ℝ (modularReflection special) • UpperHalfPlane.I :
            UpperHalfPlane) : ℂ))) := by
    rw [classicalArithmeticCocycle, arithmeticParityCocycle_specialLinear,
      modularCocycleParity_apply]
    simp only [pow_zero, one_smul]
    rfl
  rw [eichlerTwisted_cuspForm (n := n) form _ h, reflected, base, binaryCoefficient_J_apply even]
  refine Eq.trans ?_ value.symm
  simp only [smul_neg, sub_neg_eq_add, smul_add]

/-- **The twisted normal form of a cusp form is the parity-zero arithmetic cocycle** on all of
`GL₂(ℤ)`. -/
theorem eichlerTwisted_cuspForm_eq_cocycle (weight_eq : weight = ((n + 1 : ℕ) : ℤ) + 2)
    (even : Even (n + 1)) (sign : (-1 : ℂ) ^ (0 : ℤ) = (-1 : ℂ) ^ (0 : ℕ))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (h : BinaryAdelicGL) :
    eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point))
        (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) h =
      classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign matrix := by
  obtain ⟨special, unit, rfl⟩ := split_exists_pair integralDeterminantSplitting matrix
  change eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point))
      (GeneralLinearGroup.map (Int.castRingHom ℝ)
        (SpecialLinearGroup.toGL special * integralDeterminantSection unit)) h =
    classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
      (SpecialLinearGroup.toGL special * integralDeterminantSection unit)
  have section_zero : classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
      (integralDeterminantSection unit) = 0 :=
    arithmeticParityCocycle_section (n + 1) 0 even 0 sign _ unit
  have law : classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
        (SpecialLinearGroup.toGL special * integralDeterminantSection unit) =
      (arithmeticBinaryRep (n + 1) 0).ρ (SpecialLinearGroup.toGL special)
        (classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
          (integralDeterminantSection unit)) +
      classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign
        (SpecialLinearGroup.toGL special) :=
    (groupCohomology.mem_cocycles₁_iff _).mp
      (classicalArithmeticCocycle form (n + 1) weight_eq even 0 0 sign).property _ _
  rw [section_zero, map_zero, zero_add] at law
  have average : eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point))
        (GeneralLinearGroup.map (Int.castRingHom ℝ)
          (SpecialLinearGroup.toGL special * integralDeterminantSection unit)) h =
      eichlerTwisted n (fun _ point => form (UpperHalfPlane.ofComplex point))
        (GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL special)) h := by
    rcases Int.units_eq_one_or unit with rfl | rfl
    · rw [map_one, mul_one]
    · rw [map_mul, map_integralDeterminantSection_neg_one, eichlerTwisted_mul_J]
  exact average.trans ((eichlerTwisted_cuspForm_specialLinear form weight_eq even sign special
    h).trans law.symm)

end CuspForm

section Input

variable {σ : CuspidalRepresentation} {n : ℕ}
  (D : SourceConstruction.EichlerInput σ n)

theorem eichlerInput_halfWeight_neg : D.halfWeight < 0 := by
  have := D.weight
  omega

/-- The vector of an Eichler input is a classical vector. -/
theorem eichlerInput_mem_classical : D.vector ∈ cuspClassicalVectors σ D.halfWeight :=
  cuspClassicalVectors_mem_of_holomorphic σ D.halfWeight D.vector D.vector_spherical D.rotation
    (cuspScalarWeightedRealization_holomorphic σ D.halfWeight D.vector D.vector_spherical
      D.rotation D.holomorphic 1)

/-- The level-one cusp form attached to the vector of an Eichler input. -/
def classicalFormOfEichlerInput :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * D.halfWeight) :=
  cuspClassicalFormMap σ D.halfWeight (eichlerInput_halfWeight_neg D)
    ⟨D.vector, eichlerInput_mem_classical D⟩

theorem classicalFormOfEichlerInput_weight_eq :
    -2 * D.halfWeight = ((n + 1 : ℕ) : ℤ) + 2 := by
  have := D.weight
  push_cast
  omega

theorem even_succ_of_odd_tw (hn : Odd n) : Even (n + 1) := by
  obtain ⟨half, equality⟩ := hn
  exact ⟨half + 1, by omega⟩

theorem sign_zero_zero_tw : (-1 : ℂ) ^ (0 : ℤ) = (-1 : ℂ) ^ (0 : ℕ) := by
  norm_num

/-- The parity-zero twist-zero arithmetic cocycle of the cusp form of an Eichler input. -/
def eichlerClassicalCocycle (hn : Odd n) :
    groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0) :=
  classicalArithmeticCocycle (classicalFormOfEichlerInput D) (n + 1)
    (classicalFormOfEichlerInput_weight_eq D) (even_succ_of_odd_tw hn) 0 0 sign_zero_zero_tw

/-- At a point `g` fixing the vector under right translation by every real matrix, the scalar
realization is the cusp form. -/
theorem endpointScalar_eq_classicalForm (g : BinaryAdelicGL)
    (hg : ∀ real : BinaryRealGL,
      σ.realize D.vector (g * atInfinity real) = σ.realize D.vector (atInfinity real))
    (w : ℂ) (hw : 0 < w.im) :
    endpointScalar σ D.halfWeight D.vector g w =
      classicalFormOfEichlerInput D (UpperHalfPlane.ofComplex w) := by
  have value : classicalFormOfEichlerInput D (UpperHalfPlane.ofComplex w) =
      cuspScalarWeightedRealization σ D.halfWeight D.vector 1
        ((UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ) :=
    congrFun (cuspClassicalFormMap_coe σ D.halfWeight (eichlerInput_halfWeight_neg D)
      ⟨D.vector, eichlerInput_mem_classical D⟩) (UpperHalfPlane.ofComplex w)
  rw [value, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  show cuspScalarWeightedRealization σ D.halfWeight D.vector g w =
    cuspScalarWeightedRealization σ D.halfWeight D.vector 1 w
  unfold cuspScalarWeightedRealization cuspScalarAffineRealization
  rw [hg, one_mul]

/-- The Eichler periods of the scalar realization and of the cusp form agree at such a point. -/
theorem eichlerPeriod_endpointScalar_eq_classicalForm {z : ℂ} (hz : 0 < z.im)
    (g : BinaryAdelicGL)
    (hg : ∀ real : BinaryRealGL,
      σ.realize D.vector (g * atInfinity real) = σ.realize D.vector (atInfinity real)) :
    eichlerPeriod n (endpointScalar σ D.halfWeight D.vector) z g =
      eichlerPeriod n (fun _ point => classicalFormOfEichlerInput D
        (UpperHalfPlane.ofComplex point)) z g := by
  unfold eichlerPeriod
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have path : clampedPath z t = eichlerPath z t := clampedPath_eqOn z ht
  have upper : 0 < (eichlerPath z t).im := by
    rw [← path]
    exact clampedPath_im_pos z hz t
  have value := endpointScalar_eq_classicalForm D g hg (eichlerPath z t) upper
  simp only [eichlerIntegrand, value]

theorem hg_one_tw : ∀ real : BinaryRealGL,
    σ.realize D.vector (1 * atInfinity (1 : BinaryRealGL) * atInfinity real) =
      σ.realize D.vector (atInfinity real) := by
  intro real
  rw [atInfinity_one, one_mul, one_mul]

theorem hg_J_tw : ∀ real : BinaryRealGL,
    σ.realize D.vector (1 * atInfinity UpperHalfPlane.J * atInfinity real) =
      σ.realize D.vector (atInfinity real) := by
  intro real
  rw [one_mul, ← atInfinity_mul]
  exact cuspSpherical_realize_J_mul σ D.vector D.vector_spherical real

/-- The twisted normal form of the scalar realization at the adelic point `1` is that of the
cusp form. -/
theorem eichlerTwisted_endpointScalar_one (A : BinaryRealGL) :
    eichlerTwisted n (endpointScalar σ D.halfWeight D.vector) A 1 =
      eichlerTwisted n (fun _ point => classicalFormOfEichlerInput D
        (UpperHalfPlane.ofComplex point)) A 1 := by
  have positive := basePoint_im_pos A
  have reflected : 0 < (binaryComplexReflection (basePoint A)).im := by
    rw [binaryComplexReflection_im]
    exact positive
  rw [eichlerTwisted_eq_map_sub, eichlerTwisted_eq_map_sub]
  beta_reduce
  rw [eichlerPeriod_endpointScalar_eq_classicalForm D positive _ (hg_one_tw D),
    eichlerPeriod_endpointScalar_eq_classicalForm D reflected _ (hg_J_tw D)]

theorem eichlerCocycleTw_one_eq_eichlerTwisted
    (stages : PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages σ) (A : BinaryRealGL) :
    eichlerCocycleTw D A 1 = eichlerTwisted n (endpointScalar σ D.halfWeight D.vector) A 1 := by
  rw [eichlerCocycleTw_eq_eichlerNormalTw D stages A]
  simp only [eichlerNormalTw, eichlerTwisted, eichlerHolomorphic, eichlerAntiholomorphic,
    smul_sub]

/-- **The twisted Eichler cocycle on `GL₂(ℤ)` is the classical period cocycle.**  At the adelic
point `1` and on an integral matrix, it is the parity-zero arithmetic period cocycle of the cusp
form of the Eichler input. -/
theorem eichlerCocycleTw_integral_eq_classical
    (stages : PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages σ) (hn : Odd n)
    (m : GeneralLinearGroup (Fin 2) ℤ) :
    eichlerCocycleTw D (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 =
      classicalArithmeticCocycle (classicalFormOfEichlerInput D) (n + 1)
        (classicalFormOfEichlerInput_weight_eq D) (even_succ_of_odd_tw hn) 0 0
        sign_zero_zero_tw m := by
  rw [eichlerCocycleTw_one_eq_eichlerTwisted D stages, eichlerTwisted_endpointScalar_one D]
  exact eichlerTwisted_cuspForm_eq_cocycle (classicalFormOfEichlerInput D) _ _ _ m 1

/-- **The Levi class of the twisted Eichler cocycle is nonzero**: the restriction of
`eichlerCocycleTw D` at the adelic point `1` to `GL₂(ℤ)` is a genuine one-cocycle of
`Sym^{n+1}` whose class in `H¹` is nonzero. -/
theorem eichlerCocycleTw_class_ne_zero
    (stages : PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages σ) (hn : Odd n) :
    ∃ φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0),
      (∀ m : GeneralLinearGroup (Fin 2) ℤ, (φ m : Binary.HomogeneousPoly (n + 1)) =
        eichlerCocycleTw D (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0 := by
  refine ⟨eichlerClassicalCocycle D hn,
    fun m => (eichlerCocycleTw_integral_eq_classical D stages hn m).symm, ?_⟩
  have injective := cuspClassicalArithmeticPeriodMap_injective σ D.central_positive D.halfWeight
    (eichlerInput_halfWeight_neg D) (n + 1) (classicalFormOfEichlerInput_weight_eq D)
    (even_succ_of_odd_tw hn) 0 0 (by simp)
  have nonzero : cuspClassicalArithmeticPeriodMap σ D.halfWeight (eichlerInput_halfWeight_neg D)
      (n + 1) (classicalFormOfEichlerInput_weight_eq D) (even_succ_of_odd_tw hn) 0 0
      sign_zero_zero_tw ⟨D.vector, eichlerInput_mem_classical D⟩ ≠ 0 := by
    intro zero
    apply D.vector_ne
    have equal := injective (zero.trans (map_zero _).symm)
    exact congrArg Subtype.val equal
  rw [cuspClassicalArithmeticPeriodMap_apply] at nonzero
  exact nonzero

end Input

end TernaryPeriodPolynomials.TwistedSource

end
