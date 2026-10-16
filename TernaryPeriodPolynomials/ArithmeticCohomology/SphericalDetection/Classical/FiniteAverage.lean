module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerTruncation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspClassicalRealization (cusp : CuspidalRepresentation) (halfWeight : ℤ) :
    cuspClassicalVectors cusp halfWeight →ₗ[ℂ] (BinaryRealGL → ℂ) where
  toFun vector real := cusp.realize vector.val (atInfinity real)
  map_add' first second := by ext real; simp
  map_smul' scalar vector := by ext real; simp

theorem cuspClassicalRealization_injective (cusp : CuspidalRepresentation) (halfWeight : ℤ) :
    Function.Injective (cuspClassicalRealization cusp halfWeight) := by
  intro first second equality
  apply sub_eq_zero.mp
  by_contra nonzero
  obtain ⟨real, value_nonzero⟩ := cuspRealization_exists_real_nonzero cusp (first - second).val
    (first - second).property.1 (fun zero => nonzero (Subtype.ext zero))
  have zero : cuspClassicalRealization cusp halfWeight (first - second) = 0 := by
    rw [map_sub, equality, sub_self]
  exact value_nonzero (congrFun zero real)

def cuspClassicalFiniteAverage (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (exponent : ℂ) (convergent : 3 < exponent.re) :
    cuspClassicalVectors cusp halfWeight →ₗ[ℂ] (BinaryRealGL → ℂ) where
  toFun vector real := ∫ pair,
    goodLineFinitePadicIntegrand cusp (cuspSmoothAction cusp (atInfinity real) vector.val) exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
  map_add' first second := by
    ext real
    have first_int := goodLineFinitePadicIntegrand_global_integrable cusp
      (cuspSmoothAction cusp (atInfinity real) first.val)
      (cuspSmoothAction_real_spherical cusp first.val first.property.1 real) exponent convergent
    have second_int := goodLineFinitePadicIntegrand_global_integrable cusp
      (cuspSmoothAction cusp (atInfinity real) second.val)
      (cuspSmoothAction_real_spherical cusp second.val second.property.1 real) exponent convergent
    simp only [Submodule.coe_add, goodLineFinitePadicIntegrand, finitePadicCuspIntegrand,
      map_add, Pi.add_apply, mul_add] at *
    exact integral_add first_int second_int
  map_smul' scalar vector := by
    ext real
    simp only [Submodule.coe_smul, goodLineFinitePadicIntegrand, finitePadicCuspIntegrand, map_smul, Pi.smul_apply,
      smul_eq_mul]
    simp_rw [mul_left_comm _ scalar]
    exact integral_const_mul _ _

def cuspClassicalTruncatedEulerEquiv (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) :
    cuspClassicalVectors cusp halfWeight ≃ₗ[ℂ] cuspClassicalVectors cusp halfWeight :=
  (goodLineFinitePadicTruncatedIntegral_classical_equiv cusp central_positive halfWeight negative
    exponent convergent places).choose

theorem cuspClassicalTruncatedEulerEquiv_realization (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) (vector : cuspClassicalVectors cusp halfWeight) (real : BinaryRealGL) :
    cuspClassicalRealization cusp halfWeight
        (cuspClassicalTruncatedEulerEquiv cusp central_positive halfWeight negative exponent convergent places vector) real =
      goodLineFinitePadicTruncatedIntegral cusp (cuspSmoothAction cusp (atInfinity real) vector.val) exponent places :=
  ((goodLineFinitePadicTruncatedIntegral_classical_equiv cusp central_positive halfWeight negative
    exponent convergent places).choose_spec.1 vector real).symm

theorem cuspClassicalTruncatedEulerEquiv_hecke_commute (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (places : Finset FinitePlace) (prime : Nat.Primes) (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalTruncatedEulerEquiv cusp central_positive halfWeight negative exponent convergent places
        (cuspClassicalPrimeHecke cusp central_positive halfWeight prime vector) =
      cuspClassicalPrimeHecke cusp central_positive halfWeight prime
        (cuspClassicalTruncatedEulerEquiv cusp central_positive halfWeight negative exponent convergent places vector) :=
  (goodLineFinitePadicTruncatedIntegral_classical_equiv cusp central_positive halfWeight negative
    exponent convergent places).choose_spec.2 prime vector

theorem cuspClassicalTruncatedEulerEquiv_realization_tendsto (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    Tendsto (fun places => cuspClassicalRealization cusp halfWeight
      (cuspClassicalTruncatedEulerEquiv cusp central_positive halfWeight negative exponent convergent places vector))
      atTop (nhds (cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector)) := by
  apply tendsto_pi_nhds.mpr
  intro real
  simp_rw [cuspClassicalTruncatedEulerEquiv_realization]
  exact goodLineFiniteSupportRegion_integral_tendsto _
    (goodLineFinitePadicIntegrand_global_integrable cusp _
      (cuspSmoothAction_real_spherical cusp vector.val vector.property.1 real) exponent convergent)

theorem cuspClassicalFiniteAverage_mem_range (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector ∈
      (cuspClassicalRealization cusp halfWeight).range := by
  let : FiniteDimensional ℂ (cuspClassicalVectors cusp halfWeight) :=
    cuspClassicalVectors_finiteDimensional cusp central_positive halfWeight negative
  exact (cuspClassicalRealization cusp halfWeight).range.closed_of_finiteDimensional.mem_of_tendsto
    (cuspClassicalTruncatedEulerEquiv_realization_tendsto cusp central_positive halfWeight negative
      exponent convergent vector) (Eventually.of_forall (fun places => ⟨_, rfl⟩))

def cuspClassicalFiniteAverageOperator (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re) :
    Module.End ℂ (cuspClassicalVectors cusp halfWeight) :=
  (LinearEquiv.ofInjective (cuspClassicalRealization cusp halfWeight)
    (cuspClassicalRealization_injective cusp halfWeight)).symm.toLinearMap.comp
      ((cuspClassicalFiniteAverage cusp halfWeight exponent convergent).codRestrict _
        (cuspClassicalFiniteAverage_mem_range cusp central_positive halfWeight negative exponent convergent))

theorem cuspClassicalFiniteAverageOperator_realization (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (exponent : ℂ) (convergent : 3 < exponent.re)
    (vector : cuspClassicalVectors cusp halfWeight) :
    cuspClassicalRealization cusp halfWeight
        (cuspClassicalFiniteAverageOperator cusp central_positive halfWeight negative exponent convergent vector) =
      cuspClassicalFiniteAverage cusp halfWeight exponent convergent vector := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective (cuspClassicalRealization cusp halfWeight)
    (cuspClassicalRealization_injective cusp halfWeight)).apply_symm_apply
      ⟨_, cuspClassicalFiniteAverage_mem_range cusp central_positive halfWeight negative exponent convergent vector⟩)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
