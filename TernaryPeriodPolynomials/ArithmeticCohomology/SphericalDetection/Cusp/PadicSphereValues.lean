module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicSphereRecurrence

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspFiniteEvaluation (cusp : CuspidalRepresentation) (base : BinaryFiniteGL) : cusp.smooth →ₗ[ℂ] ℂ where
  toFun vector := cusp.realize vector (atFinite base)
  map_add' first second := congrFun (map_add cusp.realize first second) (atFinite base)
  map_smul' scalar vector := congrFun (map_smul cusp.realize scalar vector) (atFinite base)

def cuspLocalPadicSphereValue (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (power : ℕ) : ℂ :=
  cusp.realize (cuspLocalPadicSphereOperator cusp place power vector) (atFinite base)

theorem cuspLocalPadicSphereValue_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) :
    cuspLocalPadicSphereValue cusp vector base place 0 = cusp.realize vector (atFinite base) := rfl

theorem cuspLocalPadicSphereValue_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    cuspLocalPadicSphereValue cusp vector base place 1 = eigenvalue * cusp.realize vector (atFinite base) := by
  simp only [cuspLocalPadicSphereValue, eigen, map_smul, Pi.smul_apply, smul_eq_mul]

theorem cuspLocalPadicSphereValue_two (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (eigenvalue : ℂ) (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    cuspLocalPadicSphereValue cusp vector base place 2 =
      (eigenvalue ^ 2 - ((Rat.HeightOneSpectrum.primesEquiv place).val + 1 : ℂ) *
        cuspLocalPadicCentralChar cusp place) * cusp.realize vector (atFinite base) := by
  have identity := congrArg (cuspFiniteEvaluation cusp base)
    (cuspLocalPadicSphereOperator_step_one cusp place vector spherical)
  rw [eigen, map_smul, eigen] at identity
  simp only [map_smul, map_add, map_nsmul, smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at identity
  change eigenvalue * (eigenvalue * cusp.realize vector (atFinite base)) =
    cusp.realize (cuspLocalPadicSphereOperator cusp place 2 vector) (atFinite base) +
      (((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) + 1) *
        (cuspLocalPadicCentralChar cusp place * cusp.realize vector (atFinite base)) at identity
  unfold cuspLocalPadicSphereValue
  linear_combination -identity

theorem cuspLocalPadicSphereValue_recurrence (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (eigenvalue : ℂ) (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (power : ℕ) :
    cuspLocalPadicSphereValue cusp vector base place (power + 3) =
      eigenvalue * cuspLocalPadicSphereValue cusp vector base place (power + 2) -
        (Rat.HeightOneSpectrum.primesEquiv place).val * cuspLocalPadicCentralChar cusp place *
          cuspLocalPadicSphereValue cusp vector base place (power + 1) := by
  have identity := congrArg (cuspFiniteEvaluation cusp base)
    (cuspLocalPadicSphereOperator_step_succ cusp place vector spherical power)
  rw [eigen, map_smul] at identity
  simp only [map_smul, map_add, map_nsmul, smul_eq_mul, nsmul_eq_mul] at identity
  change eigenvalue * cusp.realize (cuspLocalPadicSphereOperator cusp place (power + 2) vector) (atFinite base) =
    cusp.realize (cuspLocalPadicSphereOperator cusp place (power + 3) vector) (atFinite base) +
      (Rat.HeightOneSpectrum.primesEquiv place).val * (cuspLocalPadicCentralChar cusp place *
        cusp.realize (cuspLocalPadicSphereOperator cusp place (power + 1) vector) (atFinite base)) at identity
  unfold cuspLocalPadicSphereValue
  linear_combination -identity

end TernaryPeriodPolynomials.SphericalDetection.Helpers
