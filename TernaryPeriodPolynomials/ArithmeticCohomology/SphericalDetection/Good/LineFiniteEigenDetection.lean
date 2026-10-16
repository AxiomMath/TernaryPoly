module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEndpointValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspFiniteRationalSlash_real_commute (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (real : BinaryRealGL) (vector : cusp.smooth) :
    cuspFiniteRationalSlash cusp rational (cuspSmoothAction cusp (atInfinity real) vector) =
      cuspSmoothAction cusp (atInfinity real) (cuspFiniteRationalSlash cusp rational vector) := by
  simp only [cuspFiniteRationalSlash, ← cuspSmoothAction_mul]
  rw [(atInfinity_commute_atFinite real (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹)).eq]

theorem cuspPrimeHeckeSum_real_commute (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (real : BinaryRealGL) (vector : cusp.smooth) :
    cuspPrimeHeckeSum cusp prime (cuspSmoothAction cusp (atInfinity real) vector) =
      cuspSmoothAction cusp (atInfinity real) (cuspPrimeHeckeSum cusp prime vector) := by
  simp only [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
    cuspFiniteRationalSlash_real_commute]

theorem cuspSmoothAction_ne_zero (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) : cuspSmoothAction cusp matrix vector ≠ 0 := by
  intro zero
  have reversed := congrArg (cuspSmoothAction cusp matrix⁻¹) zero
  rw [← cuspSmoothAction_mul, inv_mul_cancel, map_zero] at reversed
  apply nonzero
  apply Subtype.ext
  simpa only [cuspSmoothAction, LinearMap.coe_mk, AddHom.coe_mk, map_one, Module.End.one_apply] using
    congrArg Subtype.val reversed

theorem goodLineFiniteVectorIntegral_real_endpointValue (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (form_nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector) (real : BinaryRealGL) :
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint (cuspSmoothAction cusp (atInfinity real) vector) =
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 1)) * cusp.realize vector (atInfinity real) := by
  have shifted := goodLineFiniteVectorIntegral_endpointValue cusp spherical_cusp large cohomological halfWeight weight
    form form_nonzero eigenvalues relations (cuspSmoothAction cusp (atInfinity real) vector)
    (cuspSmoothAction_ne_zero cusp _ vector nonzero) (cuspSmoothAction_real_spherical cusp vector spherical real)
    (fun prime => by rw [cuspPrimeHeckeSum_real_commute, eigen, map_smul])
  simpa only [cuspSmoothAction_realize, one_mul] using shifted

theorem goodLineFiniteVectorIntegral_eigen_detects (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (form_nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector)
    (vanishes : ∀ real : BinaryRealGL,
      goodLineFiniteVectorIntegral degree cusp cohomologicalPoint (cuspSmoothAction cusp (atInfinity real) vector) = 0) :
    vector = 0 := by
  by_contra nonzero
  obtain ⟨real, value_nonzero⟩ := cuspRealization_exists_real_nonzero cusp vector spherical nonzero
  have identity := goodLineFiniteVectorIntegral_real_endpointValue cusp spherical_cusp large cohomological halfWeight weight
    form form_nonzero eigenvalues relations vector nonzero spherical eigen real
  rw [vanishes] at identity
  rw [← (cuspCriticalEulerProduct_hasProd cusp spherical_cusp cohomological halfWeight weight
    form form_nonzero eigenvalues relations).tprod_eq] at identity
  exact (mul_ne_zero (cuspCriticalEulerProduct_ne_zero cusp spherical_cusp cohomological halfWeight weight
    form form_nonzero eigenvalues relations) value_nonzero) identity.symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
