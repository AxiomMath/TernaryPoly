module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Localization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- A bounded extension of the prime Hecke sum obtained from representatives supported at the prime. -/
def cuspLocalizedHeckeOperator (cusp : CuspidalRepresentation) (prime : Nat.Primes) :
    cusp.H →L[ℂ] cusp.H :=
  ∑ index : Option (Fin prime.val),
    cuspUnitaryOperator cusp (atFinite (binaryHeckeLocalized prime index)⁻¹)

theorem cuspLocalizedHeckeOperator_apply (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.H) :
    cuspLocalizedHeckeOperator cusp prime vector =
      ∑ index : Option (Fin prime.val), cusp.π (atFinite (binaryHeckeLocalized prime index)⁻¹) vector := by
  simp only [cuspLocalizedHeckeOperator, sum_apply, cuspUnitaryOperator_apply]

theorem cuspLocalizedHeckeOperator_eq (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    cuspLocalizedHeckeOperator cusp prime vector.val = (cuspPrimeHeckeSum cusp prime vector).val := by
  rw [cuspLocalizedHeckeOperator_apply, cuspPrimeHeckeSum_eq_sum]
  exact Finset.sum_congr rfl (fun index _ => cuspHeckeLocalized_eq cusp prime vector spherical index)

theorem cuspLocalizedHeckeOperator_commute (cusp : CuspidalRepresentation) (first second : Nat.Primes) :
    Commute (cuspLocalizedHeckeOperator cusp first) (cuspLocalizedHeckeOperator cusp second) := by
  by_cases same : first = second
  · subst second
    exact Commute.refl _
  change _ = _
  ext vector
  simp only [mul_apply_eq_comp, cuspLocalizedHeckeOperator_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first_index _
  apply Finset.sum_congr rfl
  intro second_index _
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    ← atFinite_mul, ← atFinite_mul]
  rw [(binaryHeckeLocalized_commute first second same first_index second_index).inv_inv.eq]

theorem cuspPrimeHeckeSum_commute (cusp : CuspidalRepresentation) (first second : Nat.Primes)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    cuspPrimeHeckeSum cusp first (cuspPrimeHeckeSum cusp second vector) =
      cuspPrimeHeckeSum cusp second (cuspPrimeHeckeSum cusp first vector) := by
  apply Subtype.ext
  rw [← cuspLocalizedHeckeOperator_eq cusp first _ (cuspPrimeHeckeSum_spherical cusp second vector spherical),
    ← cuspLocalizedHeckeOperator_eq cusp second _ (cuspPrimeHeckeSum_spherical cusp first vector spherical),
    ← cuspLocalizedHeckeOperator_eq cusp second vector spherical,
    ← cuspLocalizedHeckeOperator_eq cusp first vector spherical]
  exact DFunLike.congr_fun (cuspLocalizedHeckeOperator_commute cusp first second).eq vector.val

end TernaryPeriodPolynomials.SphericalDetection.Helpers
