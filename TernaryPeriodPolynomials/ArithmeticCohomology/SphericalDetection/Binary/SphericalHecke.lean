module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Representatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The residue-line permutation gives the actual compact translate of each summand. -/
theorem cuspHeckeRepresentative_translate (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (compact : GeneralLinearGroup (Fin 2) IntegralAdeles) (index : Option (Fin prime.val)) :
    cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding compact))
        (cuspFiniteRationalSlash cusp (binaryHeckeRepresentative prime index) vector).val =
      (cuspFiniteRationalSlash cusp
        (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index)) vector).val := by
  obtain ⟨other, other_eq⟩ := binaryHeckePermutation_transition_integral prime compact index
  have rearrange : GeneralLinearGroup.map integralEmbedding compact *
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index))⁻¹ =
    (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index)))⁻¹ *
        GeneralLinearGroup.map integralEmbedding other := by
    rw [other_eq]
    group
  change cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding compact))
    (cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (binaryHeckeRepresentative prime index)⁻¹)) vector.val) = _
  rw [map_inv, ← Module.End.mul_apply, ← map_mul, ← atFinite_mul, rearrange,
    atFinite_mul, map_mul, Module.End.mul_apply, spherical other]
  change _ = cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index))⁻¹)) vector.val
  rw [map_inv]

theorem cuspPrimeHeckeSum_eq_sum (cusp : CuspidalRepresentation) (prime : Nat.Primes) (vector : cusp.smooth) :
    (cuspPrimeHeckeSum cusp prime vector).val =
      ∑ index : Option (Fin prime.val),
        (cuspFiniteRationalSlash cusp (binaryHeckeRepresentative prime index) vector).val := by
  simp only [Fintype.sum_option, binaryHeckeRepresentative, cuspPrimeHeckeSum,
    LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum]

theorem cuspPrimeHeckeSum_spherical (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    (cuspPrimeHeckeSum cusp prime vector).val ∈ cuspSphericalValues cusp := by
  intro compact
  rw [cuspPrimeHeckeSum_eq_sum, map_sum]
  calc
    _ = ∑ index : Option (Fin prime.val), (cuspFiniteRationalSlash cusp
        (binaryHeckeRepresentative prime (binaryHeckePermutation prime compact index)) vector).val := by
      apply Finset.sum_congr rfl
      intro index _
      exact cuspHeckeRepresentative_translate cusp prime vector spherical compact index
    _ = _ := Equiv.sum_comp (binaryHeckePermutation prime compact)
      (fun index => (cuspFiniteRationalSlash cusp (binaryHeckeRepresentative prime index) vector).val)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
