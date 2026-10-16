module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialLadders

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryWeightExponent (degree : ℕ) (position : Fin (degree + 1)) : BinaryHomogeneousExponent degree :=
  ⟨Finsupp.single 0 position.val + Finsupp.single 1 (degree - position.val), by
    simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    omega⟩

theorem binaryWeightExponent_first (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryWeightExponent degree position).val 0 = position.val := by simp [binaryWeightExponent]

theorem binaryWeightExponent_second (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryWeightExponent degree position).val 1 = degree - position.val := by simp [binaryWeightExponent]

def binaryWeightIndex (degree : ℕ) : BinaryHomogeneousExponent degree ≃ Fin (degree + 1) where
  toFun exponent := ⟨exponent.val 0, by have total := binaryHomogeneousExponent_sum exponent; omega⟩
  invFun := binaryWeightExponent degree
  left_inv exponent := by
    apply Subtype.ext
    ext position
    have total := binaryHomogeneousExponent_sum exponent
    fin_cases position
    · exact binaryWeightExponent_first degree _
    · change (binaryWeightExponent degree ⟨exponent.val 0, _⟩).val 1 = exponent.val 1
      rw [binaryWeightExponent_second]
      change degree - exponent.val 0 = exponent.val 1
      omega
  right_inv position := by
    apply Fin.ext
    exact binaryWeightExponent_first degree position

def binaryWeightBasis (degree : ℕ) : Module.Basis (Fin (degree + 1)) ℂ (Binary.HomogeneousPoly degree) :=
  (binaryRotationBasis degree).reindex (binaryWeightIndex degree)

theorem binaryWeightBasis_coe (degree : ℕ) (position : Fin (degree + 1)) :
    (binaryWeightBasis degree position).val =
      binaryPositiveCoordinate ^ position.val * binaryNegativeCoordinate ^ (degree - position.val) := by
  rw [binaryWeightBasis, Module.Basis.reindex_apply, binaryRotationBasis_coordinates]
  change binaryPositiveCoordinate ^ (binaryWeightExponent degree position).val 0 *
    binaryNegativeCoordinate ^ (binaryWeightExponent degree position).val 1 = _
  rw [binaryWeightExponent_first, binaryWeightExponent_second]

theorem binaryWeightBasis_rotation (degree : ℕ) (position : Fin (degree + 1)) :
    binaryInfinitesimalSubstitution binaryInfinitesimalRotation (binaryWeightBasis degree position).val =
      (Complex.I * ((degree : ℂ) - 2 * (position.val : ℂ))) • (binaryWeightBasis degree position).val := by
  have bound : position.val ≤ degree := by omega
  rw [binaryWeightBasis_coe, ← binaryInfinitesimalDerivation_apply, binaryInfinitesimalRotation_monomial,
    Nat.cast_sub bound]
  congr 1
  ring

theorem binaryWeightBasis_lowering_interior (degree : ℕ) (position : Fin degree) :
    binaryPolynomialLowering (binaryWeightBasis degree position.castSucc).val =
      (Complex.I * ((degree - position.val : ℕ) : ℂ)) • (binaryWeightBasis degree position.succ).val := by
  rw [binaryWeightBasis_coe, binaryPolynomialLowering_monomial, binaryWeightBasis_coe]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.sub_sub]

theorem binaryWeightBasis_raising_interior (degree : ℕ) (position : Fin degree) :
    binaryPolynomialRaising (binaryWeightBasis degree position.succ).val =
      (-Complex.I * ((position.val + 1 : ℕ) : ℂ)) • (binaryWeightBasis degree position.castSucc).val := by
  rw [binaryWeightBasis_coe, binaryPolynomialRaising_monomial, binaryWeightBasis_coe]
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel]
  have exponent : degree - (position.val + 1) + 1 = degree - position.val := by omega
  rw [exponent]

theorem binaryWeightBasis_lowering_last (degree : ℕ) :
    binaryPolynomialLowering (binaryWeightBasis degree (Fin.last degree)).val = 0 := by
  rw [binaryWeightBasis_coe, binaryPolynomialLowering_monomial]
  simp

theorem binaryWeightBasis_raising_zero (degree : ℕ) :
    binaryPolynomialRaising (binaryWeightBasis degree 0).val = 0 := by
  rw [binaryWeightBasis_coe, binaryPolynomialRaising_monomial]
  simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
