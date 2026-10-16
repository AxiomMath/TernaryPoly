module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarSlash

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryHeckeDilate (modulus : ℕ) (positive : 0 < modulus) : BinaryRationalGL :=
  GeneralLinearGroup.mkOfDetNeZero !![(modulus : ℚ), 0; 0, 1] (by
    simpa [Matrix.det_fin_two] using (Nat.cast_ne_zero.mpr (ne_of_gt positive) : (modulus : ℚ) ≠ 0))

def binaryHeckeTranslate (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) : BinaryRationalGL :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (index.val : ℚ); 0, (modulus : ℚ)] (by
    simpa [Matrix.det_fin_two] using (Nat.cast_ne_zero.mpr (ne_of_gt positive) : (modulus : ℚ) ≠ 0))

theorem binaryHeckeDilate_real (modulus : ℕ) (positive : 0 < modulus) :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive)).val =
      !![(modulus : ℝ), 0; 0, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryHeckeDilate]

theorem binaryHeckeTranslate_real (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate modulus positive index)).val =
      !![1, (index.val : ℝ); 0, (modulus : ℝ)] := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryHeckeTranslate]

theorem binaryHeckeDilate_det (modulus : ℕ) (positive : 0 < modulus) :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive)).val.det = modulus := by
  rw [binaryHeckeDilate_real]
  simp [Matrix.det_fin_two]

theorem binaryHeckeTranslate_det (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate modulus positive index)).val.det = modulus := by
  rw [binaryHeckeTranslate_real]
  simp [Matrix.det_fin_two]

theorem binaryHeckeDilate_denom (modulus : ℕ) (positive : 0 < modulus) (point : ℂ) :
    UpperHalfPlane.denom (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive)) point = 1 := by
  unfold UpperHalfPlane.denom
  rw [binaryHeckeDilate_real]
  simp

theorem binaryHeckeTranslate_denom (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) (point : ℂ) :
    UpperHalfPlane.denom (GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (binaryHeckeTranslate modulus positive index)) point = modulus := by
  unfold UpperHalfPlane.denom
  rw [binaryHeckeTranslate_real]
  simp

theorem binaryHeckeDilate_smul (modulus : ℕ) (positive : 0 < modulus) (point : UpperHalfPlane) :
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive) • point : UpperHalfPlane) : ℂ) =
      modulus * (point : ℂ) := by
  have det_positive : 0 < (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive))).val := by
    change 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate modulus positive)).val.det
    rw [binaryHeckeDilate_det]
    exact_mod_cast positive
  rw [UpperHalfPlane.coe_smul_of_det_pos det_positive, binaryHeckeDilate_denom]
  unfold UpperHalfPlane.num
  rw [binaryHeckeDilate_real]
  simp

theorem binaryHeckeTranslate_smul (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) (point : UpperHalfPlane) :
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate modulus positive index) • point : UpperHalfPlane) : ℂ) =
      ((point : ℂ) + index.val) / modulus := by
  have det_positive : 0 < (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate modulus positive index))).val := by
    change 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate modulus positive index)).val.det
    rw [binaryHeckeTranslate_det]
    exact_mod_cast positive
  rw [UpperHalfPlane.coe_smul_of_det_pos det_positive, binaryHeckeTranslate_denom]
  unfold UpperHalfPlane.num
  rw [binaryHeckeTranslate_real]
  simp

theorem cuspFiniteRationalSlash_dilate (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (modulus : ℕ) (positive : 0 < modulus) (point : UpperHalfPlane) :
    cuspScalarWeightedLinear cusp halfWeight 1
        (cuspFiniteRationalSlash cusp (binaryHeckeDilate modulus positive) vector) point =
      (modulus : ℂ) ^ (-halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 (modulus * (point : ℂ)) := by
  rw [cuspFiniteRationalSlash_weighted,
    cuspScalarWeightedRealization_positive cusp central_positive halfWeight vector rotation _
      (by rw [binaryHeckeDilate_det]; exact_mod_cast positive),
    binaryHeckeDilate_det, binaryHeckeDilate_denom, binaryHeckeDilate_smul]
  simp

theorem cuspFiniteRationalSlash_translate (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (modulus : ℕ) (positive : 0 < modulus) (index : Fin modulus) (point : UpperHalfPlane) :
    cuspScalarWeightedLinear cusp halfWeight 1
        (cuspFiniteRationalSlash cusp (binaryHeckeTranslate modulus positive index) vector) point =
      (modulus : ℂ) ^ halfWeight *
        cuspScalarWeightedRealization cusp halfWeight vector 1 (((point : ℂ) + index.val) / modulus) := by
  rw [cuspFiniteRationalSlash_weighted,
    cuspScalarWeightedRealization_positive cusp central_positive halfWeight vector rotation _
      (by rw [binaryHeckeTranslate_det]; exact_mod_cast positive),
    binaryHeckeTranslate_det, binaryHeckeTranslate_denom, binaryHeckeTranslate_smul]
  push_cast
  rw [← zpow_add₀ (Nat.cast_ne_zero.mpr (ne_of_gt positive))]
  congr 2
  ring

/-- The sum over the usual prime Hecke representatives, defined as actual finite translations. -/
def cuspPrimeHeckeSum (cusp : CuspidalRepresentation) (prime : Nat.Primes) : Module.End ℂ cusp.smooth :=
  cuspFiniteRationalSlash cusp (binaryHeckeDilate prime.val prime.property.pos) +
    ∑ index : Fin prime.val,
      cuspFiniteRationalSlash cusp (binaryHeckeTranslate prime.val prime.property.pos index)

theorem cuspPrimeHeckeSum_scalar (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (prime : Nat.Primes) (point : UpperHalfPlane) :
    cuspScalarWeightedLinear cusp halfWeight 1 (cuspPrimeHeckeSum cusp prime vector) point =
      (prime.val : ℂ) ^ (-halfWeight) *
          cuspScalarWeightedRealization cusp halfWeight vector 1 (prime.val * (point : ℂ)) +
        (prime.val : ℂ) ^ halfWeight * ∑ index : Fin prime.val,
          cuspScalarWeightedRealization cusp halfWeight vector 1 (((point : ℂ) + index.val) / prime.val) := by
  simp only [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum,
    Pi.add_apply, Finset.sum_apply]
  rw [cuspFiniteRationalSlash_dilate cusp central_positive halfWeight vector rotation]
  simp only [cuspFiniteRationalSlash_translate cusp central_positive halfWeight vector rotation,
    Finset.mul_sum]

theorem cuspPrimeHeckeSum_eigen_relation (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (prime : Nat.Primes) (eigenvalue : ℂ)
    (eigenvector : cuspPrimeHeckeSum cusp prime vector = eigenvalue • vector)
    (point : UpperHalfPlane) :
    ((prime.val : ℂ) ^ (-halfWeight - 1) * eigenvalue) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 point =
      (prime.val : ℂ) ^ (-2 * halfWeight - 1) *
          cuspScalarWeightedRealization cusp halfWeight vector 1 (prime.val * (point : ℂ)) +
        (prime.val : ℂ)⁻¹ * ∑ index : Fin prime.val,
          cuspScalarWeightedRealization cusp halfWeight vector 1 (((point : ℂ) + index.val) / prime.val) := by
  have identity := cuspPrimeHeckeSum_scalar cusp central_positive halfWeight vector rotation prime point
  rw [eigenvector, map_smul, Pi.smul_apply, smul_eq_mul] at identity
  have scaled := congrArg (fun value : ℂ => (prime.val : ℂ) ^ (-halfWeight - 1) * value) identity
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero),
    ← zpow_add₀ (Nat.cast_ne_zero.mpr prime.property.ne_zero)] at scaled
  have first_exponent : -halfWeight - 1 + -halfWeight = -2 * halfWeight - 1 := by ring
  have second_exponent : -halfWeight - 1 + halfWeight = -1 := by ring
  rw [first_exponent, second_exponent, zpow_neg_one] at scaled
  exact scaled

theorem cuspFiniteRationalSlash_norm (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (vector : cusp.smooth) : ‖cuspFiniteRationalSlash cusp rational vector‖ = ‖vector‖ :=
  cusp.unitary _ _

theorem cuspPrimeHeckeSum_norm_le (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) :
    ‖cuspPrimeHeckeSum cusp prime vector‖ ≤ (prime.val + 1 : ℝ) * ‖vector‖ := by
  rw [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply]
  calc
    _ ≤ ‖cuspFiniteRationalSlash cusp (binaryHeckeDilate prime.val prime.property.pos) vector‖ +
        ∑ index : Fin prime.val,
          ‖cuspFiniteRationalSlash cusp (binaryHeckeTranslate prime.val prime.property.pos index) vector‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = (prime.val + 1 : ℝ) * ‖vector‖ := by
      simp only [cuspFiniteRationalSlash_norm, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

theorem cuspPrimeHeckeSum_eigenvalue_norm_le (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (eigenvalue : ℂ)
    (eigenvector : cuspPrimeHeckeSum cusp prime vector = eigenvalue • vector) :
    ‖eigenvalue‖ ≤ (prime.val + 1 : ℝ) := by
  have bound := cuspPrimeHeckeSum_norm_le cusp prime vector
  rw [eigenvector, norm_smul] at bound
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr nonzero)).mp bound

theorem cuspFiniteRationalSlash_rotation (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (weight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspFiniteRationalSlash cusp rational vector).val =
      (angle : ℂ) ^ weight • (cuspFiniteRationalSlash cusp rational vector).val := by
  change cusp.π (atInfinity (binaryRotations angle))
    (cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹)) vector.val) = _
  rw [← Module.End.mul_apply, ← map_mul,
    (atInfinity_commute_atFinite (binaryRotations angle)
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹)).eq,
    map_mul, Module.End.mul_apply, rotation, map_smul]
  rfl

theorem cuspPrimeHeckeSum_rotation (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (weight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspPrimeHeckeSum cusp prime vector).val =
      (angle : ℂ) ^ weight • (cuspPrimeHeckeSum cusp prime vector).val := by
  simp only [cuspPrimeHeckeSum, LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add,
    Submodule.coe_sum, map_add, map_sum, smul_add, Finset.smul_sum]
  rw [cuspFiniteRationalSlash_rotation cusp _ weight vector rotation]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  exact cuspFiniteRationalSlash_rotation cusp _ weight vector rotation angle

theorem cuspFiniteRationalSlash_weightedOrbit (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (halfWeight : ℤ) (vector : cusp.smooth) (point : ℂ) :
    cuspWeightedAffineOrbit cusp halfWeight (cuspFiniteRationalSlash cusp rational vector).val point =
      cuspUnitaryOperator cusp (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹))
        (cuspWeightedAffineOrbit cusp halfWeight vector.val point) := by
  unfold cuspWeightedAffineOrbit cuspAffineOrbitVector
  change _ = ((cuspUnitaryOperator cusp
    (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹))).restrictScalars ℝ)
      (point.im ^ halfWeight • cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) vector.val)
  rw [map_smul]
  congr 1
  change cusp.π (atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))
    (cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹)) vector.val) = _
  rw [← Module.End.mul_apply, ← map_mul,
    (atInfinity_commute_atFinite (invertibleMatrix (binaryUpperSectionMatrix point))
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹)).eq,
    map_mul, Module.End.mul_apply]
  rfl

theorem cuspFiniteRationalSlash_holomorphic (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight
      (cuspFiniteRationalSlash cusp rational vector).val) UpperHalfPlane.upperHalfPlaneSet := by
  have regular := (cuspUnitaryOperator cusp
    (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹))).differentiable.comp_differentiableOn holomorphic
  exact regular.congr (fun point _ => cuspFiniteRationalSlash_weightedOrbit cusp rational halfWeight vector point)

theorem cuspPrimeHeckeSum_weightedOrbit (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (halfWeight : ℤ) (vector : cusp.smooth) (point : ℂ) :
    cuspWeightedAffineOrbit cusp halfWeight (cuspPrimeHeckeSum cusp prime vector).val point =
      cuspWeightedAffineOrbit cusp halfWeight
          (cuspFiniteRationalSlash cusp (binaryHeckeDilate prime.val prime.property.pos) vector).val point +
        ∑ index : Fin prime.val, cuspWeightedAffineOrbit cusp halfWeight
          (cuspFiniteRationalSlash cusp (binaryHeckeTranslate prime.val prime.property.pos index) vector).val point := by
  simp only [cuspWeightedAffineOrbit, cuspAffineOrbitVector, cuspPrimeHeckeSum,
    LinearMap.add_apply, LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum,
    map_add, map_sum, smul_add, Finset.smul_sum]

theorem cuspPrimeHeckeSum_holomorphic (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight (cuspPrimeHeckeSum cusp prime vector).val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have dilate := cuspFiniteRationalSlash_holomorphic cusp
    (binaryHeckeDilate prime.val prime.property.pos) halfWeight vector holomorphic
  have translations : DifferentiableOn ℂ (fun point => ∑ index : Fin prime.val,
      cuspWeightedAffineOrbit cusp halfWeight
        (cuspFiniteRationalSlash cusp (binaryHeckeTranslate prime.val prime.property.pos index) vector).val point)
      UpperHalfPlane.upperHalfPlaneSet := by
    simpa only [Finset.sum_fn] using DifferentiableOn.sum (u := Finset.univ)
      (fun (index : Fin prime.val) _ => cuspFiniteRationalSlash_holomorphic cusp
        (binaryHeckeTranslate prime.val prime.property.pos index) halfWeight vector holomorphic)
  exact (dilate.add translations).congr
    (fun point _ => cuspPrimeHeckeSum_weightedOrbit cusp prime halfWeight vector point)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
