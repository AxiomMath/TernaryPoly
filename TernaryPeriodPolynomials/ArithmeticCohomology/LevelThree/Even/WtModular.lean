module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtFactor
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Even.WtScalar
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Dictionary

@[expose] public section


/-!
# Weight-generic modularity of the scalar realization

Formalized by Claude Sonnet 5.5 (AxiomCode).

Twins, for an integer rotation weight `wt` (odd or even), of the modular transformation of the
scalar realization and of the level-three slash identities.  The factor `point.im ^ halfWeight`
is replaced by `wtFactor wt point.im`, `denom ^ (2 * halfWeight)` by `denom ^ wt`, and the weight
`-2 * halfWeight` of the resulting form by `-wt`.

* `binary_weighted_phase_identityWt` relates the weight factors at `matrix • point` and `point`
  through the denominator and the Iwasawa phase;
* `cuspScalarWeightedRealization_det_oneWt` and `cuspScalarWeightedRealization_modularWt` are the
  transformation under real, respectively rational, matrices of determinant one;
* `cuspScalarWeightedRealization_modular_levelThreeWt`, `cuspFiniteRationalSlash_scalar_det_oneWt`
  and `levelThree_slash_eqWt` are the level-three statements, with the classical-vector hypothesis
  replaced by its two components `hlev` and `hrot`.

Skipped (not needed by the level-three dictionary): the determinant-normalised variants
`cuspScalarWeightedRealization_positive` and `cuspFiniteRationalSlash_eq_slash`, and every level-one
statement.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.MultiplicityOne
  (levelThreeValues levelThree_fixed_gamma)

noncomputable section

namespace TernaryPeriodPolynomials.EvenLevelThree

/-- The weight factor at `matrix • point` is the weight factor at `point`, divided by the
denominator power `wt` and multiplied by the Iwasawa phase power `wt`. -/
theorem binary_weighted_phase_identityWt (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) (wt : ℤ) :
    ((wtFactor wt (matrix • point : UpperHalfPlane).im : ℝ) : ℂ) =
      UpperHalfPlane.denom matrix point ^ (-wt) *
        ((wtFactor wt point.im : ℝ) : ℂ) * binaryPhaseValue matrix point ^ wt := by
  have denominator_nonzero := UpperHalfPlane.denom_ne_zero matrix point
  have norm_positive : 0 < ‖UpperHalfPlane.denom matrix point‖ :=
    norm_pos_iff.mpr denominator_nonzero
  have key : wtFactor wt (matrix • point : UpperHalfPlane).im =
      wtFactor wt point.im / ‖UpperHalfPlane.denom matrix point‖ ^ wt := by
    rw [UpperHalfPlane.im_smul_eq_div_normSq, determinant, abs_one, one_mul,
      Complex.normSq_eq_norm_sq, wtFactor_div wt point.im_pos (pow_pos norm_positive 2),
      wtFactor_eq_sqrt_zpow wt (pow_pos norm_positive 2), Real.sqrt_sq norm_positive.le]
  have rearrange : ∀ a D N : ℂ, D ≠ 0 → a / N = D⁻¹ * a * (D / N) := by
    intro a D N hD
    rw [mul_comm D⁻¹ a, mul_assoc, div_eq_mul_inv D N, ← mul_assoc D⁻¹ D, inv_mul_cancel₀ hD,
      one_mul, div_eq_mul_inv]
  rw [key, binaryPhaseValue, div_zpow, Complex.ofReal_div, Complex.ofReal_zpow, _root_.zpow_neg]
  exact rearrange _ _ _ (zpow_ne_zero wt denominator_nonzero)

/-- The modular transformation of the scalar realization under a rational matrix of determinant
one fixing the vector. -/
theorem cuspScalarWeightedRealization_modularWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ wt • vector.val) (rational : BinaryRationalGL)
    (determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val = 1)
    (fixed : cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational))
      vector.val = vector.val)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealizationWt cusp wt vector 1
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) point ^ (-wt) *
        cuspScalarWeightedRealizationWt cusp wt vector 1 point := by
  have identity := cuspScalarAffineRealization_modular_phase cusp vector wt rotation rational
    determinant fixed point
  simp only [cuspScalarWeightedRealizationWt, Complex.real_smul]
  change (((wtFactor wt
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational • point : UpperHalfPlane).im : ℝ) : ℂ)) *
      _ = _
  rw [binary_weighted_phase_identityWt _ determinant point wt, mul_assoc, mul_assoc, identity]
  rfl

/-- The scalar realization at a base point of determinant one is the realization at `1` of the
translate, times the denominator power `wt`. -/
theorem cuspScalarWeightedRealization_det_oneWt (cusp : CuspidalRepresentation) (wt : ℤ)
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ wt • vector.val)
    (matrix : BinaryRealGL) (determinant : (GeneralLinearGroup.det matrix).val = 1)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealizationWt cusp wt vector (atInfinity matrix) point =
      UpperHalfPlane.denom matrix point ^ wt *
        cuspScalarWeightedRealizationWt cusp wt vector 1
          ((matrix • point : UpperHalfPlane) : ℂ) := by
  have phase := cuspScalarAffineRealization_rotation cusp vector wt rotation 1
    matrix determinant point
  rw [one_mul] at phase
  have scalar_identity :
      cuspScalarAffineRealization cusp vector (atInfinity matrix) point =
        binaryPhaseValue matrix point ^ wt *
          cuspScalarAffineRealization cusp vector 1 ((matrix • point : UpperHalfPlane) : ℂ) := by
    rw [cuspScalarAffineRealization, binaryUpperSectionMatrix_coe, invertibleMatrix_coe,
      ← atInfinity_mul]
    exact phase
  simp only [cuspScalarWeightedRealizationWt, Complex.real_smul]
  rw [scalar_identity]
  change _ = UpperHalfPlane.denom matrix point ^ wt *
    ((((wtFactor wt (matrix • point : UpperHalfPlane).im : ℝ) : ℂ)) * _)
  rw [binary_weighted_phase_identityWt matrix determinant point wt]
  have cancel : UpperHalfPlane.denom matrix point ^ wt *
      UpperHalfPlane.denom matrix point ^ (-wt) = 1 := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero matrix point), add_neg_cancel, zpow_zero]
  calc
    _ = (UpperHalfPlane.denom matrix point ^ wt *
        UpperHalfPlane.denom matrix point ^ (-wt)) *
        (((wtFactor wt point.im : ℝ) : ℂ) *
          (binaryPhaseValue matrix point ^ wt *
            cuspScalarAffineRealization cusp vector 1
              ((matrix • point : UpperHalfPlane) : ℂ))) := by
      rw [cancel, one_mul]
      rfl
    _ = _ := by ring

/-- The modular transformation of the scalar function under `Γ₁(3)`, for an integer rotation
weight `wt`. -/
theorem cuspScalarWeightedRealization_modular_levelThreeWt (σ : CuspidalRepresentation)
    (wt : ℤ) (v : σ.smooth) (hlev : v.val ∈ levelThreeValues σ)
    (hrot : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ wt • v.val)
    (γ : SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealizationWt σ wt v 1
        ((SpecialLinearGroup.mapGL ℝ γ • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ γ) point ^ (-wt) *
        cuspScalarWeightedRealizationWt σ wt v 1 point := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ γ))).val = 1 := by
    rw [binaryIntegral_specialLinear_real]
    exact (SpecialLinearGroup.map (algebraMap ℤ ℝ) γ).property
  simpa only [binaryIntegral_specialLinear_real] using
    cuspScalarWeightedRealization_modularWt σ wt v hrot (SpecialLinearGroup.mapGL ℚ γ)
      determinant (levelThree_fixed_gamma σ hlev hγ) point

/-- The slash of the scalar function by a rational matrix of determinant one is the scalar function
of the finite translate; no level and no central character are needed. -/
theorem cuspFiniteRationalSlash_scalar_det_oneWt (σ : CuspidalRepresentation) (wt : ℤ)
    (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ wt • v.val)
    (rational : BinaryRationalGL)
    (determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val = 1) :
    cuspScalarWeightedLinearWt σ wt 1 (cuspFiniteRationalSlash σ rational v) =
      SlashAction.map (-wt) (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)
        (cuspScalarWeightedLinearWt σ wt 1 v) := by
  funext point
  have det_positive : 0 < (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val := by
    rw [determinant]
    exact zero_lt_one
  rw [cuspFiniteRationalSlash_weightedWt,
    cuspScalarWeightedRealization_det_oneWt σ wt v rotation _ determinant point,
    ModularForm.slash_apply]
  have sigma : UpperHalfPlane.σ (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [ite_eq_left det_positive]
  rw [sigma, ContinuousAlgEquiv.refl_apply, determinant, abs_one, neg_neg]
  change _ = cuspScalarWeightedRealizationWt σ wt v 1 _ * _ * _
  simp only [Complex.ofReal_one, _root_.one_zpow, mul_one]
  exact mul_comm _ _

/-- The slash by `γ ∈ SL₂(ℤ)` of the scalar function of `v` is the scalar function of the
translate `cuspFiniteRationalSlash σ γ v`. -/
theorem levelThree_slash_eqWt (σ : CuspidalRepresentation) (wt : ℤ) (v : σ.smooth)
    (rotation : ∀ angle : Circle, σ.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ wt • v.val)
    (γ : SpecialLinearGroup (Fin 2) ℤ) :
    cuspScalarWeightedLinearWt σ wt 1
        (cuspFiniteRationalSlash σ (SpecialLinearGroup.mapGL ℚ γ) v) =
      SlashAction.map (-wt) (SpecialLinearGroup.mapGL ℝ γ)
        (cuspScalarWeightedLinearWt σ wt 1 v) := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ γ))).val = 1 := by
    rw [binaryIntegral_specialLinear_real]
    exact (SpecialLinearGroup.map (algebraMap ℤ ℝ) γ).property
  have key := cuspFiniteRationalSlash_scalar_det_oneWt σ wt v rotation
    (SpecialLinearGroup.mapGL ℚ γ) determinant
  rw [binaryIntegral_specialLinear_real] at key
  exact key

end TernaryPeriodPolynomials.EvenLevelThree
