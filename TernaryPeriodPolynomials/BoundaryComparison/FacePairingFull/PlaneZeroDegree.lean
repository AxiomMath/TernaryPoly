module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Congruence
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.RadicalTrivialZero
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.NormalizedSourceArithmetic

@[expose] public section


/-!
# Degree zero: there is no inner plane class

At `n = 0` the coefficient system is `det⁻¹` on constants. On the level the determinant is `±1`, so
`E` and the dual system `E ∘ φ` (determinant `det`) agree on the level
(`rho0_dual_eq`). The dual transport of `Dual/Congruence` then turns the vanishing of the inner
line classes at `n = 0` (`eq_zero_of_innerBoundary_atZero`) into the vanishing of the inner plane
classes (`innerBoundary_plane_zero`, `innerClasses_plane_zero_eq_bot`). Consequently the line
pairing `ar:eq:facepair` is perfect in both arguments at `n = 0` as well
(`facePairing_right_nondegenerate_zero`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.FacePairing
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- At degree zero the coefficient action of `g` is multiplication by `(det g)⁻¹`. -/
theorem rho0_apply (g : RationalGL3) (f : HomogeneousPoly 0) :
    rationalCoefficientComponent 0 trivialCharacter g f =
      ((((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ)⁻¹ : ℚ) : ℂ) • f := by
  apply Subtype.ext
  change (1 : ℂ) • ((homogeneousAction 0 (-1) _ f : HomogeneousPoly 0) : Poly) = _
  rw [homogeneousAction_coe, action_apply]
  rw [one_smul, substitute_homogeneousPoly_zero _ f, Submodule.coe_smul]
  congr 1
  simp only [determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk]
  have hd : ((Matrix.GeneralLinearGroup.det
        ((Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ))
          ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) g)) : ℂˣ) : ℂ) =
      (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ) : ℂ) := by
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map,
      Units.coe_map]
    have h := RingHom.map_det (Complex.ofRealHom.comp (algebraMap ℚ ℝ))
      (g : Matrix (Fin 3) (Fin 3) ℚ)
    simp only [RingHom.mapMatrix_apply] at h
    exact h.symm
  rw [zpow_neg_one, hd, Rat.cast_inv]

/-- Elements of the level have determinant `±1`. -/
theorem sq_det_of_mem_rationalLevel {g : RationalGL3} (hg : g ∈ rationalLevel) :
    (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ)) ^ 2 = 1 := by
  have h := TernaryPeriodPolynomials.AnalyticClasses.abs_det_of_mem_rationalLevel hg
  have hd : (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) g).val.det =
      (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ) : ℝ) := by
    have h' := RingHom.map_det (algebraMap ℚ ℝ) (g : Matrix (Fin 3) (Fin 3) ℚ)
    simp only [RingHom.mapMatrix_apply] at h'
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact h'.symm
  rw [hd] at h
  have h2 : ((((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ) : ℝ)) ^ 2 = 1 := by
    rw [← sq_abs, h, one_pow]
  exact_mod_cast h2

/-- The involution inverts the determinant. -/
theorem det_dualInvolution (g : RationalGL3) :
    ((Matrix.GeneralLinearGroup.det (dualInvolution g) : ℚˣ) : ℚ) =
      (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ))⁻¹ := by
  have hT : Matrix.GeneralLinearGroup.det (inverseTranspose g) =
      (Matrix.GeneralLinearGroup.det g)⁻¹ := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    change ((g⁻¹).val.transpose).det = _
    rw [Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]
  rw [dualInvolution_apply, map_mul, map_mul, map_inv, hT]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

/-- **At degree zero `E ∘ φ` and `E` agree on the level.** -/
theorem rho0_dual_eq {g : RationalGL3} (hg : g ∈ rationalLevel) :
    dualRep (rationalCoefficientComponent 0 trivialCharacter) g =
      rationalCoefficientComponent 0 trivialCharacter g := by
  apply LinearMap.ext
  intro f
  change rationalCoefficientComponent 0 trivialCharacter (dualInvolution g) f = _
  rw [rho0_apply, rho0_apply, det_dualInvolution, inv_inv]
  have hsq := sq_det_of_mem_rationalLevel hg
  have hne : (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ)) ≠ 0 := Units.ne_zero _
  have : (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ)) =
      (((Matrix.GeneralLinearGroup.det g : ℚˣ) : ℚ))⁻¹ := by
    field_simp
    linarith
  rw [← this]

/-- **Degree zero: no inner plane class.** -/
theorem innerBoundary_plane_zero {a : StratumH2 0 trivialCharacter .plane}
    (ha : InnerBoundary 0 trivialCharacter .plane a) : a = 0 :=
  innerBoundaryRep_plane_zero (rationalCoefficientComponent 0 trivialCharacter)
    (fun _ hg => (rho0_dual_eq hg).symm) (fun _ hg => rho0_dual_eq hg)
    (fun _ hb => eq_zero_of_innerBoundary_atZero hb) ha

/-- The inner plane classes vanish at `n = 0`. -/
theorem innerClasses_plane_zero_eq_bot : innerClasses 0 .plane = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro a ha
  exact innerBoundary_plane_zero ha

/-- **The right kernel of the line face pairing is zero at `n = 0`.** -/
theorem facePairing_right_nondegenerate_zero (ξ : innerClasses 0 .plane)
    (_ : ∀ b : innerClasses 0 .line, facePairing 0 b ξ = 0) : ξ = 0 := by
  apply Subtype.ext
  exact innerBoundary_plane_zero ξ.property

end TernaryPeriodPolynomials.Argument.FacePairingFull
