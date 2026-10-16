module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.Regularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarModularity
public import Mathlib.Analysis.Complex.Convex

@[expose] public section


/-!
# The Eichler period is a cocycle in its endpoint

Let `F h` be a family of holomorphic functions on the upper half plane of weight `n + 3` under
right translation by determinant-one real matrices,
`F (h · A) z = (c z + d)^{-(n+3)} F h (A · z)`. The straight-line Eichler period
`Per(z)(h) = ∫_i^z F h w (X₀ - w X₁)^{n+1} dw` then satisfies, for `det A = 1` and every `B`,
`Per(A B · i)(h) = Per(A · i)(h) + A · Per(B · i)(h A)`, with `A` acting by the binary coefficient
action. The difference of the two sides, as a function of the point `B · i`, has zero complex
derivative on the half plane (by the weight of `F`, the identity
`A · (X₀ - z X₁)^{n+1} = (c z + d)^{n+1} (X₀ - (A · z) X₁)^{n+1}` and `(A · z)' = (c z + d)^{-2}`)
and vanishes at `i`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem det_map_algebraMap_complex (A : BinaryRealGL) :
    ((A.val).map (algebraMap ℝ ℂ)).det = (A.val.det : ℂ) :=
  (RingHom.map_det (algebraMap ℝ ℂ) A.val).symm

theorem denom_eq_entries (A : BinaryRealGL) (z : ℂ) :
    UpperHalfPlane.denom A z = (A.val 1 0 : ℂ) * z + (A.val 1 1 : ℂ) := by
  simp [UpperHalfPlane.denom]

theorem num_eq_entries (A : BinaryRealGL) (z : ℂ) :
    UpperHalfPlane.num A z = (A.val 0 0 : ℂ) * z + (A.val 0 1 : ℂ) := by
  simp [UpperHalfPlane.num]

/-- The Möbius transformation `z ↦ (a z + b) / (c z + d)` of a real binary matrix. -/
def realMobius (A : BinaryRealGL) (z : ℂ) : ℂ := UpperHalfPlane.num A z / UpperHalfPlane.denom A z

theorem realMobius_coe (A : BinaryRealGL) (hA : A.val.det = 1) (z : UpperHalfPlane) :
    realMobius A z = ((A • z : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos
    (by rw [GeneralLinearGroup.val_det_apply, hA]; exact one_pos)]
  rfl

theorem hasDerivAt_realMobius (A : BinaryRealGL) (hA : A.val.det = 1) {z : ℂ}
    (hz : UpperHalfPlane.denom A z ≠ 0) :
    HasDerivAt (realMobius A) ((UpperHalfPlane.denom A z ^ 2)⁻¹) z := by
  have hn : HasDerivAt (fun w => UpperHalfPlane.num A w) (A.val 0 0 : ℂ) z := by
    simp_rw [num_eq_entries]
    simpa using ((hasDerivAt_id z).const_mul (A.val 0 0 : ℂ)).add_const (A.val 0 1 : ℂ)
  have hd : HasDerivAt (fun w => UpperHalfPlane.denom A w) (A.val 1 0 : ℂ) z := by
    simp_rw [denom_eq_entries]
    simpa using ((hasDerivAt_id z).const_mul (A.val 1 0 : ℂ)).add_const (A.val 1 1 : ℂ)
  have hdet : (A.val 0 0 : ℂ) * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    have := hA
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  refine (hn.div hd hz).congr_deriv ?_
  have numerator : (A.val 0 0 : ℂ) * UpperHalfPlane.denom A z -
      UpperHalfPlane.num A z * A.val 1 0 = 1 := by
    rw [num_eq_entries, denom_eq_entries]
    linear_combination hdet
  rw [numerator, one_div]

/-- The derivative of a functional of the Eichler period in its endpoint. -/
theorem hasDerivAt_functional_eichlerPeriod (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im}) {z : ℂ} (hz : 0 < z.im)
    (h : BinaryAdelicGL) (L : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    HasDerivAt (fun w => L (eichlerPeriod n F w h)) (F h z * L (binaryPointPower (n + 1) z)) z := by
  have expand : ∀ v, L v = ∑ i, (binaryWeightBasis (n + 1)).coord i v *
      L (binaryWeightBasis (n + 1) i) := by
    intro v
    conv_lhs => rw [← (binaryWeightBasis (n + 1)).sum_repr v]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  have e : (fun w => L (eichlerPeriod n F w h)) = fun w =>
      ∑ i, (binaryWeightBasis (n + 1)).coord i (eichlerPeriod n F w h) *
        L (binaryWeightBasis (n + 1) i) := funext fun w => expand _
  rw [e, expand (binaryPointPower (n + 1) z)]
  refine (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_coord_eichlerPeriod F holomorphic hz h i).mul_const _).congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem inv_map_complex_of_det_one (A : BinaryRealGL) (hA : A.val.det = 1) :
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) A)⁻¹.val =
      !![(A.val 1 1 : ℂ), -(A.val 0 1 : ℂ); -(A.val 1 0 : ℂ), (A.val 0 0 : ℂ)] := by
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, GeneralLinearGroup.val_map_apply,
    det_map_algebraMap_complex, hA, Complex.ofReal_one, Ring.inverse_one, one_smul,
    Matrix.adjugate_fin_two]
  ext r c
  fin_cases r <;> fin_cases c <;> simp

/-- The coefficient action of a determinant-one matrix on `(X₀ - z X₁)^{n+1}`. -/
theorem binaryCoefficient_binaryPointPower (A : BinaryRealGL) (hA : A.val.det = 1) (z : ℂ)
    (hz : UpperHalfPlane.denom A z ≠ 0) :
    binaryCoefficient n A (binaryPointPower (n + 1) z) =
      UpperHalfPlane.denom A z ^ (n + 1) • binaryPointPower (n + 1) (realMobius A z) := by
  have det : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) A)).val = 1 := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply,
      det_map_algebraMap_complex, hA, Complex.ofReal_one]
  apply Subtype.ext
  rw [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply]
  simp only [Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, det, _root_.one_zpow,
    one_smul]
  rw [inv_map_complex_of_det_one A hA,
    binaryPointPower_mobius_substitution _ _ _ _ _ _ (by rwa [denom_eq_entries] at hz), realMobius,
    denom_eq_entries, num_eq_entries]

/-- **The Eichler period is a cocycle in its endpoint.** For a family `F h` of holomorphic
functions of weight `n + 3` under right translation by determinant-one matrices,
`Per(A B · i)(h) = Per(A · i)(h) + A · Per(B · i)(h A)` for `det A = 1`. -/
theorem eichlerPeriod_basePoint_mul (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (modular : ∀ A : BinaryRealGL, A.val.det = 1 → ∀ h (z : UpperHalfPlane),
      F (h * atInfinity A) z = UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) * F h (A • z : _))
    (A : BinaryRealGL) (hA : A.val.det = 1) (B : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerPeriod n F (basePoint (A * B)) h = eichlerPeriod n F (basePoint A) h +
      binaryCoefficient n A (eichlerPeriod n F (basePoint B) (h * atInfinity A)) := by
  apply (binaryWeightBasis (n + 1)).ext_elem
  intro j
  set L := (binaryWeightBasis (n + 1)).coord j
  set Φ : ℂ → ℂ := fun w => L (eichlerPeriod n F (realMobius A w) h) -
    (L ∘ₗ binaryCoefficient n A) (eichlerPeriod n F w (h * atInfinity A))
  have derivative : ∀ z : ℂ, 0 < z.im → HasDerivAt Φ 0 z := by
    intro z hz
    set τ : UpperHalfPlane := ⟨z, hz⟩
    have nonzero : UpperHalfPlane.denom A z ≠ 0 := UpperHalfPlane.denom_ne_zero A τ
    have image : realMobius A z = ((A • τ : UpperHalfPlane) : ℂ) := realMobius_coe A hA τ
    have image_pos : 0 < (realMobius A z).im := by rw [image]; exact (A • τ).im_pos
    have first := (hasDerivAt_functional_eichlerPeriod F holomorphic image_pos h L).comp z
      (hasDerivAt_realMobius A hA nonzero)
    have second := hasDerivAt_functional_eichlerPeriod F holomorphic hz (h * atInfinity A)
      (L ∘ₗ binaryCoefficient n A)
    refine (first.sub second).congr_deriv ?_
    have law : F (h * atInfinity A) z =
        UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) * F h (realMobius A z) := by
      rw [image]; exact modular A hA h τ
    rw [LinearMap.comp_apply, binaryCoefficient_binaryPointPower A hA z nonzero, map_smul,
      smul_eq_mul, law]
    have power : UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) =
        ((UpperHalfPlane.denom A z ^ 2)⁻¹) * (UpperHalfPlane.denom A z ^ (n + 1))⁻¹ := by
      rw [← mul_inv, ← pow_add, ← zpow_natCast, ← _root_.zpow_neg]
      congr 1
      push_cast
      ring
    rw [power]
    field_simp
    ring
  have constant := eichlerUpperSet_isOpen.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (derivative z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (derivative z hz).deriv) (x := basePoint B) (y := Complex.I)
    (B • UpperHalfPlane.I).im_pos (by simp)
  have at_B : realMobius A (basePoint B) = basePoint (A * B) := by
    rw [basePoint, realMobius_coe A hA, basePoint, mul_smul]
  have at_I : realMobius A Complex.I = basePoint A := by
    rw [basePoint, ← realMobius_coe A hA, UpperHalfPlane.coe_I]
  have period_I : eichlerPeriod n F Complex.I (h * atInfinity A) = 0 := by
    simp only [eichlerPeriod, eichlerIntegrand, sub_self, zero_mul,
      intervalIntegral.integral_zero, zero_smul, Finset.sum_const_zero]
  simp only [Φ, at_B, at_I, period_I, map_zero, sub_zero] at constant
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply, map_add]
  linear_combination constant

end TernaryPeriodPolynomials.AnalyticClasses
