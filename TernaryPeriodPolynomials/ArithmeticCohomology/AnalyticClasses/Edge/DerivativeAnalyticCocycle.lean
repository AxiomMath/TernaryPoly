module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeInterface
public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeCocycle
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.Action

@[expose] public section


/-!
# The Eichler normal form of a scalar form is a pointwise binary cocycle

For a scalar form `F` with `EichlerData n F`, the pointwise Eichler normal form
`N(A) = ½ (Per(A · i) + J · Per(-conj(A · i)))` satisfies `N(A C) = N(A) + A · N(C)` for all
`A, C ∈ GL₂(ℝ)`: for determinant one this is the cocycle law of the two halves, `N(J C) = J · N(C)`,
and positive scalars act trivially on both sides. The weight-basis coordinates of the pointwise
normal form are Lipschitz on compact convex subsets of the upper half plane, uniformly in the
adelic argument, and vanish at `i`. Hence `N` is a `BinaryPointCocycle`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ} {F : BinaryAdelicGL → ℂ → ℂ}

theorem eichlerNormal_eq_hol_add_anti (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL) :
    eichlerNormal n F A = eichlerHolomorphic n F A + eichlerAntiholomorphic n F A :=
  funext fun h => eichlerNormal_eq_add F A h

/-- Left multiplication by `J` acts on the normal form by the action of `J`. -/
theorem eichlerNormal_J_mul (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerNormal n F (UpperHalfPlane.J * C) =
      binaryAmbientRepresentation n UpperHalfPlane.J (eichlerNormal n F C) := by
  rw [eichlerNormal_eq_hol_add_anti, eichlerNormal_eq_hol_add_anti, eichlerAntiholomorphic_eq,
    eichlerAntiholomorphic_eq, ← mul_assoc, upperJ_mul_self, one_mul, map_add,
    binaryAmbientRepresentation_J_J]
  exact add_comm _ _

theorem basePoint_scalar_mul (c : ℝˣ) (X : BinaryRealGL) :
    basePoint (GeneralLinearGroup.scalar (Fin 2) c * X) = basePoint X := by
  rw [basePoint, mul_smul, UpperHalfPlane.glScalar_smul, basePoint]

theorem eichlerNormal_scalar_mul (F : BinaryAdelicGL → ℂ → ℂ) (c : ℝˣ) (X : BinaryRealGL) :
    eichlerNormal n F (GeneralLinearGroup.scalar (Fin 2) c * X) = eichlerNormal n F X := by
  funext h
  rw [eichlerNormal_def, eichlerNormal_def, basePoint_scalar_mul]

/-- The scalar `normPower (det c) ((n + 3) / 2) · c⁻² · c^{-(n+1)}` of a positive real `c` is
one. -/
theorem normPower_scalar_factor {c : ℝˣ} (hc : 0 < c.val) :
    normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.scalar (Fin 2) c)))
        (((n : ℂ) + 3) / 2) *
      ((Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) c : ℂ) ^ (2 * (-1 : ℤ)) *
        ((Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) c : ℂ))⁻¹ ^ (n + 1)) = 1 := by
  have det : (GeneralLinearGroup.scalar (Fin 2) c).val.det = c.val ^ 2 := by
    rw [← GeneralLinearGroup.val_det_apply, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      Units.val_pow_eq_pow_val]
  have unit : ((Units.map (algebraMap ℝ ℂ : ℝ →* ℂ) c : ℂˣ) : ℂ) = (c.val : ℂ) := rfl
  have nonzero : (c.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have power : Complex.exp ((((n : ℂ) + 3) / 2) * (Real.log (c.val ^ 2) : ℂ)) =
      (c.val : ℂ) ^ (n + 3) := by
    rw [Real.log_pow, show (((n : ℂ) + 3) / 2) * (((2 : ℕ) * Real.log c.val : ℝ) : ℂ) =
      ((n + 3 : ℕ) : ℂ) * (Real.log c.val : ℂ) by push_cast; ring, Complex.exp_nat_mul,
      ← Complex.ofReal_exp, Real.exp_log hc]
  rw [binary_normalizingFactor_eq, det, power, unit]
  field_simp
  rw [show (2 : ℤ) * -1 = -2 by norm_num, _root_.zpow_neg, zpow_two, one_div, inv_pow]
  field_simp
  ring

/-- Positive scalars act trivially on functions invariant under right translation by them. -/
theorem binaryAmbientRepresentation_scalar {c : ℝˣ} (hc : 0 < c.val)
    (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (invariant : ∀ h, f (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c)) = f h) :
    binaryAmbientRepresentation n (GeneralLinearGroup.scalar (Fin 2) c) f = f := by
  funext h
  change normPower (GeneralLinearGroup.det (atInfinity (GeneralLinearGroup.scalar (Fin 2) c)))
      (((n : ℂ) + 3) / 2) • binaryCoefficient n (GeneralLinearGroup.scalar (Fin 2) c)
        (f (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c))) = f h
  rw [invariant, binaryCoefficient, GeneralLinearGroup.map_scalar,
    EisensteinRegularization.Helpers.binary_homogeneous_action_scalar, smul_smul,
    normPower_scalar_factor hc, one_smul]

namespace EichlerData

theorem eichlerPeriod_central (hF : EichlerData n F) {c : ℝˣ} (hc : 0 < c.val) (z : ℂ)
    (h : BinaryAdelicGL) :
    eichlerPeriod n F z (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c)) =
      eichlerPeriod n F z h := by
  simp only [eichlerPeriod, eichlerIntegrand, hF.central c hc]

theorem eichlerNormal_central (hF : EichlerData n F) {c : ℝˣ} (hc : 0 < c.val)
    (B : BinaryRealGL) (h : BinaryAdelicGL) :
    eichlerNormal n F B (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c)) =
      eichlerNormal n F B h := by
  have commute : atInfinity (GeneralLinearGroup.scalar (Fin 2) c) * atInfinity UpperHalfPlane.J =
      atInfinity UpperHalfPlane.J * atInfinity (GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [← atInfinity_mul, ← atInfinity_mul, GeneralLinearGroup.scalar_commute]
  have reflected : binaryAmbientRepresentation n UpperHalfPlane.J
      (eichlerPeriod n F (binaryComplexReflection (basePoint B)))
        (h * atInfinity (GeneralLinearGroup.scalar (Fin 2) c)) =
      binaryAmbientRepresentation n UpperHalfPlane.J
        (eichlerPeriod n F (binaryComplexReflection (basePoint B))) h := by
    change binaryCohomologicalAction n UpperHalfPlane.J _ _ =
      binaryCohomologicalAction n UpperHalfPlane.J _ _
    unfold binaryCohomologicalAction
    rw [mul_assoc, commute, ← mul_assoc, hF.eichlerPeriod_central hc]
  rw [eichlerNormal_def, eichlerNormal_def, hF.eichlerPeriod_central hc, reflected]

theorem antiholomorphic_mul (hF : EichlerData n F) {A : BinaryRealGL} (hA : A.val.det = 1)
    (B : BinaryRealGL) :
    eichlerAntiholomorphic n F (A * B) = eichlerAntiholomorphic n F A +
      binaryAmbientRepresentation n A (eichlerAntiholomorphic n F B) := by
  have split : UpperHalfPlane.J * (A * B) =
      (UpperHalfPlane.J * A * UpperHalfPlane.J) * (UpperHalfPlane.J * B) := by
    rw [mul_assoc (UpperHalfPlane.J * A), ← mul_assoc UpperHalfPlane.J UpperHalfPlane.J,
      upperJ_mul_self, one_mul, mul_assoc]
  have action : binaryAmbientRepresentation n UpperHalfPlane.J ∘ₗ
      binaryAmbientRepresentation n (UpperHalfPlane.J * A * UpperHalfPlane.J) =
      binaryAmbientRepresentation n A ∘ₗ binaryAmbientRepresentation n UpperHalfPlane.J := by
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, ← mul_assoc,
      ← mul_assoc, upperJ_mul_self, one_mul]
  have moved := LinearMap.congr_fun action (eichlerHolomorphic n F (UpperHalfPlane.J * B))
  simp only [LinearMap.comp_apply] at moved
  rw [eichlerAntiholomorphic_eq, eichlerAntiholomorphic_eq, eichlerAntiholomorphic_eq, split,
    eichlerHolomorphic_mul F hF.holomorphic hF.modular (det_upperJ_conj hA),
    eichlerHolomorphic_mul_J, map_add, moved]

theorem normal_mul_of_det_one (hF : EichlerData n F) {A : BinaryRealGL} (hA : A.val.det = 1)
    (B : BinaryRealGL) :
    eichlerNormal n F (A * B) =
      eichlerNormal n F A + binaryAmbientRepresentation n A (eichlerNormal n F B) := by
  rw [eichlerNormal_eq_hol_add_anti, eichlerNormal_eq_hol_add_anti,
    eichlerNormal_eq_hol_add_anti, eichlerHolomorphic_mul F hF.holomorphic hF.modular hA,
    hF.antiholomorphic_mul hA, map_add]
  abel

theorem normal_mul_of_unimodular (hF : EichlerData n F) {A : BinaryRealGL}
    (hA : |A.val.det| = 1) (B : BinaryRealGL) :
    eichlerNormal n F (A * B) =
      eichlerNormal n F A + binaryAmbientRepresentation n A (eichlerNormal n F B) := by
  rcases abs_eq (zero_le_one' ℝ) |>.mp hA with positive | negative
  · exact hF.normal_mul_of_det_one positive B
  · have det_one : (UpperHalfPlane.J * A).val.det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, det_upperJ, negative]
      norm_num
    have back : A = UpperHalfPlane.J * (UpperHalfPlane.J * A) := by
      rw [← mul_assoc, upperJ_mul_self, one_mul]
    conv_lhs => rw [back, mul_assoc, eichlerNormal_J_mul, hF.normal_mul_of_det_one det_one,
      map_add, ← eichlerNormal_J_mul, ← back, ← Module.End.mul_apply, ← map_mul, ← back]

/-- **The pointwise Eichler normal form is a pointwise binary cocycle.** -/
theorem isBinaryPointCocycle (hF : EichlerData n F) :
    IsBinaryPointCocycle (eichlerNormal n F) := by
  intro A C
  have hdet : 0 < |A.val.det| := abs_pos.mpr A.det_ne_zero
  set c : ℝˣ := Units.mk0 (Real.sqrt |A.val.det|) (Real.sqrt_pos.mpr hdet).ne'
  have hc : 0 < c.val := Real.sqrt_pos.mpr hdet
  set A₁ : BinaryRealGL := GeneralLinearGroup.scalar (Fin 2) c⁻¹ * A
  have unimodular : |A₁.val.det| = 1 := by
    have e : A₁.val.det = (c.val ^ 2)⁻¹ * A.val.det := by
      rw [← GeneralLinearGroup.val_det_apply, map_mul, GeneralLinearGroup.det_scalar,
        Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        GeneralLinearGroup.val_det_apply, inv_pow]
    rw [e, abs_mul, abs_inv, abs_of_pos (pow_pos hc 2), Units.val_mk0, Real.sq_sqrt hdet.le,
      inv_mul_cancel₀ hdet.ne']
  have split : A = GeneralLinearGroup.scalar (Fin 2) c * A₁ := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have invariant := binaryAmbientRepresentation_scalar (n := n) hc (eichlerNormal n F C)
    (hF.eichlerNormal_central hc C)
  clear_value A₁
  rw [split, mul_assoc, eichlerNormal_scalar_mul, eichlerNormal_scalar_mul,
    hF.normal_mul_of_unimodular unimodular, GeneralLinearGroup.scalar_commute, map_mul,
    Module.End.mul_apply, invariant]

end EichlerData

/-! ### Regularity of the pointwise normal form -/

theorem eichlerPointNormal_I (F : BinaryAdelicGL → ℂ → ℂ) (h : BinaryAdelicGL) :
    eichlerPointNormal n F Complex.I h = 0 := by
  rw [eichlerPointNormal, binaryComplexReflection_basepoint, eichlerPeriod_I]
  simp

/-- A compact subset of the upper half plane lies in a compact convex subset of the upper half
plane containing `i`. -/
theorem exists_convex_compact_upper {W : Set ℂ} (hW : IsCompact W)
    (hsub : W ⊆ {z : ℂ | 0 < z.im}) :
    ∃ K : Set ℂ, W ⊆ K ∧ Complex.I ∈ K ∧ K ⊆ {z : ℂ | 0 < z.im} ∧ IsCompact K ∧ Convex ℝ K := by
  obtain ⟨δ, hδ, hδW⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ W, δ ≤ w.im := by
    rcases W.eq_empty_or_nonempty with empty | nonempty
    · exact ⟨1, one_pos, by simp [empty]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hW.exists_isMinOn nonempty Complex.continuous_im.continuousOn
      exact ⟨w₀.im, hsub hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := hW.exists_bound_of_continuousOn continuous_norm.continuousOn
  refine ⟨Metric.closedBall 0 (max R 1) ∩ {z : ℂ | min δ 1 ≤ z.im}, fun w hw => ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (le_trans (le_of_eq (norm_norm w).symm) (hR w hw)).trans (le_max_left _ _)
  · exact (min_le_left _ _).trans (hδW w hw)
  · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_I]
    exact le_max_right _ _
  · simp
  · intro z hz
    exact lt_of_lt_of_le (lt_min hδ one_pos) hz.2
  · exact (isCompact_closedBall 0 _).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
  · exact (convex_closedBall 0 _).inter (convex_halfSpace_im_ge _)

namespace EichlerData

/-- **The coordinates of the pointwise normal form are Lipschitz** on compact convex subsets of the
upper half plane, uniformly in the adelic argument. -/
theorem coord_lipschitz (hF : EichlerData n F) {K : Set ℂ} (hK : K ⊆ {z : ℂ | 0 < z.im})
    (hKc : IsCompact K) (hconv : Convex ℝ K) (j : Fin (n + 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ h, ∀ z ∈ K, ∀ w ∈ K,
      ‖(binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h) -
        (binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F z h)‖ ≤ D * ‖w - z‖ := by
  obtain ⟨D, hD⟩ := exists_bound_eichlerPointNormalDeriv F hF.holomorphic hF.bounded hK hKc j
  refine ⟨max D 0, le_max_right _ _, fun h z hz w hw => ?_⟩
  exact hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx =>
      (hasFDerivAt_coord_eichlerPointNormal F hF.holomorphic (hK hx) h j).hasFDerivWithinAt)
    (fun x hx => (hD h x hx).trans (le_max_left _ _)) hz hw

/-- **The coordinates of the pointwise normal form are bounded** on compact subsets of the upper
half plane, uniformly in the adelic argument. -/
theorem coord_bounded (hF : EichlerData n F) {W : Set ℂ} (hW : IsCompact W)
    (hsub : W ⊆ {z : ℂ | 0 < z.im}) (j : Fin (n + 2)) :
    ∃ C : ℝ, ∀ h, ∀ w ∈ W,
      ‖(binaryWeightBasis (n + 1)).coord j (eichlerPointNormal n F w h)‖ ≤ C := by
  obtain ⟨K, hWK, hIK, hK, hKc, hconv⟩ := exists_convex_compact_upper hW hsub
  obtain ⟨D, hD0, hD⟩ := hF.coord_lipschitz hK hKc hconv j
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn
    (continuous_id.sub continuous_const).norm.continuousOn (f := fun w => ‖w - Complex.I‖)
  refine ⟨D * R, fun h w hw => ?_⟩
  have := hD h Complex.I hIK w (hWK hw)
  rw [eichlerPointNormal_I, map_zero, sub_zero] at this
  refine this.trans (mul_le_mul_of_nonneg_left ?_ hD0)
  simpa using hR w (hWK hw)

theorem eichlerNormal_bounded (hF : EichlerData n F) (K : Set BinaryRealGL)
    (compact : IsCompact K) (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, ∀ A ∈ K, ∀ h, ‖functional (eichlerNormal n F A h)‖ ≤ C := by
  have image : IsCompact (basePoint '' K) :=
    compact.image (UpperHalfPlane.continuous_coe.comp smul_I_continuous)
  have upper : basePoint '' K ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨A, _, rfl⟩
    exact (A • UpperHalfPlane.I).im_pos
  obtain ⟨C, hC⟩ := bound_functional_of_coord
    (fun point : BinaryRealGL × BinaryAdelicGL => eichlerNormal n F point.1 point.2)
    (K ×ˢ Set.univ) (fun j => by
      obtain ⟨C, hC⟩ := hF.coord_bounded image upper j
      exact ⟨C, fun point member => by
        rw [eichlerNormal_eq_eichlerPointNormal]
        exact hC point.2 _ ⟨point.1, member.1, rfl⟩⟩) functional
  exact ⟨C, fun A hA h => hC (A, h) ⟨hA, Set.mem_univ _⟩⟩

/-- **The pointwise Eichler normal form of a scalar form with Eichler data**, as a pointwise binary
cocycle. -/
def pointCocycle (hF : EichlerData n F) : BinaryPointCocycle n where
  value := eichlerNormal n F
  cocycle := hF.isBinaryPointCocycle
  continuous := eichlerNormal_continuous F (fun h => (hF.holomorphic h).continuousOn)
  bounded := hF.eichlerNormal_bounded

theorem pointCocycle_value (hF : EichlerData n F) : hF.pointCocycle.value = eichlerNormal n F :=
  rfl

end EichlerData

end TernaryPeriodPolynomials.AnalyticClasses
