module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.NormalCocycleHolomorphic

@[expose] public section


/-!
# The good-line transport of the twisted Eichler normal form is a one-cocycle

For a family `F h` of holomorphic functions of weight `n + 3` (in the application the scalar
weighted realization of the classical lower endpoint, of rotation weight `2k = -(n + 3)`), the
holomorphic half `N_hol(A) = ½ Per(A · i)` of the Eichler normal form is a cocycle for
determinant-one `A`, and the antiholomorphic half is its conjugate by `J`:
`N_anti(A) = J · N_hol(J A)`. Hence the twisted normal form `N⁻ = N_hol - N_anti` satisfies
`N⁻(C J) = N⁻(C)`, `N⁻(J C) = -J · N⁻(C)` and the twisted cocycle law
`N⁻(A B) = N⁻(A) + det A · A · N⁻(B)` for `det A = ±1`. Transporting along the pivot conjugation
`m ↦ σ m σ` and the swap of the binary variables, the edge normal form
`edgeNormal F m = Sw (N⁻ (σ m σ))` is a one-cocycle of the real Levi for `edgeAction`, and it
vanishes on the stabilizer of `i`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

theorem binaryAmbientRepresentation_apply_of_unimodular {A : BinaryRealGL}
    (hA : |A.val.det| = 1) (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1))
    (h : BinaryAdelicGL) :
    binaryAmbientRepresentation n A f h = binaryCoefficient n A (f (h * atInfinity A)) := by
  change normPower (GeneralLinearGroup.det (atInfinity A)) (((n : ℂ) + 3) / 2) •
    binaryCoefficient n A (f (h * atInfinity A)) = _
  rw [normPower_det_unimodular hA, one_smul]

theorem eichlerHolomorphic_eq_smul (F : BinaryAdelicGL → ℂ → ℂ) (A : BinaryRealGL) :
    eichlerHolomorphic n F A = (2 : ℂ)⁻¹ • eichlerPeriod n F (basePoint A) := rfl

theorem basePoint_mul_J (C : BinaryRealGL) : basePoint (C * UpperHalfPlane.J) = basePoint C := by
  rw [basePoint, mul_smul, binaryReflection_smul_I, basePoint]

theorem basePoint_J_mul (C : BinaryRealGL) :
    basePoint (UpperHalfPlane.J * C) = binaryComplexReflection (basePoint C) := by
  rw [basePoint, mul_smul, UpperHalfPlane.coe_J_smul, basePoint]
  simp [binaryComplexReflection]

theorem upperJ_mul_self : (UpperHalfPlane.J * UpperHalfPlane.J : BinaryRealGL) = 1 := by
  rw [← sq, UpperHalfPlane.J_sq]

theorem binaryAmbientRepresentation_J_J (f : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)) :
    binaryAmbientRepresentation n UpperHalfPlane.J
      (binaryAmbientRepresentation n UpperHalfPlane.J f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, upperJ_mul_self, map_one, Module.End.one_apply]

theorem eichlerAntiholomorphic_eq (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerAntiholomorphic n F C = binaryAmbientRepresentation n UpperHalfPlane.J
      (eichlerHolomorphic n F (UpperHalfPlane.J * C)) := by
  funext h
  rw [eichlerHolomorphic_eq_smul, map_smul, Pi.smul_apply, basePoint_J_mul]
  rfl

theorem eichlerTwisted_eq (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerTwisted n F C = eichlerHolomorphic n F C - binaryAmbientRepresentation n
      UpperHalfPlane.J (eichlerHolomorphic n F (UpperHalfPlane.J * C)) := by
  rw [← eichlerAntiholomorphic_eq]
  rfl

theorem eichlerHolomorphic_mul_J (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerHolomorphic n F (C * UpperHalfPlane.J) = eichlerHolomorphic n F C := by
  rw [eichlerHolomorphic_eq_smul, eichlerHolomorphic_eq_smul, basePoint_mul_J]

/-- The twisted normal form only depends on the coset `C · ⟨J⟩`. -/
theorem eichlerTwisted_mul_J (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerTwisted n F (C * UpperHalfPlane.J) = eichlerTwisted n F C := by
  rw [eichlerTwisted_eq, eichlerTwisted_eq, eichlerHolomorphic_mul_J, ← mul_assoc,
    eichlerHolomorphic_mul_J]

/-- Left multiplication by `J` negates the twisted normal form, up to the action of `J`. -/
theorem eichlerTwisted_J_mul (F : BinaryAdelicGL → ℂ → ℂ) (C : BinaryRealGL) :
    eichlerTwisted n F (UpperHalfPlane.J * C) =
      -binaryAmbientRepresentation n UpperHalfPlane.J (eichlerTwisted n F C) := by
  rw [eichlerTwisted_eq, eichlerTwisted_eq, ← mul_assoc, upperJ_mul_self, one_mul, map_sub,
    binaryAmbientRepresentation_J_J, neg_sub]

theorem det_upperJ : (UpperHalfPlane.J : BinaryRealGL).val.det = -1 := by
  rw [← GeneralLinearGroup.val_det_apply, UpperHalfPlane.det_J, Units.val_neg, Units.val_one]

theorem det_upperJ_conj {A : BinaryRealGL} (hA : A.val.det = 1) :
    (UpperHalfPlane.J * A * UpperHalfPlane.J).val.det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_upperJ, hA]
  norm_num

/-! ### The cocycle laws -/

section Cocycle

variable (F : BinaryAdelicGL → ℂ → ℂ)
  (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
  (modular : ∀ A : BinaryRealGL, A.val.det = 1 → ∀ h (z : UpperHalfPlane),
    F (h * atInfinity A) z = UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) * F h (A • z : _))
include holomorphic modular

/-- **The holomorphic half of the normal form is a cocycle** on determinant-one matrices. -/
theorem eichlerHolomorphic_mul {A : BinaryRealGL} (hA : A.val.det = 1) (B : BinaryRealGL) :
    eichlerHolomorphic n F (A * B) =
      eichlerHolomorphic n F A + binaryAmbientRepresentation n A (eichlerHolomorphic n F B) := by
  funext h
  rw [Pi.add_apply, binaryAmbientRepresentation_apply_of_unimodular (by rw [hA, abs_one])]
  simp only [eichlerHolomorphic]
  rw [eichlerPeriod_basePoint_mul F holomorphic modular A hA B h, smul_add, map_smul]

/-- **The twisted normal form is a cocycle** for determinant-one matrices on the left. -/
theorem eichlerTwisted_mul_of_det_one {A : BinaryRealGL} (hA : A.val.det = 1)
    (B : BinaryRealGL) :
    eichlerTwisted n F (A * B) =
      eichlerTwisted n F A + binaryAmbientRepresentation n A (eichlerTwisted n F B) := by
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
  rw [eichlerTwisted_eq, eichlerTwisted_eq, eichlerTwisted_eq, split,
    eichlerHolomorphic_mul F holomorphic modular hA,
    eichlerHolomorphic_mul F holomorphic modular (det_upperJ_conj hA), eichlerHolomorphic_mul_J,
    map_add, moved, map_sub]
  abel

/-- **The twisted cocycle law** `N⁻(A B) = N⁻(A) + det A · A · N⁻(B)` for `det A = ±1`. -/
theorem eichlerTwisted_mul {A : BinaryRealGL} (hA : |A.val.det| = 1) (B : BinaryRealGL) :
    eichlerTwisted n F (A * B) = eichlerTwisted n F A +
      ((A.val.det : ℝ) : ℂ) • binaryAmbientRepresentation n A (eichlerTwisted n F B) := by
  rcases abs_eq (zero_le_one' ℝ) |>.mp hA with positive | negative
  · rw [positive, Complex.ofReal_one, one_smul]
    exact eichlerTwisted_mul_of_det_one F holomorphic modular positive B
  · have det_one : (UpperHalfPlane.J * A).val.det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, det_upperJ, negative]
      norm_num
    have back : A = UpperHalfPlane.J * (UpperHalfPlane.J * A) := by
      rw [← mul_assoc, upperJ_mul_self, one_mul]
    have flip : ∀ x : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1), (-1 : ℂ) • x = -x :=
      fun x => neg_one_smul ℂ x
    rw [negative, Complex.ofReal_neg, Complex.ofReal_one, flip]
    conv_lhs => rw [back, mul_assoc, eichlerTwisted_J_mul,
      eichlerTwisted_mul_of_det_one F holomorphic modular det_one, map_add, ← Module.End.mul_apply,
      ← map_mul, ← back, neg_add, ← eichlerTwisted_J_mul, ← back]

end Cocycle

/-! ### Transport along the pivot conjugation and the swap -/

theorem binaryCoefficient_val_eq (A : BinaryRealGL) (P : Binary.HomogeneousPoly (n + 1)) :
    (binaryCoefficient n A P).val = ((A.val.det : ℂ))⁻¹ •
      Binary.substitute (GeneralLinearGroup.map (algebraMap ℝ ℂ) A)⁻¹.val P.val := by
  rw [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply]
  congr 1
  simp only [Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply, det_map_algebraMap_complex,
    _root_.zpow_neg_one]

theorem pivotConjugate_inv (m : BinaryRealGL) : (pivotConjugate m)⁻¹ = pivotConjugate m⁻¹ := by
  have swap : (binaryPivotSwap⁻¹ : BinaryRealGL) = binaryPivotSwap :=
    inv_eq_of_mul_eq_one_right binaryPivotSwap_mul_self
  unfold pivotConjugate
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, swap, mul_assoc]

theorem pivotConjugate_map_val (X : BinaryRealGL) :
    (GeneralLinearGroup.map (algebraMap ℝ ℂ) (pivotConjugate X)).val =
      (GeneralLinearGroup.map (algebraMap ℝ ℂ) X).val.submatrix (Equiv.swap 0 1)
        (Equiv.swap 0 1) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [pivotConjugate, binaryPivotSwap, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_pivotConjugate (m : BinaryRealGL) : (pivotConjugate m).val.det = m.val.det := by
  unfold pivotConjugate
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  have swap : (binaryPivotSwap : BinaryRealGL).val.det = -1 := by
    simp [binaryPivotSwap, Matrix.det_fin_two]
  rw [swap]
  ring

theorem rename_swap_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) (P : Binary.Poly) :
    rename (Equiv.swap (0 : Fin 2) 1)
        (Binary.substitute (M.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1)) P) =
      Binary.substitute M (rename (Equiv.swap (0 : Fin 2) 1) P) := by
  have homs : (rename (Equiv.swap (0 : Fin 2) 1)).comp
      (Binary.substitute (M.submatrix (Equiv.swap 0 1) (Equiv.swap 0 1))) =
      (Binary.substitute M).comp (rename (Equiv.swap (0 : Fin 2) 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Binary.substitute_X, rename_X, Binary.linearForm,
      Fin.sum_univ_two]
    fin_cases i <;> simp [add_comm]
  exact DFunLike.congr_fun homs P

/-- The swap of the binary variables intertwines the coefficient actions of `σ m σ` and `m`. -/
theorem binarySwap_binaryCoefficient (m : BinaryRealGL) (P : Binary.HomogeneousPoly (n + 1)) :
    binarySwap n (binaryCoefficient n (pivotConjugate m) P) =
      binaryCoefficient n m (binarySwap n P) := by
  apply Subtype.ext
  change rename (Equiv.swap (0 : Fin 2) 1) (binaryCoefficient n (pivotConjugate m) P).val =
    (binaryCoefficient n m (binarySwap n P)).val
  rw [binaryCoefficient_val_eq, binaryCoefficient_val_eq, map_smul, det_pivotConjugate, ← map_inv,
    ← map_inv, pivotConjugate_inv]
  congr 1
  rw [pivotConjugate_map_val, rename_swap_substitute]
  rfl

/-! ### The edge normal form -/

/-- **The good-line transport of the twisted normal form is a one-cocycle of the real Levi.** -/
theorem edgeNormal_mul (F : BinaryAdelicGL → ℂ → ℂ)
    (holomorphic : ∀ h, DifferentiableOn ℂ (F h) {z : ℂ | 0 < z.im})
    (modular : ∀ A : BinaryRealGL, A.val.det = 1 → ∀ h (z : UpperHalfPlane),
      F (h * atInfinity A) z = UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) * F h (A • z : _))
    (a b : unimodularLevi) :
    edgeNormal n F (a * b) = edgeNormal n F a + edgeAction a (edgeNormal n F b) := by
  funext h
  have unimodular : |(pivotConjugate (a : BinaryRealGL)).val.det| = 1 := by
    rw [abs_det_pivotConjugate]
    exact a.property
  simp only [edgeNormal, edgeAction, Pi.add_apply, Subgroup.coe_mul, pivotConjugate_mul]
  rw [eichlerTwisted_mul F holomorphic modular unimodular, Pi.add_apply, Pi.smul_apply,
    binaryAmbientRepresentation_apply_of_unimodular unimodular, map_add, map_smul,
    binarySwap_binaryCoefficient, det_pivotConjugate]

theorem eichlerPeriod_I_eq_zero (F : BinaryAdelicGL → ℂ → ℂ) :
    eichlerPeriod n F Complex.I = 0 := by
  funext h
  simp only [eichlerPeriod, eichlerIntegrand, sub_self, zero_mul, intervalIntegral.integral_zero,
    zero_smul, Finset.sum_const_zero, Pi.zero_apply]

/-- The twisted normal form vanishes on the stabilizer of `i`. -/
theorem eichlerTwisted_of_basePoint (F : BinaryAdelicGL → ℂ → ℂ) {C : BinaryRealGL}
    (base : basePoint C = Complex.I) : eichlerTwisted n F C = 0 := by
  funext h
  simp only [eichlerTwisted, eichlerHolomorphic, eichlerAntiholomorphic, base,
    binaryComplexReflection_basepoint, eichlerPeriod_I_eq_zero, map_zero, Pi.zero_apply,
    smul_zero, sub_zero]

/-- **The edge normal form vanishes when `σ m σ` fixes `i`.** -/
theorem edgeNormal_of_basePoint (F : BinaryAdelicGL → ℂ → ℂ) {m : unimodularLevi}
    (base : basePoint (pivotConjugate (m : BinaryRealGL)) = Complex.I) : edgeNormal n F m = 0 := by
  funext h
  rw [edgeNormal, eichlerTwisted_of_basePoint F base, Pi.zero_apply, map_zero]

theorem binaryPivotSwap_smul_I :
    (binaryPivotSwap : BinaryRealGL) • UpperHalfPlane.I = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul]
  simp [UpperHalfPlane.σ, UpperHalfPlane.num, UpperHalfPlane.denom, binaryPivotSwap]
  norm_num

/-- **The edge normal form vanishes on the stabilizer of `i`** (rotations, `±1`, `±J`). -/
theorem edgeNormal_of_smul_I (F : BinaryAdelicGL → ℂ → ℂ) {m : unimodularLevi}
    (fixes : (m : BinaryRealGL) • UpperHalfPlane.I = UpperHalfPlane.I) : edgeNormal n F m = 0 := by
  apply edgeNormal_of_basePoint
  rw [basePoint, pivotConjugate, mul_smul, mul_smul, binaryPivotSwap_smul_I, fixes,
    binaryPivotSwap_smul_I, UpperHalfPlane.coe_I]

theorem binaryRotations_mem_unimodularLevi (angle : Circle) :
    binaryRotations angle ∈ unimodularLevi := by
  change |(binaryRotations angle).val.det| = 1
  rw [← GeneralLinearGroup.val_det_apply, binaryRotations_det, abs_one]

/-- **The edge normal form vanishes on the rotations.** -/
theorem edgeNormal_rotation (F : BinaryAdelicGL → ℂ → ℂ) (angle : Circle) :
    edgeNormal n F ⟨binaryRotations angle, binaryRotations_mem_unimodularLevi angle⟩ = 0 :=
  edgeNormal_of_smul_I F (binaryRotations_smul_I angle)

/-! ### The scalar weighted realization of the lower endpoint -/

/-- The scalar weighted realization of a vector of rotation weight `2k` has weight `-2k` under
right translation by determinant-one matrices. -/
theorem cuspScalarWeightedRealization_translate (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (A : BinaryRealGL) (hA : A.val.det = 1) (h : BinaryAdelicGL) (z : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector (h * atInfinity A) z =
      UpperHalfPlane.denom A z ^ (2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector h ((A • z : UpperHalfPlane) : ℂ) := by
  have det : (GeneralLinearGroup.det A).val = 1 := by
    rw [GeneralLinearGroup.val_det_apply, hA]
  have identity := cuspScalarAffineRealization_rotation cusp vector (2 * halfWeight) rotation h A
    det z
  have phase := binary_weighted_phase_identity A det z halfWeight
  simp only [cuspScalarWeightedRealization, Complex.real_smul, UpperHalfPlane.coe_im]
  rw [phase, cuspScalarAffineRealization, binaryUpperSectionMatrix_coe, invertibleMatrix_coe,
    mul_assoc, ← atInfinity_mul, identity]
  have cancel : UpperHalfPlane.denom A z ^ (2 * halfWeight) *
      UpperHalfPlane.denom A z ^ (-2 * halfWeight) = 1 := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero A z)]
    ring_nf
    exact zpow_zero _
  linear_combination (-(↑(z.im ^ halfWeight) * binaryPhaseValue A ↑z ^ (2 * halfWeight) *
    cuspScalarAffineRealization cusp vector h ↑(A • z))) * cancel

section Endpoint

variable (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
  (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
    (angle : ℂ) ^ (2 * halfWeight) • vector.val)
  (weight : 2 * halfWeight = -((n : ℤ) + 3))
  (holomorphic : ∀ h, DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector h)
    UpperHalfPlane.upperHalfPlaneSet)

include rotation weight in
theorem cuspScalarWeightedRealization_modular_weight (A : BinaryRealGL) (hA : A.val.det = 1)
    (h : BinaryAdelicGL) (z : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector (h * atInfinity A) z =
      UpperHalfPlane.denom A z ^ (-((n : ℤ) + 3)) *
        cuspScalarWeightedRealization cusp halfWeight vector h ((A • z : UpperHalfPlane) : ℂ) := by
  rw [← weight]
  exact cuspScalarWeightedRealization_translate cusp halfWeight vector rotation A hA h z

include rotation weight holomorphic in
/-- **The edge normal form of the classical lower endpoint is a one-cocycle of the real Levi**:
`Ẽ(a b) = Ẽ(a) + a ⋆ Ẽ(b)` with `(m ⋆ G)(h) = det m · binaryCoefficient m (G (h · σ m σ))`. -/
theorem cuspScalar_edgeNormal_mul (a b : unimodularLevi) :
    edgeNormal n (cuspScalarWeightedRealization cusp halfWeight vector) (a * b) =
      edgeNormal n (cuspScalarWeightedRealization cusp halfWeight vector) a +
        edgeAction a (edgeNormal n (cuspScalarWeightedRealization cusp halfWeight vector) b) :=
  edgeNormal_mul _ holomorphic
    (cuspScalarWeightedRealization_modular_weight cusp halfWeight vector rotation weight) a b

end Endpoint

end TernaryPeriodPolynomials.AnalyticClasses
