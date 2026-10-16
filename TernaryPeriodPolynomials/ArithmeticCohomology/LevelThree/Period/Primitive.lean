module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.PeriodPolynomial

@[expose] public section


/-!
# Holomorphic Eichler integrals of arbitrary holomorphic functions

For a holomorphic function `f` on the upper half-plane and `m : ℕ`, the polynomial-valued
differential `f(z) (X₀ - z X₁)^m dz` (`pointForm`) has a holomorphic primitive `P` on the upper
half-plane, normalized by `P(i) = 0` (`primitive`). It is unique (`eq_primitive_add`) and hence
linear in `f` (`primitive_add`, `primitive_smul`). This generalizes Sol's level-one
`classicalBinaryPrimitive`, whose construction only uses holomorphy.

For a real matrix `M` of positive determinant `D`, with `j(M, z) = cz + d`,
`M · (X₀ - (M z) X₁)^m = (D / j(M, z))^m (X₀ - z X₁)^m` under right substitution
(`substitute_pointPower`), so for the coefficient representation `Sym^m ⊗ det^e`
the function `z ↦ ρ(M)⁻¹ P(M z)` is a primitive of `D^{-e} (f ∣[m+2] M)(z) (X₀ - z X₁)^m dz`
(`transform_hasDerivAt`). In particular, if `f ∣[m+2] M = f` and `D = 1`, then
`P(M z) = P(M i) + ρ(M) P(z)` (`primitive_modular`): `M ↦ P(M i)` is a cocycle.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein Matrix MvPolynomial UpperHalfPlane
open scoped Manifold ModularForm
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive

variable (m : ℕ)

/-- The coefficient space `Sym^m(ℂ²)`. -/
abbrev V := Binary.HomogeneousPoly m

/-- The polynomial-valued differential `f(z) (X₀ - z X₁)^m`. -/
def pointForm (f : ℍ → ℂ) (z : ℂ) : V m :=
  f (ofComplex z) • binaryPointPower m z

theorem pointForm_add (f g : ℍ → ℂ) (z : ℂ) :
    pointForm m (f + g) z = pointForm m f z + pointForm m g z := by
  simp [pointForm, add_smul]

theorem pointForm_smul (c : ℂ) (f : ℍ → ℂ) (z : ℂ) :
    pointForm m (c • f) z = c • pointForm m f z := by
  simp [pointForm, smul_smul]

theorem pointForm_coord_differentiableOn {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (ℓ : V m →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => ℓ (pointForm m f z)) upperHalfPlaneSet := by
  have holomorphic := UpperHalfPlane.mdifferentiable_iff.mp hf
  simp only [pointForm, map_smul, smul_eq_mul]
  intro z hz
  exact (holomorphic z hz).mul
    (binaryPointPower_functional_analytic m ℓ z).differentiableAt.differentiableWithinAt

/-- Being a primitive of `pointForm m f` on the upper half-plane, functional by functional. -/
def IsPrimitive (f : ℍ → ℂ) (P : ℂ → V m) : Prop :=
  ∀ (ℓ : V m →ₗ[ℂ] ℂ) (z : ℂ), 0 < z.im →
    HasDerivAt (fun w => ℓ (P w)) (ℓ (pointForm m f z)) z

theorem exists_primitive {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ P : ℂ → V m, P Complex.I = 0 ∧ IsPrimitive m f P := by
  have exists_coordinate (position : Fin (m + 1)) :=
    (convex_halfSpace_im_gt 0).exists_forall_hasDerivWithinAt
      (pointForm_coord_differentiableOn m hf ((binaryStandardBasis m).coord position))
  choose coordinate derivative using exists_coordinate
  let P : ℂ → V m := fun z =>
    ∑ position : Fin (m + 1), (coordinate position z - coordinate position Complex.I) •
      binaryStandardBasis m position
  refine ⟨P, ?_, ?_⟩
  · simp [P]
  · intro ℓ z positive
    have values : (fun z => ℓ (P z)) =
        fun z => ∑ position : Fin (m + 1),
          (coordinate position z - coordinate position Complex.I) *
            ℓ (binaryStandardBasis m position) := by
      funext z
      simp only [P, map_sum, map_smul, smul_eq_mul]
    have differential : ℓ (pointForm m f z) =
        ∑ position : Fin (m + 1),
          (binaryStandardBasis m).coord position (pointForm m f z) *
            ℓ (binaryStandardBasis m position) := by
      conv_lhs => rw [← (binaryStandardBasis m).sum_repr (pointForm m f z)]
      simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
    rw [values, differential]
    apply HasDerivAt.fun_sum
    intro position _
    exact (((derivative position z positive).hasDerivAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive)).sub_const
        (coordinate position Complex.I)).mul_const (ℓ (binaryStandardBasis m position))

open Classical in
/-- The holomorphic primitive of `f(z) (X₀ - z X₁)^m dz` with `P(i) = 0` (zero if `f` is not
holomorphic). -/
def primitive (f : ℍ → ℂ) : ℂ → V m :=
  if hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f then (exists_primitive m hf).choose else 0

theorem primitive_basepoint (f : ℍ → ℂ) : primitive m f Complex.I = 0 := by
  unfold primitive
  split_ifs with hf
  · exact (exists_primitive m hf).choose_spec.1
  · rfl

theorem primitive_isPrimitive {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    IsPrimitive m f (primitive m f) := by
  unfold primitive
  rw [dite_eq_left hf]
  exact (exists_primitive m hf).choose_spec.2

/-- A function with zero derivative (functional by functional) on the upper half-plane is
constant there. -/
theorem eq_of_hasDerivAt_zero (D : ℂ → V m)
    (zero : ∀ (ℓ : V m →ₗ[ℂ] ℂ) (z : ℂ), 0 < z.im → HasDerivAt (fun w => ℓ (D w)) 0 z)
    (z : ℂ) (hz : 0 < z.im) : D z = D Complex.I := by
  apply (binaryStandardBasis m).ext_elem
  intro position
  let ℓ := (binaryStandardBasis m).coord position
  change ℓ (D z) = ℓ (D Complex.I)
  apply (convex_halfSpace_im_gt 0).is_const_of_fderivWithin_eq_zero
    (fun w hw => (zero ℓ w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => ?_) hz (by simp)
  rw [fderivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hw]
  simpa using (zero ℓ w hw).hasFDerivAt.fderiv

/-- **Uniqueness of primitives.** Any primitive differs from `primitive` by its value at `i`. -/
theorem eq_primitive_add {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (F : ℂ → V m)
    (hF : IsPrimitive m f F) (z : ℂ) (hz : 0 < z.im) :
    F z = primitive m f z + F Complex.I := by
  have key := eq_of_hasDerivAt_zero m (fun w => F w - primitive m f w) (by
    intro ℓ w hw
    have h := (hF ℓ w hw).sub (primitive_isPrimitive m hf ℓ w hw)
    rw [sub_self] at h
    convert h using 1
    all_goals first | (solve | ext) | (funext v; exact map_sub ℓ _ _)) z hz
  rw [primitive_basepoint, sub_zero] at key
  rw [← key]
  abel

theorem primitive_add {f g : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (z : ℂ) (hz : 0 < z.im) :
    primitive m (f + g) z = primitive m f z + primitive m g z := by
  have h := eq_primitive_add m (hf.add hg) (fun w => primitive m f w + primitive m g w) (by
    intro ℓ w hw
    simp only [map_add, pointForm_add]
    exact (primitive_isPrimitive m hf ℓ w hw).add (primitive_isPrimitive m hg ℓ w hw)) z hz
  rw [primitive_basepoint, primitive_basepoint, add_zero, add_zero] at h
  exact h.symm

theorem primitive_smul (c : ℂ) {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (z : ℂ)
    (hz : 0 < z.im) : primitive m (c • f) z = c • primitive m f z := by
  have hcf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c • f) := by
    have e : c • f = (fun _ => c) * f := by
      funext w
      simp
    rw [e]
    exact mdifferentiable_const.mul hf
  have h := eq_primitive_add m hcf (fun w => c • primitive m f w) (by
    intro ℓ w hw
    simp only [map_smul, pointForm_smul, smul_eq_mul]
    exact (primitive_isPrimitive m hf ℓ w hw).const_mul c) z hz
  rw [primitive_basepoint, smul_zero, add_zero] at h
  exact h.symm

/-! ### Transformation under real matrices of positive determinant -/

/-- The complexification `GL₂(ℝ) → GL₂(ℂ)`. -/
abbrev complexify : GL (Fin 2) ℝ →* GL (Fin 2) ℂ := GeneralLinearGroup.map (algebraMap ℝ ℂ)

theorem det_complexify (M : GL (Fin 2) ℝ) :
    (complexify M).val.det = ((M.val.det : ℝ) : ℂ) := by
  change (M.val.map (algebraMap ℝ ℂ)).det = _
  rw [show M.val.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix M.val from rfl,
    ← RingHom.map_det]
  rfl

theorem denom_eq (M : GL (Fin 2) ℝ) (z : ℂ) :
    denom M z = (M.val 1 0 : ℂ) * z + (M.val 1 1 : ℂ) := rfl

theorem num_eq (M : GL (Fin 2) ℝ) (z : ℂ) :
    num M z = (M.val 0 0 : ℂ) * z + (M.val 0 1 : ℂ) := rfl

theorem substitute_linear (M : GL (Fin 2) ℝ) (hM : 0 < M.val.det) (z : ℍ) :
    Binary.substitute (complexify M).val (X 0 - C ((M • z : ℍ) : ℂ) * X 1) =
      C ((M.val.det : ℂ) / denom M z) * (X 0 - C (z : ℂ) * X 1) := by
  have hpos : 0 < ((GeneralLinearGroup.det M : ℝˣ) : ℝ) := by
    rwa [GeneralLinearGroup.val_det_apply]
  have hden : (M.val 1 0 : ℂ) * (z : ℂ) + (M.val 1 1 : ℂ) ≠ 0 := denom_ne_zero M z
  have hden' : (z : ℂ) * (M.val 1 0 : ℂ) + (M.val 1 1 : ℂ) ≠ 0 := by
    rw [mul_comm]
    exact hden
  have hw : ((M • z : ℍ) : ℂ) = num M z / denom M z := coe_smul_of_det_pos hpos z
  have hdet : (M.val.det : ℂ) = (M.val 0 0 : ℂ) * (M.val 1 1 : ℂ) -
      (M.val 0 1 : ℂ) * (M.val 1 0 : ℂ) := by
    rw [Matrix.det_fin_two]
    push_cast
    ring
  have h1 : (M.val 0 0 : ℂ) - ((M • z : ℍ) : ℂ) * (M.val 1 0 : ℂ) =
      (M.val.det : ℂ) / denom M z := by
    rw [hw, hdet, denom_eq, num_eq]
    first | (field_simp; done) | (field_simp; ring)
  have h2 : (M.val 0 1 : ℂ) - ((M • z : ℍ) : ℂ) * (M.val 1 1 : ℂ) =
      -((M.val.det : ℂ) / denom M z * (z : ℂ)) := by
    rw [hw, hdet, denom_eq, num_eq]
    first | (field_simp; done) | (field_simp; ring)
  simp only [Binary.substitute, map_sub, map_mul, bind₁_C_right, bind₁_X_right,
    Binary.linearForm, Fin.sum_univ_two]
  have e00 : (complexify M).val 0 0 = (M.val 0 0 : ℂ) := rfl
  have e01 : (complexify M).val 0 1 = (M.val 0 1 : ℂ) := rfl
  have e10 : (complexify M).val 1 0 = (M.val 1 0 : ℂ) := rfl
  have e11 : (complexify M).val 1 1 = (M.val 1 1 : ℂ) := rfl
  rw [e00, e01, e10, e11]
  have c1 := congrArg (C : ℂ → Binary.Poly) h1
  have c2 := congrArg (C : ℂ → Binary.Poly) h2
  simp only [map_sub, map_mul, map_neg] at c1 c2
  linear_combination (X 0 : Binary.Poly) * c1 + (X 1 : Binary.Poly) * c2

/-- `M · (X₀ - (M z) X₁)^m = (D / j(M, z))^m (X₀ - z X₁)^m`. -/
theorem substitute_pointPower (M : GL (Fin 2) ℝ) (hM : 0 < M.val.det) (z : ℍ) :
    Binary.substitute (complexify M).val (binaryPointPower m ((M • z : ℍ) : ℂ)).val =
      ((((M.val.det : ℂ) / denom M z) ^ m) • binaryPointPower m (z : ℂ)).val := by
  simp only [binaryPointPower, Submodule.coe_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [map_pow, substitute_linear M hM z, mul_pow, map_pow]

/-- `ρ(M)⁻¹ (X₀ - (M z) X₁)^m = D^{-e} (D / j(M, z))^m (X₀ - z X₁)^m` for `Sym^m ⊗ det^e`. -/
theorem action_inv_pointPower (e : ℤ) (M : GL (Fin 2) ℝ) (hM : 0 < M.val.det) (z : ℍ) :
    Binary.homogeneousAction m e (complexify M)⁻¹ (binaryPointPower m ((M • z : ℍ) : ℂ)) =
      (((M.val.det : ℂ) ^ (-e) * ((M.val.det : ℂ) / denom M z) ^ m)) •
        binaryPointPower m (z : ℂ) := by
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.action_apply, inv_inv, substitute_pointPower m M hM z]
  rw [Submodule.coe_smul, Submodule.coe_smul, smul_smul]
  congr 1
  change ((GeneralLinearGroup.det (complexify M)⁻¹ : ℂˣ) : ℂ) ^ e * _ = _
  rw [map_inv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply, det_complexify,
    _root_.inv_zpow']

/-- The slash operator of a matrix of positive determinant. -/
theorem slash_apply_of_det_pos (k : ℤ) (f : ℍ → ℂ) (M : GL (Fin 2) ℝ) (hM : 0 < M.val.det)
    (z : ℍ) : (f ∣[k] M) z = f (M • z) * (M.val.det : ℂ) ^ (k - 1) * denom M z ^ (-k) := by
  have hpos : 0 < ((GeneralLinearGroup.det M : ℝˣ) : ℝ) := by
    rwa [GeneralLinearGroup.val_det_apply]
  rw [ModularForm.slash_def]
  simp only [σ, ite_eq_left hpos, ContinuousAlgEquiv.refl_apply]
  rw [GeneralLinearGroup.val_det_apply, abs_of_pos hM]

theorem scalar_identity (F D den L : ℂ) (hD : D ≠ 0) (hden : den ≠ 0) (e : ℤ) (m : ℕ) :
    F * (D ^ (-e) * (D / den) ^ m * L) * (D / den ^ 2) =
      D ^ (-e) * (F * D ^ ((m : ℤ) + 2 - 1) * den ^ (-((m : ℤ) + 2))) * L := by
  have e1 : D ^ ((m : ℤ) + 2 - 1) = D ^ (m + 1) := by
    rw [show (m : ℤ) + 2 - 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have e2 : den ^ (-((m : ℤ) + 2)) = (den ^ (m + 2))⁻¹ := by
    rw [show -((m : ℤ) + 2) = -((m + 2 : ℕ) : ℤ) by push_cast; ring, _root_.zpow_neg,
      zpow_natCast]
  rw [e1, e2, div_pow]
  first | (field_simp; done) | (field_simp; ring)

/-- **Transformation of the primitive.** For `M` of positive determinant `D`,
`z ↦ ρ(M)⁻¹ P_f(M z)` is a primitive of `D^{-e} (f ∣[m+2] M)`. -/
theorem transform_isPrimitive (e : ℤ) {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (M : GL (Fin 2) ℝ) (hM : 0 < M.val.det) :
    IsPrimitive m (((M.val.det : ℂ) ^ (-e)) • (f ∣[(m : ℤ) + 2] M))
      (fun z => Binary.homogeneousAction m e (complexify M)⁻¹
        (primitive m f ((M • ofComplex z : ℍ) : ℂ))) := by
  intro ℓ z hz
  let upper : ℍ := ⟨z, hz⟩
  let moved : ℍ := M • upper
  have upper_eq : ofComplex z = upper := ofComplex_apply upper
  have transform := (hasStrictDerivAt_smul hM upper).hasDerivAt
  have first := primitive_isPrimitive m hf
    (ℓ.comp (Binary.homogeneousAction m e (complexify M)⁻¹)) moved moved.im_pos
  have moved_eq : (moved : ℂ) = ((M • ofComplex z : ℍ) : ℂ) := by rw [upper_eq]
  rw [moved_eq] at first
  have composed := first.comp z transform
  have hden : denom M z ≠ 0 := denom_ne_zero M upper
  have scalar : (ℓ.comp (Binary.homogeneousAction m e (complexify M)⁻¹))
        (pointForm m f ((M • ofComplex z : ℍ) : ℂ)) * ((M.val.det : ℂ) / denom M z ^ 2) =
        ℓ (pointForm m (((M.val.det : ℂ) ^ (-e)) • (f ∣[(m : ℤ) + 2] M)) z) := by
    rw [← moved_eq]
    simp only [pointForm, LinearMap.comp_apply, map_smul, smul_eq_mul, ofComplex_apply]
    change f moved * ℓ (Binary.homogeneousAction m e (complexify M)⁻¹
      (binaryPointPower m ((M • upper : ℍ) : ℂ))) * _ = _
    rw [action_inv_pointPower m e M hM upper, map_smul, smul_eq_mul, Pi.smul_apply,
      upper_eq, slash_apply_of_det_pos _ _ _ hM, smul_eq_mul]
    have hD : (M.val.det : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    exact scalar_identity _ _ _ _ hD hden e m
  rw [scalar] at composed
  exact composed

/-- **The cocycle relation.** If `det M = 1` and `f ∣[m+2] M = f`, then
`P(M z) = P(M i) + ρ(M) P(z)`. -/
theorem primitive_modular (e : ℤ) {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (M : GL (Fin 2) ℝ) (hdet : M.val.det = 1) (hinv : f ∣[(m : ℤ) + 2] M = f) (z : ℍ) :
    primitive m f ((M • z : ℍ) : ℂ) = primitive m f ((M • I : ℍ) : ℂ) +
      Binary.homogeneousAction m e (complexify M) (primitive m f (z : ℂ)) := by
  have hM : 0 < M.val.det := by rw [hdet]; exact one_pos
  have hprim := transform_isPrimitive m e hf M hM
  rw [hdet, hinv, Complex.ofReal_one, _root_.one_zpow, one_smul] at hprim
  have key := eq_primitive_add m hf _ hprim z z.im_pos
  have hI : ofComplex Complex.I = I := ofComplex_apply I
  simp only [ofComplex_apply, hI] at key
  have := congrArg (Binary.homogeneousAction m e (complexify M)) key
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
    map_add, ← Module.End.mul_apply (Binary.homogeneousAction m e (complexify M)), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply] at this
  rw [this, add_comm]

end TernaryPeriodPolynomials.LevelThree.LevelThreePeriodPrimitive
