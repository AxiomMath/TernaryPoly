module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Involution

@[expose] public section


/-!
# The involution preserves the level and exchanges the flag varieties

`dualInvolution` is an involution of `GL₃(ℚ)` mapping the rational image of the arithmetic level
to itself. Composed with the long Weyl element it carries line flags to plane flags, plane flags
to line flags and complete flags to complete flags, equivariantly along `dualInvolution`.
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.Duality

/-- The underlying matrix of the inverse transpose. -/
theorem inverseTranspose_val (g : RationalGL3) :
    (inverseTranspose g).val = (g⁻¹).val.transpose := rfl

/-- The entries of `dualInvolution g` are those of `(g⁻¹)ᵀ` rescaled by `diag(1, 1, 3)`. -/
theorem dualInvolution_val_apply (g : RationalGL3) (i j : Fin 3) :
    (dualInvolution g).val i j = ![1, 1, 3] i * (g⁻¹).val j i * ![1, 1, 1 / 3] j := by
  rw [dualInvolution_apply]
  simp [levelScale, inverseTranspose_val, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The inverse transpose of `diag(1, 1, 3)` is its inverse. -/
theorem inverseTranspose_levelScale : inverseTranspose levelScale = levelScale⁻¹ := by
  apply Units.ext
  simp [inverseTranspose_val, levelScale]

/-- The inverse transpose is an involution. -/
theorem inverseTranspose_involutive (g : RationalGL3) :
    inverseTranspose (inverseTranspose g) = g := by
  apply Units.ext
  rfl

/-- `dualInvolution` is an involution. -/
theorem dualInvolution_involutive (g : RationalGL3) : dualInvolution (dualInvolution g) = g := by
  rw [dualInvolution_apply, dualInvolution_apply, map_mul, map_mul, map_inv,
    inverseTranspose_involutive, inverseTranspose_levelScale]
  group

/-- The integral matrix `diag(1, 1, 3) Nᵀ diag(1, 1, 3)⁻¹`, with exact division by three. -/
def integralDual (N : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![N 0 0, N 1 0, N 2 0 / 3], ![N 0 1, N 1 1, N 2 1 / 3],
    ![3 * N 0 2, 3 * N 1 2, N 2 2]]

/-- Membership in the arithmetic level is the congruence `e₃* γ ≡ e₃*` on the last row. -/
theorem lastRow_congruence {γ : IntegralGL3} (h : γ ∈ arithmeticLevel) :
    ((γ.val 2 0 : ℤ) : ZMod 3) = 0 ∧ ((γ.val 2 1 : ℤ) : ZMod 3) = 0 ∧
      ((γ.val 2 2 : ℤ) : ZMod 3) = 1 := by
  have row : lastRow ᵥ* (reductionThree γ).val = lastRow := h
  have entry (j : Fin 3) := congrFun row j
  refine ⟨?_, ?_, ?_⟩
  · simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry 0
  · simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry 1
  · simpa [lastRow, reductionThree, Matrix.vecMul, dotProduct, Fin.sum_univ_three] using entry 2

/-- On a level element, `dualInvolution` is the cast of `integralDual` of the inverse. -/
theorem dualInvolution_map_val {γ : IntegralGL3} (h : γ ∈ arithmeticLevel) :
    (dualInvolution (GeneralLinearGroup.map (Int.castRingHom ℚ) γ)).val =
      (integralDual (γ⁻¹).val).map (Int.castRingHom ℚ) := by
  obtain ⟨h0, h1, -⟩ := lastRow_congruence (inv_mem h)
  obtain ⟨k0, hk0⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  obtain ⟨k1, hk1⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h1
  have hinv : ((GeneralLinearGroup.map (Int.castRingHom ℚ) γ)⁻¹).val =
      (γ⁻¹).val.map (Int.castRingHom ℚ) := by
    rw [← map_inv]
    rfl
  ext i j
  rw [dualInvolution_val_apply, hinv]
  generalize (γ⁻¹).val = N at hk0 hk1 ⊢
  fin_cases i <;> fin_cases j <;>
    simp [integralDual, hk0, hk1, mul_comm (3 : ℚ)]

/-- On a level element, `integralDual (γ⁻¹)` is inverse to `integralDual γ`. -/
theorem integralDual_mul {γ : IntegralGL3} (h : γ ∈ arithmeticLevel) :
    integralDual (γ⁻¹).val * integralDual γ.val = 1 := by
  apply Matrix.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
  have hval := dualInvolution_map_val h
  have hval' := dualInvolution_map_val (inv_mem h)
  rw [inv_inv] at hval'
  change (integralDual (γ⁻¹).val * integralDual γ.val).map (Int.castRingHom ℚ) =
    (1 : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)
  rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hval, ← hval',
    ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Units.val_one]

/-- The level element `diag(1, 1, 3) (γ⁻¹)ᵀ diag(1, 1, 3)⁻¹` of `GL₃(ℤ)`. -/
def integralDualUnit {γ : IntegralGL3} (h : γ ∈ arithmeticLevel) : IntegralGL3 :=
  ⟨integralDual (γ⁻¹).val, integralDual γ.val, integralDual_mul h, by
    simpa only [inv_inv] using integralDual_mul (inv_mem h)⟩

/-- `integralDualUnit` lies in the arithmetic level. -/
theorem integralDualUnit_mem {γ : IntegralGL3} (h : γ ∈ arithmeticLevel) :
    integralDualUnit h ∈ arithmeticLevel := by
  obtain ⟨-, -, h2⟩ := lastRow_congruence (inv_mem h)
  have three : (3 : ZMod 3) = 0 := rfl
  change lastRow ᵥ* (integralDual (γ⁻¹).val).map (Int.castRingHom (ZMod 3)) = lastRow
  generalize (γ⁻¹).val = N at h2 ⊢
  funext j
  fin_cases j <;>
    simp [lastRow, integralDual, Matrix.vecMul, dotProduct, Fin.sum_univ_three, three, h2]

/-- `dualInvolution` maps the rational image of the arithmetic level to itself. -/
theorem dualInvolution_mem_rationalLevel {g : RationalGL3} (h : g ∈ rationalLevel) :
    dualInvolution g ∈ rationalLevel := by
  obtain ⟨γ, rfl⟩ := h
  refine ⟨⟨integralDualUnit γ.property, integralDualUnit_mem γ.property⟩, ?_⟩
  apply Units.ext
  exact (dualInvolution_map_val γ.property).symm

/-- The antidiagonal permutation matrix exchanging `e₀` and `e₂`. -/
def longWeylMatrix : Matrix (Fin 3) (Fin 3) ℚ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The long Weyl element squares to the identity. -/
theorem longWeylMatrix_mul_self : longWeylMatrix * longWeylMatrix = 1 := by
  rw [longWeylMatrix, Matrix.mul_fin_three, Matrix.one_fin_three]
  norm_num

/-- The long Weyl element of `GL₃(ℚ)`, the antidiagonal permutation matrix. -/
def longWeyl : RationalGL3 :=
  ⟨longWeylMatrix, longWeylMatrix, longWeylMatrix_mul_self, longWeylMatrix_mul_self⟩

/-- Conjugation by the long Weyl element reverses both indices of a matrix. -/
theorem longWeyl_conj_val (X : RationalGL3) (i j : Fin 3) :
    (longWeyl⁻¹ * X * longWeyl).val i j = X.val i.rev j.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [longWeyl, longWeylMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three]

/-- `dualInvolution` followed by the long Weyl conjugation maps the line parabolic into the
plane parabolic. -/
theorem dualInvolution_line {q : RationalGL3} (hq : q ∈ parabolic .line) :
    longWeyl⁻¹ * dualInvolution q * longWeyl ∈ parabolic .plane := by
  obtain ⟨h1, h2⟩ : (q⁻¹).val 1 0 = 0 ∧ (q⁻¹).val 2 0 = 0 := inv_mem hq
  refine ⟨?_, ?_⟩ <;> rw [longWeyl_conj_val, dualInvolution_val_apply]
  · rw [show (0 : Fin 3).rev = 2 from rfl, show (2 : Fin 3).rev = 0 from rfl, h2, mul_zero,
      zero_mul]
  · rw [show (1 : Fin 3).rev = 1 from rfl, show (2 : Fin 3).rev = 0 from rfl, h1, mul_zero,
      zero_mul]

/-- `dualInvolution` followed by the long Weyl conjugation maps the plane parabolic into the
line parabolic. -/
theorem dualInvolution_plane {q : RationalGL3} (hq : q ∈ parabolic .plane) :
    longWeyl⁻¹ * dualInvolution q * longWeyl ∈ parabolic .line := by
  obtain ⟨h0, h1⟩ : (q⁻¹).val 2 0 = 0 ∧ (q⁻¹).val 2 1 = 0 := inv_mem hq
  refine ⟨?_, ?_⟩ <;> rw [longWeyl_conj_val, dualInvolution_val_apply]
  · rw [show (1 : Fin 3).rev = 1 from rfl, show (0 : Fin 3).rev = 2 from rfl, h1, mul_zero,
      zero_mul]
  · rw [show (2 : Fin 3).rev = 0 from rfl, show (0 : Fin 3).rev = 2 from rfl, h0, mul_zero,
      zero_mul]

/-- `dualInvolution` followed by the long Weyl conjugation maps the Borel subgroup to itself. -/
theorem dualInvolution_borel {q : RationalGL3}
    (hq : q ∈ parabolic .plane ⊓ parabolic .line) :
    longWeyl⁻¹ * dualInvolution q * longWeyl ∈ parabolic .plane ⊓ parabolic .line :=
  ⟨dualInvolution_line hq.2, dualInvolution_plane hq.1⟩

/-- The relative position of two twisted images is the twisted image of the relative position. -/
theorem dualInvolution_relative (a b : RationalGL3) :
    (dualInvolution a * longWeyl)⁻¹ * (dualInvolution b * longWeyl) =
      longWeyl⁻¹ * dualInvolution (a⁻¹ * b) * longWeyl := by
  rw [map_mul, map_inv]
  group

/-- The map from line flags to plane flags induced by `g ↦ dualInvolution g * longWeyl`. -/
def dualFlag : Flags .line → Flags .plane :=
  Quotient.map' (fun g => dualInvolution g * longWeyl) fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [dualInvolution_relative]
    exact dualInvolution_line h

/-- The map from plane flags to line flags induced by `g ↦ dualInvolution g * longWeyl`. -/
def dualPlaneFlag : Flags .plane → Flags .line :=
  Quotient.map' (fun g => dualInvolution g * longWeyl) fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [dualInvolution_relative]
    exact dualInvolution_plane h

/-- The map on complete flags induced by `g ↦ dualInvolution g * longWeyl`. -/
def dualEdge : Edges → Edges :=
  Quotient.map' (fun g => dualInvolution g * longWeyl) fun a b h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    rw [dualInvolution_relative]
    exact dualInvolution_borel h

/-- `dualFlag` on the class of `g`. -/
theorem dualFlag_mk (g : RationalGL3) :
    dualFlag (QuotientGroup.mk g) = QuotientGroup.mk (dualInvolution g * longWeyl) := rfl

/-- `dualPlaneFlag` on the class of `g`. -/
theorem dualPlaneFlag_mk (g : RationalGL3) :
    dualPlaneFlag (QuotientGroup.mk g) = QuotientGroup.mk (dualInvolution g * longWeyl) := rfl

/-- `dualEdge` on the class of `g`. -/
theorem dualEdge_mk (g : RationalGL3) :
    dualEdge (QuotientGroup.mk g) = QuotientGroup.mk (dualInvolution g * longWeyl) := rfl

/-- `dualFlag` is equivariant along `dualInvolution`. -/
theorem dualFlag_smul (g : RationalGL3) (F : Flags .line) :
    dualFlag (g • F) = dualInvolution g • dualFlag F := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective F
  rw [MulAction.Quotient.smul_mk, dualFlag_mk, dualFlag_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul, mul_assoc]

/-- `dualPlaneFlag` is equivariant along `dualInvolution`. -/
theorem dualPlaneFlag_smul (g : RationalGL3) (F : Flags .plane) :
    dualPlaneFlag (g • F) = dualInvolution g • dualPlaneFlag F := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective F
  rw [MulAction.Quotient.smul_mk, dualPlaneFlag_mk, dualPlaneFlag_mk,
    MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, map_mul, mul_assoc]

/-- `dualEdge` is equivariant along `dualInvolution`. -/
theorem dualEdge_smul (g : RationalGL3) (e : Edges) :
    dualEdge (g • e) = dualInvolution g • dualEdge e := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rw [MulAction.Quotient.smul_mk, dualEdge_mk, dualEdge_mk, MulAction.Quotient.smul_mk,
    smul_eq_mul, smul_eq_mul, map_mul, mul_assoc]

/-- The plane endpoint of the dual complete flag is the dual of its line endpoint. -/
theorem endpoint_plane_dualEdge (e : Edges) :
    endpoint .plane (dualEdge e) = dualFlag (endpoint .line e) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rfl

/-- The line endpoint of the dual complete flag is the dual of its plane endpoint. -/
theorem endpoint_line_dualEdge (e : Edges) :
    endpoint .line (dualEdge e) = dualPlaneFlag (endpoint .plane e) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective e
  rfl

end TernaryPeriodPolynomials.Duality
