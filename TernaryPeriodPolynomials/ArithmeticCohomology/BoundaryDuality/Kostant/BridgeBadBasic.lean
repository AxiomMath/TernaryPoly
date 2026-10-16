module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BridgeLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.BadLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Fiber.ParabolicL0

@[expose] public section


/-!
# Basic facts for the level-three bridge at the bad line

The radical of the stabilizer of the bad line `L₀ = ⟨e₀⟩` in the level is the lattice
`latL0 = {I + x E₀₁ + y E₀₂}`, which is the radical of the semidirect model of the stabilizer; the
Levi group `Γ = Γ₁'(3) ⊆ GL₂(ℤ)` embeds as `diag(1, γ)` (`badLevi`) and conjugates the lattice by
the Levi action `conjAct` of the semidirect model (`badLevi_conj`).  This module collects:

* the identification of `latL0` with the radical embedding (`latL0_hom_eq`);
* the Levi embedding `badLevi`, its values on the generators `upper 1`, `lower 1` (`badLevi_T`,
  `badLevi_L`), its membership in the level and the normalization of the lattice;
* the anti-diagonal negation `swapNegHom` carrying a point `p` of the upper plane radical lattice to
  the point of `latL0` with `φ(u(swapNeg p)) · badFrame = badFrame · planeUnipotent p`
  (`badFrame_conj`);
* the dual Levi element `badDualLevi γ = σ γ^{-T} σ`, the matrix by which `φ(diag(1, γ))` acts on
  the dual radical in the frame `badFrame` (`badFrame_conj_levi`), and the compatibility of the
  lattice actions (`conjAct_swapNeg`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne (GL2Z)

attribute [local instance] TernaryPeriodPolynomials.SphericalDetection.Helpers.complexEndRationalAlgebra

namespace TernaryPeriodPolynomials.BoundaryDuality.Kostant

open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₀ uL0 zuL0 zuL0_val embedZ embedZ_apply zT zT_val zL zL_val)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators
  (upper lower)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)

/-! ### The radical lattice of the bad line -/

/-- The entries of an integral element viewed over `ℚ`. -/
theorem integralRational_apply (z : IntegralGL3) (i j : Fin 3) :
    (integralRational z).val i j = ((z.val i j : ℤ) : ℚ) := rfl

/-- The lattice of the bad line is the line radical. -/
theorem uL0_eq_lineUnipotent (x y : ℤ) : uL0 x y = lineUnipotent (x : ℚ) (y : ℚ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uL0, embedZ_apply, zuL0_val, lineUnipotent, upperUnipotent]

/-- The parametrization of the lattice `latL0` is the radical embedding of the semidirect model. -/
theorem latL0_hom_eq : latL0.hom = integralRadicalRationalHom := by
  apply MonoidHom.ext
  intro p
  change uL0 p.toAdd.1 p.toAdd.2 =
    integralRational (lineUnipotent p.toAdd.1 p.toAdd.2)
  rw [uL0_eq_lineUnipotent]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralRational_apply, lineUnipotent, upperUnipotent]

/-! ### The Levi embedding -/

/-- The Levi embedding `Γ₁'(3) → GL₃(ℚ)`, `γ ↦ diag(1, γ)`. -/
def badLevi : binaryArithmeticLevel →* RationalGL3 :=
  integralRational.comp ((lineLeviHom ℤ).comp (MonoidHom.prod 1 binaryArithmeticLevel.subtype))

theorem badLevi_apply (γ : binaryArithmeticLevel) :
    badLevi γ = integralRational (lineLevi 1 γ.1) := rfl

/-- The matrix of the Levi embedding. -/
theorem badLevi_val_apply (γ : binaryArithmeticLevel) (i j : Fin 3) :
    (badLevi γ).val i j = (((lineLevi 1 γ.1).val i j : ℤ) : ℚ) := rfl

/-- The Levi embedding sends `upper 1` to `T = I + E₁₂`. -/
theorem badLevi_T : badLevi (upper 1) = L2Matrices.T := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [badLevi_val_apply, lineLevi_val, upper, L2Matrices.T, embedZ_apply, zT_val]

/-- The Levi embedding sends `lower 1` to `L = I + 3E₂₁`. -/
theorem badLevi_L : badLevi (lower 1) = L2Matrices.L := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [badLevi_val_apply, lineLevi_val, lower, L2Matrices.L, embedZ_apply, zL_val]

/-- The value of the semidirect model at a radical element. -/
theorem equiv_inl_val (r : Multiplicative (ℤ × ℤ)) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inl r)).val = latL0.hom r := by
  rw [standardBadLineSemidirectEquiv_inl, latL0_hom_eq]
  rfl

/-- The value of the semidirect model at a Levi element. -/
theorem equiv_inr_val (γ : binaryArithmeticLevel) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr ((1 : ℤˣ), γ))).val = badLevi γ := by
  rw [standardBadLineSemidirectEquiv_inr]
  rfl

/-- **The Levi element conjugates the lattice**: `u(r) · k = k · u(conjAct (k⁻¹) r)`. -/
theorem badLevi_conj (γ : binaryArithmeticLevel) (r : Multiplicative (ℤ × ℤ)) :
    latL0.hom r * badLevi γ =
      badLevi γ * latL0.hom (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ r) := by
  have h := semidirect_conjugation_intertwines integralBadLineSplitting.conjAct ((1 : ℤˣ), γ) r
  have h2 := congrArg (fun x => (standardBadLineSemidirectEquiv x).val) h
  simp only [map_mul, Subgroup.coe_mul, equiv_inr_val, equiv_inl_val] at h2
  exact h2.symm

/-- `k⁻¹ u(r) k = u(conjAct (k⁻¹) r)`. -/
theorem badLevi_inv_conj (γ : binaryArithmeticLevel) (r : Multiplicative (ℤ × ℤ)) :
    (badLevi γ)⁻¹ * latL0.hom r * badLevi γ =
      latL0.hom (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ r) := by
  rw [mul_assoc, badLevi_conj, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The inverse Levi element normalizes the lattice. -/
theorem badLevi_inv_normalizes (γ : binaryArithmeticLevel) :
    ∀ u ∈ latL0.sub, (badLevi γ)⁻¹ * u * badLevi γ ∈ latL0.sub := by
  rintro u ⟨r, rfl⟩
  rw [badLevi_inv_conj]
  exact ⟨_, rfl⟩

/-- The Levi embedding lies in the stabilizer of the bad line in the level. -/
theorem badLevi_mem_level (γ : binaryArithmeticLevel) : badLevi γ ∈ levelStabilizer L₀ :=
  integralBadLineStabilizer_rational_mem (integralBadLineLeviSection ((1 : ℤˣ), γ))

/-- The coordinates of the inverse Levi action on the radical. -/
theorem conjAct_inv_coords (γ : binaryArithmeticLevel) (r : Multiplicative (ℤ × ℤ)) :
    (integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ r).toAdd =
      (r.toAdd.1 * γ.1.val 0 0 + r.toAdd.2 * γ.1.val 1 0,
        r.toAdd.1 * γ.1.val 0 1 + r.toAdd.2 * γ.1.val 1 1) := by
  have h := integralBadLine_inverse_conjAct_coordinates ((1 : ℤˣ), γ) r
  have h1 : ((1 : ℤˣ).inv : ℤ) = 1 := rfl
  simpa [h1] using h

/-! ### The dual radical in the frame `badFrame` -/

/-- The anti-diagonal negation `(a, b) ↦ (-b, -a)` of the lattice coordinates. -/
def swapNegHom : RadicalLattice →* Multiplicative (ℤ × ℤ) where
  toFun p := Multiplicative.ofAdd (-p.toAdd.2, -p.toAdd.1)
  map_one' := by
    apply Multiplicative.toAdd.injective
    simp
  map_mul' p q := by
    apply Multiplicative.toAdd.injective
    ext <;> simp <;> ring

theorem swapNegHom_toAdd (p : RadicalLattice) :
    (swapNegHom p).toAdd = (-p.toAdd.2, -p.toAdd.1) := rfl

/-- The lattice element attached to `p` by the anti-diagonal negation. -/
theorem hom_swapNeg (p : RadicalLattice) :
    latL0.hom (swapNegHom p) = lineUnipotent (-(p.toAdd.2 : ℚ)) (-(p.toAdd.1 : ℚ)) := by
  change uL0 (-p.toAdd.2) (-p.toAdd.1) = _
  rw [uL0_eq_lineUnipotent, Int.cast_neg, Int.cast_neg]

/-- **The frame identity for the cocycle coordinates**: the level involution of the lattice element
attached to `p` is conjugate, in the frame `badFrame`, to the element `p` of the upper plane
radical. -/
theorem badFrame_conj (p : RadicalLattice) :
    badFrame⁻¹ * dualInvolution (latL0.hom (swapNegHom p)) * badFrame = upperRadicalLattice p := by
  rw [hom_swapNeg]
  have h := badFrame_identity (-(p.toAdd.2 : ℚ)) (-(p.toAdd.1 : ℚ))
  have hP : planeUnipotent (-(p.toAdd.1 : ℚ)) (-(p.toAdd.2 : ℚ)) *
      planeUnipotent (p.toAdd.1 : ℚ) (p.toAdd.2 : ℚ) = 1 := by
    rw [← GeneralEisenstein.Adelic.planeUnipotent_add, neg_add_cancel, neg_add_cancel]
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [planeUnipotent]
  have h1 := eq_mul_inv_of_mul_eq h
  rw [inv_eq_of_mul_eq_one_right hP] at h1
  have key : badFrame⁻¹ * (dualInvolution (lineUnipotent (-(p.toAdd.2 : ℚ)) (-(p.toAdd.1 : ℚ))) *
      badFrame) = planeUnipotent (p.toAdd.1 : ℚ) (p.toAdd.2 : ℚ) := by
    rw [h1, inv_mul_cancel_left]
  rw [mul_assoc]
  exact key

/-! ### The dual Levi element -/

/-- The matrix `[[0, 1], [1, 0]]` is its own transpose. -/
theorem swapInt_transpose : swapIntᵀ = swapInt := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapInt]

theorem swapInt_mul_self : swapInt * swapInt = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapInt, Matrix.mul_apply, Fin.sum_univ_two]

/-- The exchange matrix as an element of `GL₂(ℤ)`. -/
def swapZ : GL2Z := ⟨swapInt, swapInt, swapInt_mul_self, swapInt_mul_self⟩

/-- **The dual Levi element** `σ γ^{-T} σ`, the matrix by which `φ(diag(1, γ))` acts on the dual
radical in the frame `badFrame`. -/
def badDualLevi (γ : binaryArithmeticLevel) : GL2Z := swapZ * invT γ.1 * swapZ

theorem badDualLevi_val (γ : binaryArithmeticLevel) :
    ((badDualLevi γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
      swapInt * ((γ.1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ * swapInt := by
  rw [badDualLevi, Units.val_mul, Units.val_mul]
  rfl

theorem badDualLevi_inv_val (γ : binaryArithmeticLevel) :
    (((badDualLevi γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) =
      swapInt * ((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ * swapInt := by
  rw [badDualLevi, _root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc]
  rfl

/-- **The Levi relation** `σ γ σ M'ᵀ = 1` for the dual Levi element `M' = σ γ^{-T} σ`. -/
theorem badDualLevi_relation (γ : binaryArithmeticLevel) :
    swapInt * ((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * swapInt *
        ((badDualLevi γ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)ᵀ = 1 := by
  have hS := swapInt_mul_self
  rw [badDualLevi_val, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    swapInt_transpose]
  have e : swapInt * ((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * swapInt *
      (swapInt * (((γ.1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * swapInt)) =
      swapInt * (((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((γ.1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ)) * swapInt := by
    calc _ = swapInt * ((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * (swapInt * swapInt) *
          (((γ.1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * swapInt) := by
          simp only [Matrix.mul_assoc]
      _ = swapInt * ((γ.1 : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * 1 *
          (((γ.1⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) * swapInt) := by rw [hS]
      _ = _ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [e, Units.mul_inv, Matrix.mul_one, hS]

/-- The coordinates of the upper Levi action of the dual Levi element. -/
theorem upperLeviInput_badDual (γ : binaryArithmeticLevel) (p : RadicalLattice) :
    (upperLeviLatticeInput (badDualLevi γ) p).toAdd =
      (γ.1.val 1 1 * p.toAdd.1 + γ.1.val 0 1 * p.toAdd.2,
        γ.1.val 1 0 * p.toAdd.1 + γ.1.val 0 0 * p.toAdd.2) := by
  change ((((badDualLevi γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * p.toAdd.1 +
        (((badDualLevi γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * p.toAdd.2,
      (((badDualLevi γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * p.toAdd.1 +
        (((badDualLevi γ)⁻¹ : GL2Z) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * p.toAdd.2) = _
  rw [badDualLevi_inv_val]
  refine Prod.ext ?_ ?_ <;>
    simp [swapInt, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- **The Levi action on the lattice, in the frame**: the inverse Levi conjugation of the point
attached to `p` is the point attached to the upper Levi translate of `p` by the dual Levi element. -/
theorem conjAct_swapNeg (γ : binaryArithmeticLevel) (p : RadicalLattice) :
    integralBadLineSplitting.conjAct ((1 : ℤˣ), γ)⁻¹ (swapNegHom p) =
      swapNegHom (upperLeviLatticeInput (badDualLevi γ) p) := by
  apply Multiplicative.toAdd.injective
  rw [conjAct_inv_coords, swapNegHom_toAdd, swapNegHom_toAdd, upperLeviInput_badDual]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- **The frame conjugate of the dual of a Levi element is the dual Levi element**:
`badFrame⁻¹ φ(diag(1, γ)) badFrame = diag(σ γ^{-T} σ, 1)`. -/
theorem badFrame_conj_levi (γ : binaryArithmeticLevel) :
    badFrame⁻¹ * dualInvolution (badLevi γ) * badFrame = arithmeticLevi (badDualLevi γ) := by
  have hL : ((levelScale : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 3] := rfl
  have hLi : (((levelScale⁻¹ : RationalGL3)) : Matrix (Fin 3) (Fin 3) ℚ) =
      Matrix.diagonal ![1, 1, 1 / 3] := rfl
  have hinv : (((badLevi γ)⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      ((badLevi γ⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) := by
    rw [map_inv]
  have hF : ((badFrame⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 0, 1 / 3; 0, 1, 0; 1, 0, 0] := rfl
  have hF' : ((badFrame : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 0, 1; 0, 1, 0; 3, 0, 0] := rfl
  apply Units.ext
  rw [dualInvolution_apply, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, hL, hLi, hF,
    hF']
  have hT : ((inverseTranspose (badLevi γ) : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ) =
      ((badLevi γ⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ)ᵀ :=
    congrArg Matrix.transpose hinv
  rw [hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, badLevi_val_apply,
      lineLevi_val, arithmeticLevi, planeLevi, planeBlock, badDualLevi_val, swapInt,
      Fin.sum_univ_two, GeneralLinearGroup.map_apply, Matrix.vecMul, dotProduct, -map_inv]; try ring)

end TernaryPeriodPolynomials.BoundaryDuality.Kostant

end
