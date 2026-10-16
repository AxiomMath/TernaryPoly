module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs

@[expose] public section


/-!
# The level-preserving anti-involution `x ↦ w xᵀ w⁻¹`

With `w = diag(1, 1, 3)`, the map `ι x = w xᵀ w⁻¹` is an involutive
anti-automorphism of `GL₃(ℚ)` which preserves the arithmetic level
`rationalLevel` (integral matrices whose last row is `e₃*` modulo three).
It fixes every diagonal matrix.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- `w = diag(1, 1, 3)`. -/
def wMat : Matrix (Fin 3) (Fin 3) ℚ := diagonal ![1, 1, 3]

/-- `w⁻¹ = diag(1, 1, 1/3)`. -/
def wInv : Matrix (Fin 3) (Fin 3) ℚ := diagonal ![1, 1, 1 / 3]

theorem wInv_mul_wMat : wInv * wMat = 1 := by
  rw [wInv, wMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wMat_mul_wInv : wMat * wInv = 1 := by
  rw [wInv, wMat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem wMat_transpose : wMatᵀ = wMat := diagonal_transpose _
theorem wInv_transpose : wInvᵀ = wInv := diagonal_transpose _

/-- The underlying matrix map. -/
def ιMat (A : Matrix (Fin 3) (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ := wMat * Aᵀ * wInv

theorem ιMat_mul (A B : Matrix (Fin 3) (Fin 3) ℚ) : ιMat (A * B) = ιMat B * ιMat A := by
  simp only [ιMat, transpose_mul]
  calc wMat * (Bᵀ * Aᵀ) * wInv = wMat * Bᵀ * (wInv * wMat) * Aᵀ * wInv := by
        rw [wInv_mul_wMat]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem ιMat_one : ιMat 1 = 1 := by
  simp [ιMat, wMat_mul_wInv]

theorem ιMat_ιMat (A : Matrix (Fin 3) (Fin 3) ℚ) : ιMat (ιMat A) = A := by
  simp only [ιMat, transpose_mul, wMat_transpose, wInv_transpose, transpose_transpose]
  calc wMat * (wInv * (A * wMat)) * wInv = (wMat * wInv) * A * (wMat * wInv) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [wMat_mul_wInv, Matrix.one_mul, Matrix.mul_one]

/-- The anti-involution on `GL₃(ℚ)`. -/
def ι (g : RationalGL3) : RationalGL3 where
  val := ιMat g.val
  inv := ιMat (g⁻¹).val
  val_inv := by rw [← ιMat_mul, Units.inv_mul, ιMat_one]
  inv_val := by rw [← ιMat_mul, Units.mul_inv, ιMat_one]

@[simp] theorem ι_val (g : RationalGL3) : (ι g).val = ιMat g.val := rfl

theorem ι_mul (x y : RationalGL3) : ι (x * y) = ι y * ι x := by
  apply Units.ext
  simp [ιMat_mul]

theorem ι_ι (x : RationalGL3) : ι (ι x) = x := by
  apply Units.ext
  simp [ιMat_ιMat]

theorem ιMat_diagonal (d : Fin 3 → ℚ) : ιMat (diagonal d) = diagonal d := by
  rw [ιMat, diagonal_transpose, wMat, wInv, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem ι_of_diagonal (x : RationalGL3) (d : Fin 3 → ℚ) (hx : x.val = diagonal d) : ι x = x := by
  apply Units.ext
  rw [ι_val, hx, ιMat_diagonal]

/-! ### Integral description of the level -/

/-- Integral matrices with unit determinant and last row `e₃*` modulo three give
elements of the level. -/
theorem mem_rationalLevel_of_int (g : RationalGL3) (M : Matrix (Fin 3) (Fin 3) ℤ)
    (hg : g.val = M.map (Int.cast : ℤ → ℚ)) (hdet : IsUnit M.det)
    (hrow : ∀ j, ((M 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0) : g ∈ rationalLevel := by
  let γ : IntegralGL3 := ⟨M, M⁻¹, Matrix.mul_nonsing_inv M hdet, Matrix.nonsing_inv_mul M hdet⟩
  have hlevel : γ ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree γ).val = lastRow
    have e : ∀ i j, (reductionThree γ).val i j = ((M i j : ℤ) : ZMod 3) := fun _ _ => rfl
    funext j
    simp only [vecMul, dotProduct, lastRow, Fin.sum_univ_three, Pi.single_apply, e]
    have := hrow j
    fin_cases j <;> simp_all
  refine ⟨⟨γ, hlevel⟩, ?_⟩
  apply Units.ext
  rw [hg]
  rfl

/-- Elements of the level are integral with unit determinant and last row `e₃*`. -/
theorem int_of_mem_rationalLevel {g : RationalGL3} (hg : g ∈ rationalLevel) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ, g.val = M.map (Int.cast : ℤ → ℚ) ∧ IsUnit M.det ∧
      ∀ j, ((M 2 j : ℤ) : ZMod 3) = if j = 2 then 1 else 0 := by
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := hg
  refine ⟨γ.val, rfl, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
  · intro j
    have h : lastRow ᵥ* (reductionThree γ).val = lastRow := hγ
    have e : ∀ i j, (reductionThree γ).val i j = ((γ.val i j : ℤ) : ZMod 3) := fun _ _ => rfl
    have hj := congrFun h j
    simp only [vecMul, dotProduct, lastRow, Fin.sum_univ_three, Pi.single_apply, e] at hj
    fin_cases j <;> simp_all

/-- `ι` preserves the level. -/
theorem ι_mem_rationalLevel {g : RationalGL3} (hg : g ∈ rationalLevel) : ι g ∈ rationalLevel := by
  obtain ⟨M, hM, hdet, hrow⟩ := int_of_mem_rationalLevel hg
  have h0 : (3 : ℤ) ∣ M 2 0 := by
    have := hrow 0
    simp only [show (0 : Fin 3) ≠ 2 by decide, ite_false] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
  have h1 : (3 : ℤ) ∣ M 2 1 := by
    have := hrow 1
    simp only [show (1 : Fin 3) ≠ 2 by decide, ite_false] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp this
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  let N : Matrix (Fin 3) (Fin 3) ℤ :=
    !![M 0 0, M 1 0, a; M 0 1, M 1 1, b; 3 * M 0 2, 3 * M 1 2, M 2 2]
  have hN : (ι g).val = N.map (Int.cast : ℤ → ℚ) := by
    rw [ι_val, hM, ιMat, wMat, wInv]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [N, Matrix.mul_apply, diagonal, ha, hb] <;> ring
  have hdetN : N.det = M.det := by
    simp only [N, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]
    rw [ha, hb]
    ring
  refine mem_rationalLevel_of_int (ι g) N hN (hdetN ▸ hdet) ?_
  intro j
  have h22 := hrow 2
  simp only [ite_true] at h22
  fin_cases j <;> simp [N, h22] <;> exact Or.inl (by decide)

end TernaryPeriodPolynomials.HeckeCommutativity
