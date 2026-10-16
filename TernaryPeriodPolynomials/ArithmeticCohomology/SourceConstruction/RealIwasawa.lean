module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


/-!
# The analytic Iwasawa decomposition of `GL₃(ℝ)`

Every `g ∈ GL₃(ℝ)` factors uniquely as `g = b · κ` with `b` upper triangular with positive diagonal
and `κ` orthogonal. The factors are computed by Gram–Schmidt on the rows of `g`, starting from the
last row, and depend real-analytically on `g` (the only non-algebraic operation is a square root of a
positive quantity). The factorization is equivariant for the parabolic subgroups containing the
upper triangular group: for `p` in the line or plane parabolic, `κ(p g) = m κ(g)` with `m` an
orthogonal element of the same parabolic, which is block diagonal.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

open TernaryPeriodPolynomials.SphericalDetection.Helpers

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-! ### The two factor classes -/

/-- Upper triangular with positive diagonal. -/
def IsUpperPositive (b : RealGL3) : Prop :=
  b.val 1 0 = 0 ∧ b.val 2 0 = 0 ∧ b.val 2 1 = 0 ∧ 0 < b.val 0 0 ∧ 0 < b.val 1 1 ∧ 0 < b.val 2 2

/-- Real orthogonal: `kᵀ k = 1`. -/
def IsOrthogonalReal (k : RealGL3) : Prop := k.val.transpose * k.val = 1

theorem IsOrthogonalReal.rows {k : RealGL3} (hk : IsOrthogonalReal k) :
    k.val * k.val.transpose = 1 := by
  have h : k.val.transpose * k.val = 1 := hk
  exact mul_eq_one_comm.mp h

theorem IsOrthogonalReal.mul {k₁ k₂ : RealGL3} (h₁ : IsOrthogonalReal k₁)
    (h₂ : IsOrthogonalReal k₂) : IsOrthogonalReal (k₁ * k₂) := by
  have h₁' : k₁.val.transpose * k₁.val = 1 := h₁
  have h₂' : k₂.val.transpose * k₂.val = 1 := h₂
  change (k₁.val * k₂.val).transpose * (k₁.val * k₂.val) = 1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc k₁.val.transpose, h₁',
    Matrix.one_mul, h₂']

theorem isOrthogonalReal_one : IsOrthogonalReal 1 := by
  change (1 : RealGL3).val.transpose * (1 : RealGL3).val = 1
  simp

theorem isUpperPositive_one : IsUpperPositive (1 : RealGL3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem det_ne_zero_realGL3 (g : RealGL3) : g.val.det ≠ 0 := GeneralLinearGroup.det_ne_zero g

/-! ### Elementary real-variable lemmas -/

theorem iwPos_eq_of_sq_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 = y ^ 2) : x = y := by
  have h' : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · linarith
  · exfalso
    linarith

theorem iwEq_of_mul_eq {x y z : ℝ} (hz : 0 < z) (h : (x - y) * z = 0) : x = y := by
  rcases mul_eq_zero.mp h with h' | h'
  · linarith
  · exfalso
    linarith

theorem iwSq_eq_zero {x : ℝ} (h : x ^ 2 = 0) : x = 0 := by
  by_contra hne
  exact pow_ne_zero 2 hne h

/-! ### Uniqueness: a Cholesky-type argument -/

/-- If two upper triangular matrices with positive diagonal have the same Gram matrix `b bᵀ`, they
are equal. -/
theorem iwUpper_gram_unique {b c : Mat3}
    (hb10 : b 1 0 = 0) (hb20 : b 2 0 = 0) (hb21 : b 2 1 = 0)
    (hc10 : c 1 0 = 0) (hc20 : c 2 0 = 0) (hc21 : c 2 1 = 0)
    (hb00 : 0 < b 0 0) (hb11 : 0 < b 1 1) (hb22 : 0 < b 2 2)
    (hc00 : 0 < c 0 0) (hc11 : 0 < c 1 1) (hc22 : 0 < c 2 2)
    (h : b * b.transpose = c * c.transpose) : b = c := by
  have e : ∀ i j, (b * b.transpose) i j = (c * c.transpose) i j := fun i j => by rw [h]
  have e22 := e 2 2
  have e12 := e 1 2
  have e11 := e 1 1
  have e02 := e 0 2
  have e01 := e 0 1
  have e00 := e 0 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, hb10, hb20, hb21,
    hc10, hc20, hc21, mul_zero, add_zero, zero_add] at e22 e12 e11 e02 e01 e00
  have k22 : b 2 2 = c 2 2 := iwPos_eq_of_sq_eq hb22 hc22 (by linear_combination e22)
  have k12 : b 1 2 = c 1 2 :=
    iwEq_of_mul_eq hc22 (by linear_combination e12 - b 1 2 * k22)
  have k11 : b 1 1 = c 1 1 :=
    iwPos_eq_of_sq_eq hb11 hc11 (by linear_combination e11 - (b 1 2 + c 1 2) * k12)
  have k02 : b 0 2 = c 0 2 :=
    iwEq_of_mul_eq hc22 (by linear_combination e02 - b 0 2 * k22)
  have k01 : b 0 1 = c 0 1 :=
    iwEq_of_mul_eq hc11
      (by linear_combination e01 - b 0 1 * k11 - b 0 2 * k12 - c 1 2 * k02)
  have k00 : b 0 0 = c 0 0 :=
    iwPos_eq_of_sq_eq hb00 hc00
      (by linear_combination e00 - (b 0 1 + c 0 1) * k01 - (b 0 2 + c 0 2) * k02)
  ext i j
  fin_cases i <;> fin_cases j
  · exact k00
  · exact k01
  · exact k02
  · exact hb10.trans hc10.symm
  · exact k11
  · exact k12
  · exact hb20.trans hc20.symm
  · exact hb21.trans hc21.symm
  · exact k22

/-- **Uniqueness of the Iwasawa decomposition.** -/
theorem iwasawa_unique {b b' k k' : RealGL3} (hb : IsUpperPositive b) (hb' : IsUpperPositive b')
    (hk : IsOrthogonalReal k) (hk' : IsOrthogonalReal k') (h : b * k = b' * k') :
    b = b' ∧ k = k' := by
  obtain ⟨hb10, hb20, hb21, hb00, hb11, hb22⟩ := hb
  obtain ⟨hb'10, hb'20, hb'21, hb'00, hb'11, hb'22⟩ := hb'
  have hv : b.val * k.val = b'.val * k'.val := by
    have := congrArg Units.val h
    simpa using this
  have hk1 : k.val * k.val.transpose = 1 := IsOrthogonalReal.rows hk
  have hk2 : k'.val * k'.val.transpose = 1 := IsOrthogonalReal.rows hk'
  have hgram : b.val * b.val.transpose = b'.val * b'.val.transpose := by
    calc b.val * b.val.transpose
        = b.val * (k.val * k.val.transpose) * b.val.transpose := by rw [hk1, Matrix.mul_one]
      _ = (b.val * k.val) * (b.val * k.val).transpose := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (b'.val * k'.val) * (b'.val * k'.val).transpose := by rw [hv]
      _ = b'.val * (k'.val * k'.val.transpose) * b'.val.transpose := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = b'.val * b'.val.transpose := by rw [hk2, Matrix.mul_one]
  have hbb : b.val = b'.val :=
    iwUpper_gram_unique hb10 hb20 hb21 hb'10 hb'20 hb'21 hb00 hb11 hb22 hb'00 hb'11 hb'22 hgram
  have hbeq : b = b' := Units.ext hbb
  subst hbeq
  exact ⟨rfl, mul_left_cancel h⟩

/-! ### Vectors in `ℝ³` and Gram–Schmidt -/

/-- The standard dot product on `ℝ³`. -/
def iwDot (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The Euclidean norm on `ℝ³`. -/
def iwNorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (iwDot v v)

/-- The normalization `v / ‖v‖`. -/
def iwUnit (v : Fin 3 → ℝ) : Fin 3 → ℝ := (iwNorm v)⁻¹ • v

theorem iwDot_comm (u v : Fin 3 → ℝ) : iwDot u v = iwDot v u := by
  unfold iwDot
  ring

theorem iwDot_smul_left (c : ℝ) (u v : Fin 3 → ℝ) : iwDot (c • u) v = c * iwDot u v := by
  simp only [iwDot, Pi.smul_apply, smul_eq_mul]
  ring

theorem iwDot_sub_left (u w v : Fin 3 → ℝ) : iwDot (u - w) v = iwDot u v - iwDot w v := by
  simp only [iwDot, Pi.sub_apply]
  ring

theorem iwDot_smul_smul (c : ℝ) (u v : Fin 3 → ℝ) :
    iwDot (c • u) (c • v) = c ^ 2 * iwDot u v := by
  simp only [iwDot, Pi.smul_apply, smul_eq_mul]
  ring

theorem iwDot_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ iwDot v v := by
  unfold iwDot
  have h0 := mul_self_nonneg (v 0)
  have h1 := mul_self_nonneg (v 1)
  have h2 := mul_self_nonneg (v 2)
  linarith

theorem iwDot_self_eq_zero (v : Fin 3 → ℝ) (h : iwDot v v = 0) : ∀ j, v j = 0 := by
  unfold iwDot at h
  have h0 : v 0 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  intro j
  fin_cases j
  · exact iwSq_eq_zero h0
  · exact iwSq_eq_zero h1
  · exact iwSq_eq_zero h2

theorem iwNorm_pos {v : Fin 3 → ℝ} (h : 0 < iwDot v v) : 0 < iwNorm v :=
  Real.sqrt_pos.mpr h

theorem iwDot_unit_self {v : Fin 3 → ℝ} (h : 0 < iwDot v v) :
    iwDot (iwUnit v) (iwUnit v) = 1 := by
  have hn : iwNorm v ≠ 0 := (iwNorm_pos h).ne'
  have hs : iwNorm v ^ 2 = iwDot v v := Real.sq_sqrt h.le
  unfold iwUnit
  rw [iwDot_smul_smul, ← hs]
  rw [← mul_pow, inv_mul_cancel₀ hn, one_pow]

theorem iwNorm_mul_unit {v : Fin 3 → ℝ} (h : iwNorm v ≠ 0) (j : Fin 3) :
    iwNorm v * iwUnit v j = v j := by
  show iwNorm v * ((iwNorm v)⁻¹ * v j) = v j
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

theorem iwDot_unit_orth {v w : Fin 3 → ℝ} (h : iwDot v w = 0) : iwDot (iwUnit v) w = 0 := by
  unfold iwUnit
  rw [iwDot_smul_left, h, mul_zero]

theorem iwDot_residual (r u : Fin 3 → ℝ) (hu : iwDot u u = 1) :
    iwDot (r - iwDot r u • u) u = 0 := by
  rw [iwDot_sub_left, iwDot_smul_left, hu]
  ring

theorem iwDot_residual2 (r u w : Fin 3 → ℝ) (hu : iwDot u u = 1) (hw : iwDot w w = 1)
    (huw : iwDot u w = 0) :
    iwDot (r - iwDot r u • u - iwDot r w • w) u = 0 ∧
      iwDot (r - iwDot r u • u - iwDot r w • w) w = 0 := by
  have hwu : iwDot w u = 0 := by
    rw [iwDot_comm]
    exact huw
  constructor
  · simp only [iwDot_sub_left, iwDot_smul_left, hu, hwu]
    ring
  · simp only [iwDot_sub_left, iwDot_smul_left, hw, huw]
    ring

/-! ### The Gram–Schmidt data of a matrix, rows from the last -/

/-- The last orthonormal row `κ₂ = r₂ / ‖r₂‖`. -/
def iwK2 (A : Mat3) : Fin 3 → ℝ := iwUnit (A 2)

/-- `b₁₂ = ⟨r₁, κ₂⟩`. -/
def iwB12 (A : Mat3) : ℝ := iwDot (A 1) (iwK2 A)

/-- The residual `r₁ - b₁₂ κ₂`. -/
def iwV1 (A : Mat3) : Fin 3 → ℝ := A 1 - iwB12 A • iwK2 A

/-- The middle orthonormal row. -/
def iwK1 (A : Mat3) : Fin 3 → ℝ := iwUnit (iwV1 A)

/-- `b₀₁ = ⟨r₀, κ₁⟩`. -/
def iwB01 (A : Mat3) : ℝ := iwDot (A 0) (iwK1 A)

/-- `b₀₂ = ⟨r₀, κ₂⟩`. -/
def iwB02 (A : Mat3) : ℝ := iwDot (A 0) (iwK2 A)

/-- The residual `r₀ - b₀₁ κ₁ - b₀₂ κ₂`. -/
def iwV0 (A : Mat3) : Fin 3 → ℝ := A 0 - iwB01 A • iwK1 A - iwB02 A • iwK2 A

/-- The first orthonormal row. -/
def iwK0 (A : Mat3) : Fin 3 → ℝ := iwUnit (iwV0 A)

theorem iwK2_apply (A : Mat3) (j : Fin 3) : iwK2 A j = (iwNorm (A 2))⁻¹ * A 2 j := rfl

theorem iwV1_apply (A : Mat3) (j : Fin 3) : iwV1 A j = A 1 j - iwB12 A * iwK2 A j := rfl

theorem iwK1_apply (A : Mat3) (j : Fin 3) :
    iwK1 A j = (iwNorm (iwV1 A))⁻¹ * iwV1 A j := rfl

theorem iwV0_apply (A : Mat3) (j : Fin 3) :
    iwV0 A j = A 0 j - iwB01 A * iwK1 A j - iwB02 A * iwK2 A j := rfl

/-- The Gram–Schmidt rotation factor, as a matrix (rows `κ₀, κ₁, κ₂`). -/
def iwasawaKMatrix (A : Mat3) : Mat3 := Matrix.of ![iwK0 A, iwK1 A, iwK2 A]

/-- The Gram–Schmidt upper triangular factor, as a matrix. -/
def iwasawaBMatrix (A : Mat3) : Mat3 :=
  !![iwNorm (iwV0 A), iwB01 A, iwB02 A;
    0, iwNorm (iwV1 A), iwB12 A;
    0, 0, iwNorm (A 2)]

/-! ### Determinant and positivity -/

theorem iwDet_row2 (A : Mat3) (h0 : A 2 0 = 0) (h1 : A 2 1 = 0) (h2 : A 2 2 = 0) :
    A.det = 0 := by
  rw [Matrix.det_fin_three, h0, h1, h2]
  ring

theorem iwDet_dep1 (A : Mat3) (c : ℝ) (h : ∀ j, A 1 j = c * A 2 j) : A.det = 0 := by
  rw [Matrix.det_fin_three, h 0, h 1, h 2]
  ring

theorem iwDet_dep2 (A : Mat3) (c d : ℝ) (h : ∀ j, A 0 j = c * A 1 j + d * A 2 j) :
    A.det = 0 := by
  rw [Matrix.det_fin_three, h 0, h 1, h 2]
  ring

theorem iwRow2_pos (A : Mat3) (hA : A.det ≠ 0) : 0 < iwDot (A 2) (A 2) := by
  rcases (iwDot_self_nonneg (A 2)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := iwDot_self_eq_zero (A 2) h.symm
    exact hA (iwDet_row2 A (hz 0) (hz 1) (hz 2))

theorem iwV1_pos (A : Mat3) (hA : A.det ≠ 0) : 0 < iwDot (iwV1 A) (iwV1 A) := by
  rcases (iwDot_self_nonneg (iwV1 A)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := iwDot_self_eq_zero (iwV1 A) h.symm
    refine hA (iwDet_dep1 A (iwB12 A * (iwNorm (A 2))⁻¹) fun j => ?_)
    have hj := hz j
    rw [iwV1_apply, iwK2_apply] at hj
    linear_combination hj

theorem iwV0_pos (A : Mat3) (hA : A.det ≠ 0) : 0 < iwDot (iwV0 A) (iwV0 A) := by
  rcases (iwDot_self_nonneg (iwV0 A)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := iwDot_self_eq_zero (iwV0 A) h.symm
    refine hA (iwDet_dep2 A (iwB01 A * (iwNorm (iwV1 A))⁻¹)
      (iwB02 A * (iwNorm (A 2))⁻¹ - iwB01 A * (iwNorm (iwV1 A))⁻¹ * iwB12 A * (iwNorm (A 2))⁻¹)
      fun j => ?_)
    have hj := hz j
    rw [iwV0_apply, iwK1_apply, iwV1_apply, iwK2_apply] at hj
    linear_combination hj

/-! ### Orthonormality of the rows `κ₀, κ₁, κ₂` -/

theorem iwK2_K2 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK2 A) (iwK2 A) = 1 :=
  iwDot_unit_self (iwRow2_pos A hA)

theorem iwK1_K1 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK1 A) (iwK1 A) = 1 :=
  iwDot_unit_self (iwV1_pos A hA)

theorem iwK0_K0 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK0 A) (iwK0 A) = 1 :=
  iwDot_unit_self (iwV0_pos A hA)

theorem iwV1_K2 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwV1 A) (iwK2 A) = 0 :=
  iwDot_residual (A 1) (iwK2 A) (iwK2_K2 A hA)

theorem iwK1_K2 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK1 A) (iwK2 A) = 0 :=
  iwDot_unit_orth (iwV1_K2 A hA)

theorem iwV0_K1_K2 (A : Mat3) (hA : A.det ≠ 0) :
    iwDot (iwV0 A) (iwK1 A) = 0 ∧ iwDot (iwV0 A) (iwK2 A) = 0 :=
  iwDot_residual2 (A 0) (iwK1 A) (iwK2 A) (iwK1_K1 A hA) (iwK2_K2 A hA) (iwK1_K2 A hA)

theorem iwK0_K1 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK0 A) (iwK1 A) = 0 :=
  iwDot_unit_orth (iwV0_K1_K2 A hA).1

theorem iwK0_K2 (A : Mat3) (hA : A.det ≠ 0) : iwDot (iwK0 A) (iwK2 A) = 0 :=
  iwDot_unit_orth (iwV0_K1_K2 A hA).2

theorem iwasawaKMatrix_mul_transpose (A : Mat3) (hA : A.det ≠ 0) :
    iwasawaKMatrix A * (iwasawaKMatrix A).transpose = 1 := by
  have h00 : iwK0 A 0 * iwK0 A 0 + iwK0 A 1 * iwK0 A 1 + iwK0 A 2 * iwK0 A 2 = 1 :=
    iwK0_K0 A hA
  have h11 : iwK1 A 0 * iwK1 A 0 + iwK1 A 1 * iwK1 A 1 + iwK1 A 2 * iwK1 A 2 = 1 :=
    iwK1_K1 A hA
  have h22 : iwK2 A 0 * iwK2 A 0 + iwK2 A 1 * iwK2 A 1 + iwK2 A 2 * iwK2 A 2 = 1 :=
    iwK2_K2 A hA
  have h01 : iwK0 A 0 * iwK1 A 0 + iwK0 A 1 * iwK1 A 1 + iwK0 A 2 * iwK1 A 2 = 0 :=
    iwK0_K1 A hA
  have h02 : iwK0 A 0 * iwK2 A 0 + iwK0 A 1 * iwK2 A 1 + iwK0 A 2 * iwK2 A 2 = 0 :=
    iwK0_K2 A hA
  have h12 : iwK1 A 0 * iwK2 A 0 + iwK1 A 1 * iwK2 A 1 + iwK1 A 2 * iwK2 A 2 = 0 :=
    iwK1_K2 A hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iwasawaKMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linarith

theorem iwasawaKMatrix_transpose_mul (A : Mat3) (hA : A.det ≠ 0) :
    (iwasawaKMatrix A).transpose * iwasawaKMatrix A = 1 :=
  mul_eq_one_comm.mp (iwasawaKMatrix_mul_transpose A hA)

/-! ### The factorization `A = B K` -/

theorem iwRowEq2 (A : Mat3) (hA : A.det ≠ 0) (j : Fin 3) :
    iwNorm (A 2) * iwK2 A j = A 2 j :=
  iwNorm_mul_unit (iwNorm_pos (iwRow2_pos A hA)).ne' j

theorem iwRowEq1 (A : Mat3) (hA : A.det ≠ 0) (j : Fin 3) :
    iwNorm (iwV1 A) * iwK1 A j + iwB12 A * iwK2 A j = A 1 j := by
  have h : iwNorm (iwV1 A) * iwK1 A j = iwV1 A j :=
    iwNorm_mul_unit (iwNorm_pos (iwV1_pos A hA)).ne' j
  have h' := iwV1_apply A j
  linarith

theorem iwRowEq0 (A : Mat3) (hA : A.det ≠ 0) (j : Fin 3) :
    iwNorm (iwV0 A) * iwK0 A j + iwB01 A * iwK1 A j + iwB02 A * iwK2 A j = A 0 j := by
  have h : iwNorm (iwV0 A) * iwK0 A j = iwV0 A j :=
    iwNorm_mul_unit (iwNorm_pos (iwV0_pos A hA)).ne' j
  have h' := iwV0_apply A j
  linarith

theorem iwasawaBMatrix_mul_iwasawaKMatrix (A : Mat3) (hA : A.det ≠ 0) :
    iwasawaBMatrix A * iwasawaKMatrix A = A := by
  ext i j
  have r0 := iwRowEq0 A hA j
  have r1 := iwRowEq1 A hA j
  have r2 := iwRowEq2 A hA j
  fin_cases i <;>
    simp [iwasawaBMatrix, iwasawaKMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linarith

theorem iwasawaBMatrix_eq_mul_transpose (A : Mat3) (hA : A.det ≠ 0) :
    iwasawaBMatrix A = A * (iwasawaKMatrix A).transpose := by
  calc iwasawaBMatrix A
      = (iwasawaBMatrix A * iwasawaKMatrix A) * (iwasawaKMatrix A).transpose := by
        rw [Matrix.mul_assoc, iwasawaKMatrix_mul_transpose A hA, Matrix.mul_one]
    _ = A * (iwasawaKMatrix A).transpose := by
        rw [iwasawaBMatrix_mul_iwasawaKMatrix A hA]

theorem iwasawaBMatrix_00 (A : Mat3) : iwasawaBMatrix A 0 0 = iwNorm (iwV0 A) := by
  simp [iwasawaBMatrix]

theorem iwasawaBMatrix_11 (A : Mat3) : iwasawaBMatrix A 1 1 = iwNorm (iwV1 A) := by
  simp [iwasawaBMatrix]

theorem iwasawaBMatrix_22 (A : Mat3) : iwasawaBMatrix A 2 2 = iwNorm (A 2) := by
  simp [iwasawaBMatrix]

theorem iwasawaBMatrix_10 (A : Mat3) : iwasawaBMatrix A 1 0 = 0 := by
  simp [iwasawaBMatrix]

theorem iwasawaBMatrix_20 (A : Mat3) : iwasawaBMatrix A 2 0 = 0 := by
  simp [iwasawaBMatrix]

theorem iwasawaBMatrix_21 (A : Mat3) : iwasawaBMatrix A 2 1 = 0 := by
  simp [iwasawaBMatrix]

/-! ### The group-level factors -/

/-- The orthogonal Iwasawa factor `κ(g)`. -/
def iwasawaK (g : RealGL3) : RealGL3 :=
  ⟨iwasawaKMatrix g.val, (iwasawaKMatrix g.val).transpose,
    iwasawaKMatrix_mul_transpose g.val (det_ne_zero_realGL3 g),
    iwasawaKMatrix_transpose_mul g.val (det_ne_zero_realGL3 g)⟩

/-- The upper triangular Iwasawa factor `b(g) = g κ(g)⁻¹`. -/
def iwasawaB (g : RealGL3) : RealGL3 := g * (iwasawaK g)⁻¹

theorem iwasawaK_val (g : RealGL3) : (iwasawaK g).val = iwasawaKMatrix g.val := rfl

theorem iwasawaB_val (g : RealGL3) : (iwasawaB g).val = iwasawaBMatrix g.val := by
  have e : (iwasawaB g).val = g.val * (iwasawaKMatrix g.val).transpose := rfl
  rw [e]
  exact (iwasawaBMatrix_eq_mul_transpose g.val (det_ne_zero_realGL3 g)).symm

theorem iwasawaB_mul_iwasawaK (g : RealGL3) : iwasawaB g * iwasawaK g = g := by
  unfold iwasawaB
  exact inv_mul_cancel_right g (iwasawaK g)

theorem iwasawaB_upper (g : RealGL3) : IsUpperPositive (iwasawaB g) := by
  have hA := det_ne_zero_realGL3 g
  unfold IsUpperPositive
  rw [iwasawaB_val]
  refine ⟨iwasawaBMatrix_10 _, iwasawaBMatrix_20 _, iwasawaBMatrix_21 _, ?_, ?_, ?_⟩
  · rw [iwasawaBMatrix_00]
    exact iwNorm_pos (iwV0_pos _ hA)
  · rw [iwasawaBMatrix_11]
    exact iwNorm_pos (iwV1_pos _ hA)
  · rw [iwasawaBMatrix_22]
    exact iwNorm_pos (iwRow2_pos _ hA)

theorem iwasawaK_orthogonal (g : RealGL3) : IsOrthogonalReal (iwasawaK g) :=
  iwasawaKMatrix_transpose_mul g.val (det_ne_zero_realGL3 g)

/-! ### Consequences of uniqueness -/

theorem iwasawa_eq {b k : RealGL3} (hb : IsUpperPositive b) (hk : IsOrthogonalReal k) :
    iwasawaB (b * k) = b ∧ iwasawaK (b * k) = k :=
  iwasawa_unique (iwasawaB_upper (b * k)) hb (iwasawaK_orthogonal (b * k)) hk
    (iwasawaB_mul_iwasawaK (b * k))

theorem iwasawaB_one : iwasawaB 1 = 1 := by
  have h := (iwasawa_eq isUpperPositive_one isOrthogonalReal_one).1
  rwa [mul_one] at h

theorem iwasawaK_one : iwasawaK 1 = 1 := by
  have h := (iwasawa_eq isUpperPositive_one isOrthogonalReal_one).2
  rwa [mul_one] at h

theorem iwasawaK_mul_orth (g : RealGL3) {k : RealGL3} (hk : IsOrthogonalReal k) :
    iwasawaK (g * k) = iwasawaK g * k := by
  have e : g * k = iwasawaB g * (iwasawaK g * k) := by
    rw [← mul_assoc, iwasawaB_mul_iwasawaK]
  have h := (iwasawa_eq (iwasawaB_upper g) ((iwasawaK_orthogonal g).mul hk)).2
  rw [e]
  exact h

theorem iwasawaB_mul_orth (g : RealGL3) {k : RealGL3} (hk : IsOrthogonalReal k) :
    iwasawaB (g * k) = iwasawaB g := by
  have e : g * k = iwasawaB g * (iwasawaK g * k) := by
    rw [← mul_assoc, iwasawaB_mul_iwasawaK]
  have h := (iwasawa_eq (iwasawaB_upper g) ((iwasawaK_orthogonal g).mul hk)).1
  rw [e]
  exact h

/-! ### Parabolic equivariance -/

theorem iwSubgroup_mem_of_mul_eq {G : Type*} [Group G] (P : Subgroup G) {x y z : G}
    (hx : x ∈ P) (hz : z ∈ P) (h : x * y = z) : y ∈ P := by
  have hy : y = x⁻¹ * z := by rw [← h, inv_mul_cancel_left]
  rw [hy]
  exact P.mul_mem (P.inv_mem hx) hz

theorem iwInv_form {G : Type*} [Group G] {B m c : G} (h : B * m = c) : B = c * m⁻¹ := by
  rw [← h, mul_inv_cancel_right]

/-- Equivariance of the Iwasawa decomposition for any subgroup containing the upper triangular
matrices with positive diagonal. -/
theorem iwasawa_parabolic_of_upper {P : Subgroup RealGL3}
    (hB : ∀ b : RealGL3, IsUpperPositive b → b ∈ P) {p : RealGL3} (hp : p ∈ P) (g : RealGL3) :
    ∃ m : RealGL3, m ∈ P ∧ IsOrthogonalReal m ∧ iwasawaK (p * g) = m * iwasawaK g ∧
      iwasawaB (p * g) = p * iwasawaB g * m⁻¹ := by
  obtain ⟨b, k, hb, hk, rfl⟩ : ∃ b k : RealGL3, IsUpperPositive b ∧ IsOrthogonalReal k ∧
      g = b * k :=
    ⟨iwasawaB g, iwasawaK g, iwasawaB_upper g, iwasawaK_orthogonal g,
      (iwasawaB_mul_iwasawaK g).symm⟩
  obtain ⟨hb1, hk1⟩ := iwasawa_eq hb hk
  have hpb : p * b ∈ P := P.mul_mem hp (hB b hb)
  have hB' := iwasawaB_upper (p * b)
  have hm := iwasawaK_orthogonal (p * b)
  have h1 : iwasawaB (p * b) * iwasawaK (p * b) = p * b := iwasawaB_mul_iwasawaK _
  have hmP : iwasawaK (p * b) ∈ P := iwSubgroup_mem_of_mul_eq P (hB _ hB') hpb h1
  have e : p * (b * k) = iwasawaB (p * b) * (iwasawaK (p * b) * k) := by
    rw [← mul_assoc, ← mul_assoc, h1]
  have hmk : IsOrthogonalReal (iwasawaK (p * b) * k) := hm.mul hk
  obtain ⟨u1, u2⟩ := iwasawa_eq hB' hmk
  refine ⟨iwasawaK (p * b), hmP, hm, ?_, ?_⟩
  · rw [hk1, e]
    exact u2
  · rw [hb1, e, u1]
    exact iwInv_form h1

/-- **Line-parabolic equivariance.** -/
theorem iwasawa_lineParabolic {p : RealGL3} (hp : p ∈ lineParabolic ℝ) (g : RealGL3) :
    ∃ m : RealGL3, m ∈ lineParabolic ℝ ∧ IsOrthogonalReal m ∧
      iwasawaK (p * g) = m * iwasawaK g ∧ iwasawaB (p * g) = p * iwasawaB g * m⁻¹ :=
  iwasawa_parabolic_of_upper (P := lineParabolic ℝ) (fun _ hb => ⟨hb.1, hb.2.1⟩) hp g

/-- **Plane-parabolic equivariance.** -/
theorem iwasawa_planeParabolic {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (g : RealGL3) :
    ∃ m : RealGL3, m ∈ planeParabolic ℝ ∧ IsOrthogonalReal m ∧
      iwasawaK (p * g) = m * iwasawaK g ∧ iwasawaB (p * g) = p * iwasawaB g * m⁻¹ :=
  iwasawa_parabolic_of_upper (P := planeParabolic ℝ) (fun _ hb => ⟨hb.2.1, hb.2.2.1⟩) hp g

/-- An orthogonal element of the line parabolic is block diagonal. -/
theorem orth_lineParabolic_block {m : RealGL3} (hm : m ∈ lineParabolic ℝ)
    (ho : IsOrthogonalReal m) : m.val 0 1 = 0 ∧ m.val 0 2 = 0 := by
  obtain ⟨h10, h20⟩ := hm
  change m.val 1 0 = 0 at h10
  change m.val 2 0 = 0 at h20
  have hc : m.val.transpose * m.val = 1 := ho
  have hr : m.val * m.val.transpose = 1 := ho.rows
  have c00 := congrFun (congrFun hc 0) 0
  have r00 := congrFun (congrFun hr 0) 0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply_eq] at c00 r00
  have hsq : m.val 0 1 ^ 2 + m.val 0 2 ^ 2 = 0 := by
    linear_combination r00 - c00 + m.val 1 0 * h10 + m.val 2 0 * h20
  have a1 : m.val 0 1 ^ 2 = 0 := by
    nlinarith [sq_nonneg (m.val 0 1), sq_nonneg (m.val 0 2)]
  have a2 : m.val 0 2 ^ 2 = 0 := by
    nlinarith [sq_nonneg (m.val 0 1), sq_nonneg (m.val 0 2)]
  exact ⟨iwSq_eq_zero a1, iwSq_eq_zero a2⟩

/-- An orthogonal element of the plane parabolic is block diagonal. -/
theorem orth_planeParabolic_block {m : RealGL3} (hm : m ∈ planeParabolic ℝ)
    (ho : IsOrthogonalReal m) : m.val 0 2 = 0 ∧ m.val 1 2 = 0 := by
  obtain ⟨h20, h21⟩ := hm
  change m.val 2 0 = 0 at h20
  change m.val 2 1 = 0 at h21
  have hc : m.val.transpose * m.val = 1 := ho
  have hr : m.val * m.val.transpose = 1 := ho.rows
  have c22 := congrFun (congrFun hc 2) 2
  have r22 := congrFun (congrFun hr 2) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
    Matrix.one_apply_eq] at c22 r22
  have hsq : m.val 0 2 ^ 2 + m.val 1 2 ^ 2 = 0 := by
    linear_combination c22 - r22 + m.val 2 0 * h20 + m.val 2 1 * h21
  have a1 : m.val 0 2 ^ 2 = 0 := by
    nlinarith [sq_nonneg (m.val 0 2), sq_nonneg (m.val 1 2)]
  have a2 : m.val 1 2 ^ 2 = 0 := by
    nlinarith [sq_nonneg (m.val 0 2), sq_nonneg (m.val 1 2)]
  exact ⟨iwSq_eq_zero a1, iwSq_eq_zero a2⟩

/-! ### Real analyticity -/

theorem iwDomain_isOpen : IsOpen {A : Mat3 | A.det ≠ 0} :=
  isOpen_ne_fun continuous_id.matrix_det continuous_const

theorem iwAnalyticAt_of_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Mat3 → E} (h : ContDiffOn ℝ ⊤ f {A : Mat3 | A.det ≠ 0}) {A : Mat3} (hA : A.det ≠ 0) :
    AnalyticAt ℝ f A := by
  have hA' : A ∈ {A : Mat3 | A.det ≠ 0} := hA
  exact ((iwDomain_isOpen.contDiffOn_iff).mp h hA').analyticAt

theorem iwEntry_contDiff {n : WithTop ℕ∞} (i j : Fin 3) :
    ContDiff ℝ n (fun A : Mat3 => A i j) := by
  fun_prop

theorem iwRow_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} (i : Fin 3) :
    ContDiffOn ℝ n (fun A : Mat3 => A i) S :=
  contDiffOn_pi.mpr fun j => (iwEntry_contDiff i j).contDiffOn

theorem iwDot_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {F G : Mat3 → Fin 3 → ℝ}
    (hF : ContDiffOn ℝ n F S) (hG : ContDiffOn ℝ n G S) :
    ContDiffOn ℝ n (fun A => iwDot (F A) (G A)) S := by
  have hF' := contDiffOn_pi.mp hF
  have hG' := contDiffOn_pi.mp hG
  show ContDiffOn ℝ n (fun A => F A 0 * G A 0 + F A 1 * G A 1 + F A 2 * G A 2) S
  exact (((hF' 0).mul (hG' 0)).add ((hF' 1).mul (hG' 1))).add ((hF' 2).mul (hG' 2))

theorem iwSmul_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {c : Mat3 → ℝ} {F : Mat3 → Fin 3 → ℝ}
    (hc : ContDiffOn ℝ n c S) (hF : ContDiffOn ℝ n F S) :
    ContDiffOn ℝ n (fun A => c A • F A) S := by
  refine contDiffOn_pi.mpr fun j => ?_
  exact hc.mul (contDiffOn_pi.mp hF j)

theorem iwSub_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {F G : Mat3 → Fin 3 → ℝ}
    (hF : ContDiffOn ℝ n F S) (hG : ContDiffOn ℝ n G S) :
    ContDiffOn ℝ n (fun A => F A - G A) S := by
  refine contDiffOn_pi.mpr fun j => ?_
  exact (contDiffOn_pi.mp hF j).sub (contDiffOn_pi.mp hG j)

theorem iwUnit_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {F : Mat3 → Fin 3 → ℝ}
    (hF : ContDiffOn ℝ n F S) (hpos : ∀ A ∈ S, 0 < iwDot (F A) (F A)) :
    ContDiffOn ℝ n (fun A => iwUnit (F A)) S := by
  have h1 : ContDiffOn ℝ n (fun A => iwNorm (F A)) S :=
    (iwDot_contDiffOn hF hF).sqrt (fun A hA => (hpos A hA).ne')
  have h2 : ContDiffOn ℝ n (fun A => (iwNorm (F A))⁻¹) S :=
    h1.inv (fun A hA => (iwNorm_pos (hpos A hA)).ne')
  exact iwSmul_contDiffOn h2 hF

theorem iwK2_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwK2 {A : Mat3 | A.det ≠ 0} := by
  have h := iwUnit_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 2) (iwRow_contDiffOn 2) (fun A hA => iwRow2_pos A hA)
  exact h

theorem iwB12_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwB12 {A : Mat3 | A.det ≠ 0} := by
  have h := iwDot_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 1) (G := iwK2) (iwRow_contDiffOn 1) iwK2_contDiffOn
  exact h

theorem iwV1_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwV1 {A : Mat3 | A.det ≠ 0} := by
  have h := iwSub_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 1) (G := fun A => iwB12 A • iwK2 A) (iwRow_contDiffOn 1)
    (iwSmul_contDiffOn iwB12_contDiffOn iwK2_contDiffOn)
  exact h

theorem iwK1_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwK1 {A : Mat3 | A.det ≠ 0} := by
  have h := iwUnit_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0}) (F := iwV1)
    iwV1_contDiffOn (fun A hA => iwV1_pos A hA)
  exact h

theorem iwB01_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwB01 {A : Mat3 | A.det ≠ 0} := by
  have h := iwDot_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 0) (G := iwK1) (iwRow_contDiffOn 0) iwK1_contDiffOn
  exact h

theorem iwB02_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwB02 {A : Mat3 | A.det ≠ 0} := by
  have h := iwDot_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 0) (G := iwK2) (iwRow_contDiffOn 0) iwK2_contDiffOn
  exact h

theorem iwV0_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwV0 {A : Mat3 | A.det ≠ 0} := by
  have h := iwSub_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0})
    (F := fun A : Mat3 => A 0 - iwB01 A • iwK1 A) (G := fun A => iwB02 A • iwK2 A)
    (iwSub_contDiffOn (iwRow_contDiffOn 0) (iwSmul_contDiffOn iwB01_contDiffOn iwK1_contDiffOn))
    (iwSmul_contDiffOn iwB02_contDiffOn iwK2_contDiffOn)
  exact h

theorem iwK0_contDiffOn {n : WithTop ℕ∞} : ContDiffOn ℝ n iwK0 {A : Mat3 | A.det ≠ 0} := by
  have h := iwUnit_contDiffOn (n := n) (S := {A : Mat3 | A.det ≠ 0}) (F := iwV0)
    iwV0_contDiffOn (fun A hA => iwV0_pos A hA)
  exact h

theorem iwasawaKMatrix_contDiffOn {n : WithTop ℕ∞} :
    ContDiffOn ℝ n iwasawaKMatrix {A : Mat3 | A.det ≠ 0} := by
  refine contDiffOn_pi.mpr fun i => ?_
  fin_cases i
  · exact iwK0_contDiffOn
  · exact iwK1_contDiffOn
  · exact iwK2_contDiffOn

theorem iwMatMul_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {F G : Mat3 → Mat3}
    (hF : ContDiffOn ℝ n F S) (hG : ContDiffOn ℝ n G S) :
    ContDiffOn ℝ n (fun A => F A * G A) S := by
  have hF' : ∀ i j, ContDiffOn ℝ n (fun A => F A i j) S :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hF i) j
  have hG' : ∀ i j, ContDiffOn ℝ n (fun A => G A i j) S :=
    fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hG i) j
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun r _ => (hF' i r).mul (hG' r j)

theorem iwTranspose_contDiffOn {n : WithTop ℕ∞} {S : Set Mat3} {F : Mat3 → Mat3}
    (hF : ContDiffOn ℝ n F S) : ContDiffOn ℝ n (fun A => (F A).transpose) S := by
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  exact contDiffOn_pi.mp (contDiffOn_pi.mp hF j) i

theorem iwasawaBMatrix_contDiffOn {n : WithTop ℕ∞} :
    ContDiffOn ℝ n iwasawaBMatrix {A : Mat3 | A.det ≠ 0} := by
  have h : ContDiffOn ℝ n (fun A : Mat3 => A * (iwasawaKMatrix A).transpose)
      {A : Mat3 | A.det ≠ 0} :=
    iwMatMul_contDiffOn (F := fun A : Mat3 => A) contDiffOn_id
      (iwTranspose_contDiffOn iwasawaKMatrix_contDiffOn)
  exact h.congr fun A hA => iwasawaBMatrix_eq_mul_transpose A hA

/-- Analyticity (`ContDiffOn ℝ ⊤`, i.e. `C^ω`) of the orthogonal Iwasawa factor. -/
theorem iwasawaKMatrix_contDiffOn_top :
    ContDiffOn ℝ ⊤ iwasawaKMatrix {A : Mat3 | A.det ≠ 0} :=
  iwasawaKMatrix_contDiffOn

/-- Analyticity (`ContDiffOn ℝ ⊤`, i.e. `C^ω`) of the upper triangular Iwasawa factor. -/
theorem iwasawaBMatrix_contDiffOn_top :
    ContDiffOn ℝ ⊤ iwasawaBMatrix {A : Mat3 | A.det ≠ 0} :=
  iwasawaBMatrix_contDiffOn

theorem iwasawaK_contDiffOn :
    ContDiffOn ℝ ⊤ (fun A : Mat3 => (iwasawaK (invertibleMatrix A)).val) {A : Mat3 | A.det ≠ 0} := by
  refine (iwasawaKMatrix_contDiffOn (n := ⊤)).congr fun A hA => ?_
  have hA' : A.det ≠ 0 := hA
  show iwasawaKMatrix (invertibleMatrix A).val = iwasawaKMatrix A
  rw [invertibleMatrix_val A hA']

theorem iwasawaB_contDiffOn :
    ContDiffOn ℝ ⊤ (fun A : Mat3 => (iwasawaB (invertibleMatrix A)).val) {A : Mat3 | A.det ≠ 0} := by
  refine (iwasawaBMatrix_contDiffOn (n := ⊤)).congr fun A hA => ?_
  have hA' : A.det ≠ 0 := hA
  show (iwasawaB (invertibleMatrix A)).val = iwasawaBMatrix A
  rw [iwasawaB_val, invertibleMatrix_val A hA']

theorem iwasawaKMatrix_analyticAt {A : Mat3} (hA : A.det ≠ 0) :
    AnalyticAt ℝ iwasawaKMatrix A :=
  iwAnalyticAt_of_contDiffOn iwasawaKMatrix_contDiffOn_top hA

theorem iwasawaBMatrix_analyticAt {A : Mat3} (hA : A.det ≠ 0) :
    AnalyticAt ℝ iwasawaBMatrix A :=
  iwAnalyticAt_of_contDiffOn iwasawaBMatrix_contDiffOn_top hA

theorem iwasawaK_analyticAt {A : Mat3} (hA : A.det ≠ 0) :
    AnalyticAt ℝ (fun A : Mat3 => (iwasawaK (invertibleMatrix A)).val) A :=
  iwAnalyticAt_of_contDiffOn iwasawaK_contDiffOn hA

theorem iwasawaB_analyticAt {A : Mat3} (hA : A.det ≠ 0) :
    AnalyticAt ℝ (fun A : Mat3 => (iwasawaB (invertibleMatrix A)).val) A :=
  iwAnalyticAt_of_contDiffOn iwasawaB_contDiffOn hA

end TernaryPeriodPolynomials.SourceConstruction
