module

public import TernaryPeriodPolynomials.Building.ModThreeGoodAction
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.NonunimodularFractionalPoint

open ModThreeGoodAction Matrix

abbrev IntegralMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- Coefficient extension to the rational matrix space. -/
def rationalMatrix (M : IntegralMatrix) : Matrix (Fin 3) (Fin 3) ℚ :=
  M.map (Int.castRingHom ℚ)

theorem rationalMatrix_det (M : IntegralMatrix) : (rationalMatrix M).det = (M.det : ℚ) :=
  ((Int.castRingHom ℚ).map_det M).symm

theorem rationalMatrix_mul_inverse {M : IntegralMatrix} (hM : M.det ≠ 0) :
    rationalMatrix M * (rationalMatrix M)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  apply isUnit_iff_ne_zero.mpr
  rw [rationalMatrix_det]
  exact_mod_cast hM

/-- A nonunit integer determinant forces a genuinely nonintegral inverse entry. -/
theorem exists_fractional_inverse_entry (M : IntegralMatrix) (hM : M.det ≠ 0)
    (hlarge : 1 < M.det.natAbs) :
    ∃ i j : Fin 3, (rationalMatrix M)⁻¹ i j ≠ (⌊(rationalMatrix M)⁻¹ i j⌋ : ℚ) := by
  classical
  by_contra h
  have he (i j : Fin 3) : (rationalMatrix M)⁻¹ i j = (⌊(rationalMatrix M)⁻¹ i j⌋ : ℚ) :=
    not_ne_iff.mp (fun hn => h ⟨i,j,hn⟩)
  let B : IntegralMatrix := fun i j => ⌊(rationalMatrix M)⁻¹ i j⌋
  have hB : B.map (Int.castRingHom ℚ) = (rationalMatrix M)⁻¹ := by
    ext i j
    exact (he i j).symm
  have hMB : M * B = 1 := by
    apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    change (M * B).map (Int.castRingHom ℚ) = (1 : IntegralMatrix).map (Int.castRingHom ℚ)
    rw [Matrix.map_mul,hB]
    change rationalMatrix M * (rationalMatrix M)⁻¹ = (1 : IntegralMatrix).map (Int.castRingHom ℚ)
    rw [rationalMatrix_mul_inverse hM]
    simp
  have hu : IsUnit M.det := Matrix.isUnit_det_of_right_inverse hMB
  exact (ne_of_gt hlarge) (Int.isUnit_iff_natAbs_eq.mp hu)

theorem rationalVector_matrix_mulVec (M : IntegralMatrix) (u : IntegralVector) :
    rationalVector (M.mulVec u) = (rationalMatrix M).mulVec (rationalVector u) := by
  funext i
  exact (Int.castRingHom ℚ).map_mulVec M u i

/-- An inverse column maps to its corresponding standard integral basis vector. -/
theorem inverse_column_mulVec (M : IntegralMatrix) (hM : M.det ≠ 0) (j : Fin 3) :
    (rationalMatrix M).mulVec (fun i => (rationalMatrix M)⁻¹ i j) = Pi.single j 1 := by
  change (rationalMatrix M).mulVec ((rationalMatrix M)⁻¹.col j) = _
  rw [← Matrix.mulVec_single_one,Matrix.mulVec_mulVec,rationalMatrix_mul_inverse hM,
    Matrix.one_mulVec]

/-- The half-open fundamental parallelepiped of a nonunimodular integer matrix
contains a nonzero integral point, expressed with all coefficients in `[0,1)`. -/
theorem fractional_lattice_point (M : IntegralMatrix) (hM : M.det ≠ 0)
    (hlarge : 1 < M.det.natAbs) :
    ∃ (w : IntegralVector) (a : Fin 3 → ℚ),
      rationalVector w = (M.map (Int.castRingHom ℚ)).mulVec a ∧
      (∀ i, 0 ≤ a i ∧ a i < 1) ∧ ∃ k, 0 < a k := by
  classical
  obtain ⟨k,j,hkj⟩ := exists_fractional_inverse_entry M hM hlarge
  let c : Fin 3 → ℚ := fun i => (rationalMatrix M)⁻¹ i j
  let u : IntegralVector := fun i => ⌊c i⌋
  let a : Fin 3 → ℚ := fun i => Int.fract (c i)
  let w : IntegralVector := Pi.single j 1 - M.mulVec u
  have ha : a = c - rationalVector u := rfl
  have he : rationalVector (Pi.single j 1 : IntegralVector) = Pi.single j 1 := by
    ext i
    simp [rationalVector,Pi.single_apply]
  have hw : rationalVector w = rationalVector (Pi.single j 1 : IntegralVector) -
      rationalVector (M.mulVec u) := by
    ext i
    simp [w,rationalVector]
  refine ⟨w,a,?_,?_,?_⟩
  · change rationalVector w = (rationalMatrix M).mulVec a
    rw [hw,he,rationalVector_matrix_mulVec,ha,Matrix.mulVec_sub]
    rw [show (rationalMatrix M).mulVec c = Pi.single j 1 from inverse_column_mulVec M hM j]
  · intro i
    exact ⟨Int.fract_nonneg (c i),Int.fract_lt_one (c i)⟩
  · exact ⟨k,Int.fract_pos.mpr hkj⟩

end TernaryPoly.NonunimodularFractionalPoint
