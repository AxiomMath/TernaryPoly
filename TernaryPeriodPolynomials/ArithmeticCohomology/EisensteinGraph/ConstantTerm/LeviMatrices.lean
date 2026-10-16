module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.Basic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.ConstantTerm.GridCovariance

@[expose] public section


/-!
# Levi matrices of flag-preserving arithmetic elements

Let `g ∈ GL₃(ℤ)` and let `γ` lie in the rational image of the arithmetic level. If
`p = g⁻¹ γ g` lies in the standard rational parabolic of a side, then `p` is the image of an
integral matrix `p₀ ∈ GL₃(ℤ)` lying in the parabolic, and conjugation of the unipotent radical
by `p` acts on its coordinates through the column action of a matrix `A ∈ GL₂(ℤ)`:
`p⁻¹ u(κ r) p = u(κ A r)` for every real scalar `κ` and `r ∈ ℝ²`.

Written by AxiomCode.
-/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

namespace LeviMatrices

/-- Conjugation by `P` carries `U` to `U'` as soon as `U P = P U'`. -/
theorem lev_conj_eq_of_comm {R : Type*} [CommRing R] (P U U' : GL3 R)
    (h : (U : Matrix (Fin 3) (Fin 3) R) * (P : Matrix (Fin 3) (Fin 3) R) =
      (P : Matrix (Fin 3) (Fin 3) R) * (U' : Matrix (Fin 3) (Fin 3) R)) :
    P⁻¹ * U * P = U' := by
  have h' : U * P = P * U' := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h)
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h'

/-- A `3 × 3` matrix equality from its nine entries. -/
theorem lev_matrix3_ext {R : Type*} (M N : Matrix (Fin 3) (Fin 3) R)
    (h00 : M 0 0 = N 0 0) (h01 : M 0 1 = N 0 1) (h02 : M 0 2 = N 0 2)
    (h10 : M 1 0 = N 1 0) (h11 : M 1 1 = N 1 1) (h12 : M 1 2 = N 1 2)
    (h20 : M 2 0 = N 2 0) (h21 : M 2 1 = N 2 1) (h22 : M 2 2 = N 2 2) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem lev_map_val {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : GL3 R)
    (i j : Fin 3) : (Matrix.GeneralLinearGroup.map f x).val i j = f (x.val i j) :=
  rfl

theorem lev_castQ_val (x : Matrix.GeneralLinearGroup (Fin 3) ℤ) (i j : Fin 3) :
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) x).val i j = ((x.val i j : ℤ) : ℚ) :=
  (lev_map_val (Int.castRingHom ℚ) x i j).trans rfl

theorem lev_map_map_val (x : Matrix.GeneralLinearGroup (Fin 3) ℤ) (i j : Fin 3) :
    (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) x)).val i j = ((x.val i j : ℤ) : ℝ) :=
  (lev_map_val (algebraMap ℚ ℝ) (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) x) i j).trans
    ((congrArg (algebraMap ℚ ℝ) (lev_map_val (Int.castRingHom ℚ) x i j)).trans (by simp))

theorem lev_mul_entry {R : Type*} [CommRing R] (P Q : Matrix (Fin 3) (Fin 3) R) (h : P * Q = 1)
    (i j : Fin 3) :
    P i 0 * Q 0 j + P i 1 * Q 1 j + P i 2 * Q 2 j = (1 : Matrix (Fin 3) (Fin 3) R) i j := by
  have h' : (P * Q) i j = (1 : Matrix (Fin 3) (Fin 3) R) i j := by rw [h]
  rw [Matrix.mul_apply, Fin.sum_univ_three] at h'
  exact h'

theorem lev_mul_diag {R : Type*} [CommRing R] (P Q : Matrix (Fin 3) (Fin 3) R) (h : P * Q = 1)
    (i : Fin 3) : P i 0 * Q 0 i + P i 1 * Q 1 i + P i 2 * Q 2 i = 1 := by
  have h' := lev_mul_entry P Q h i i
  rw [Matrix.one_apply_eq] at h'
  exact h'

theorem lev_mul_off {R : Type*} [CommRing R] (P Q : Matrix (Fin 3) (Fin 3) R) (h : P * Q = 1)
    {i j : Fin 3} (hij : i ≠ j) : P i 0 * Q 0 j + P i 1 * Q 1 j + P i 2 * Q 2 j = 0 := by
  have h' := lev_mul_entry P Q h i j
  rw [Matrix.one_apply_ne hij] at h'
  exact h'

/-- Building an element of `GL₂(ℤ)` from the entries of a matrix and of a right inverse. -/
theorem lev_exists_GL2 (m00 m01 m10 m11 n00 n01 n10 n11 : ℤ)
    (h00 : m00 * n00 + m01 * n10 = 1) (h01 : m00 * n01 + m01 * n11 = 0)
    (h10 : m10 * n00 + m11 * n10 = 0) (h11 : m10 * n01 + m11 * n11 = 1) :
    ∃ A : GLTwo ℤ, A.val 0 0 = m00 ∧ A.val 0 1 = m01 ∧ A.val 1 0 = m10 ∧
      A.val 1 1 = m11 := by
  have h : (!![m00, m01; m10, m11] : Matrix (Fin 2) (Fin 2) ℤ) * !![n00, n01; n10, n11] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two, h00, h01, h10, h11]
  exact ⟨⟨!![m00, m01; m10, m11], !![n00, n01; n10, n11], h, mul_eq_one_comm.mp h⟩,
    rfl, rfl, rfl, rfl⟩

theorem lev_plane_entries {R : Type*} [CommRing R] (s t : R) :
    (planeUnipotent s t).val 0 0 = 1 ∧ (planeUnipotent s t).val 0 1 = 0 ∧
    (planeUnipotent s t).val 0 2 = s ∧ (planeUnipotent s t).val 1 0 = 0 ∧
    (planeUnipotent s t).val 1 1 = 1 ∧ (planeUnipotent s t).val 1 2 = t ∧
    (planeUnipotent s t).val 2 0 = 0 ∧ (planeUnipotent s t).val 2 1 = 0 ∧
    (planeUnipotent s t).val 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem lev_line_entries {R : Type*} [CommRing R] (s t : R) :
    (lineUnipotent s t).val 0 0 = 1 ∧ (lineUnipotent s t).val 0 1 = s ∧
    (lineUnipotent s t).val 0 2 = t ∧ (lineUnipotent s t).val 1 0 = 0 ∧
    (lineUnipotent s t).val 1 1 = 1 ∧ (lineUnipotent s t).val 1 2 = 0 ∧
    (lineUnipotent s t).val 2 0 = 0 ∧ (lineUnipotent s t).val 2 1 = 0 ∧
    (lineUnipotent s t).val 2 2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The commutation `u(κ r) P = P u(κ A r)` for a matrix `P` with zero entries `(2,0)`, `(2,1)`,
where `A = (m_ij)` satisfies `P_B A = P₂₂ · 1` for the top-left block `P_B` of `P`. -/
theorem lev_plane_comm {R : Type*} [CommRing R] (P : Matrix (Fin 3) (Fin 3) R)
    (m00 m01 m10 m11 : R) (h20 : P 2 0 = 0) (h21 : P 2 1 = 0)
    (h00 : P 0 0 * m00 + P 0 1 * m10 = P 2 2) (h01 : P 0 0 * m01 + P 0 1 * m11 = 0)
    (h10 : P 1 0 * m00 + P 1 1 * m10 = 0) (h11 : P 1 0 * m01 + P 1 1 * m11 = P 2 2)
    (κ x y : R) :
    (planeUnipotent (κ * x) (κ * y)).val * P =
      P * (planeUnipotent (κ * (m00 * x + m01 * y)) (κ * (m10 * x + m11 * y))).val := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := lev_plane_entries (κ * x) (κ * y)
  obtain ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩ :=
    lev_plane_entries (κ * (m00 * x + m01 * y)) (κ * (m10 * x + m11 * y))
  refine lev_matrix3_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b00, b10, b20]
    linear_combination (κ * x) * h20
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b01, b11, b21]
    linear_combination (κ * x) * h21
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b02, b12, b22]
    linear_combination (-(κ * x)) * h00 - (κ * y) * h01
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b00, b10, b20]
    linear_combination (κ * y) * h20
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b01, b11, b21]
    linear_combination (κ * y) * h21
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b02, b12, b22]
    linear_combination (-(κ * x)) * h10 - (κ * y) * h11
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b00, b10, b20]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b01, b11, b21]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b02, b12, b22]
    linear_combination (-(κ * (m00 * x + m01 * y))) * h20 - (κ * (m10 * x + m11 * y)) * h21

/-- The commutation `u(κ r) P = P u(κ A r)` for a matrix `P` with zero entries `(1,0)`, `(2,0)`,
where `A = (m_ij)` satisfies `P₀₀ A = (P_B)ᵀ` for the bottom-right block `P_B` of `P`. -/
theorem lev_line_comm {R : Type*} [CommRing R] (P : Matrix (Fin 3) (Fin 3) R)
    (m00 m01 m10 m11 : R) (h10 : P 1 0 = 0) (h20 : P 2 0 = 0)
    (hm00 : P 0 0 * m00 = P 1 1) (hm01 : P 0 0 * m01 = P 2 1)
    (hm10 : P 0 0 * m10 = P 1 2) (hm11 : P 0 0 * m11 = P 2 2)
    (κ x y : R) :
    (lineUnipotent (κ * x) (κ * y)).val * P =
      P * (lineUnipotent (κ * (m00 * x + m01 * y)) (κ * (m10 * x + m11 * y))).val := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := lev_line_entries (κ * x) (κ * y)
  obtain ⟨b00, b01, b02, b10, b11, b12, b20, b21, b22⟩ :=
    lev_line_entries (κ * (m00 * x + m01 * y)) (κ * (m10 * x + m11 * y))
  refine lev_matrix3_ext _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b00, b10, b20]
    linear_combination (κ * x) * h10 + (κ * y) * h20
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b01, b11, b21]
    linear_combination (-(κ * x)) * hm00 - (κ * y) * hm01
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a00, a01, a02, b02, b12, b22]
    linear_combination (-(κ * x)) * hm10 - (κ * y) * hm11
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b00, b10, b20]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b01, b11, b21]
    linear_combination (-(κ * (m00 * x + m01 * y))) * h10
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a10, a11, a12, b02, b12, b22]
    linear_combination (-(κ * (m10 * x + m11 * y))) * h10
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b00, b10, b20]
    ring
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b01, b11, b21]
    linear_combination (-(κ * (m00 * x + m01 * y))) * h20
  · simp only [Matrix.mul_apply, Fin.sum_univ_three, a20, a21, a22, b02, b12, b22]
    linear_combination (-(κ * (m10 * x + m11 * y))) * h20

/-- Integral block computation for a matrix with a zero `(2,0)`, `(2,1)` corner and inverse. -/
theorem lev_plane_aux (P Q : Matrix (Fin 3) (Fin 3) ℤ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h20 : P 2 0 = 0) (h21 : P 2 1 = 0) (hq20 : Q 2 0 = 0) (hq21 : Q 2 1 = 0) :
    ∃ A : GLTwo ℤ,
      P 0 0 * A.val 0 0 + P 0 1 * A.val 1 0 = P 2 2 ∧
      P 0 0 * A.val 0 1 + P 0 1 * A.val 1 1 = 0 ∧
      P 1 0 * A.val 0 0 + P 1 1 * A.val 1 0 = 0 ∧
      P 1 0 * A.val 0 1 + P 1 1 * A.val 1 1 = P 2 2 := by
  have g22 : P 2 2 * Q 2 2 = 1 := by
    have h := lev_mul_diag P Q hPQ 2
    linear_combination h - Q 0 2 * h20 - Q 1 2 * h21
  have f00 : Q 0 0 * P 0 0 + Q 0 1 * P 1 0 = 1 := by
    have h := lev_mul_diag Q P hQP 0
    linear_combination h - Q 0 2 * h20
  have f01 : Q 0 0 * P 0 1 + Q 0 1 * P 1 1 = 0 := by
    have h := lev_mul_off Q P hQP (show (0 : Fin 3) ≠ 1 by decide)
    linear_combination h - Q 0 2 * h21
  have f10 : Q 1 0 * P 0 0 + Q 1 1 * P 1 0 = 0 := by
    have h := lev_mul_off Q P hQP (show (1 : Fin 3) ≠ 0 by decide)
    linear_combination h - Q 1 2 * h20
  have f11 : Q 1 0 * P 0 1 + Q 1 1 * P 1 1 = 1 := by
    have h := lev_mul_diag Q P hQP 1
    linear_combination h - Q 1 2 * h21
  have e00 : P 0 0 * Q 0 0 + P 0 1 * Q 1 0 = 1 := by
    have h := lev_mul_diag P Q hPQ 0
    linear_combination h - P 0 2 * hq20
  have e01 : P 0 0 * Q 0 1 + P 0 1 * Q 1 1 = 0 := by
    have h := lev_mul_off P Q hPQ (show (0 : Fin 3) ≠ 1 by decide)
    linear_combination h - P 0 2 * hq21
  have e10 : P 1 0 * Q 0 0 + P 1 1 * Q 1 0 = 0 := by
    have h := lev_mul_off P Q hPQ (show (1 : Fin 3) ≠ 0 by decide)
    linear_combination h - P 1 2 * hq20
  have e11 : P 1 0 * Q 0 1 + P 1 1 * Q 1 1 = 1 := by
    have h := lev_mul_diag P Q hPQ 1
    linear_combination h - P 1 2 * hq21
  obtain ⟨A, hA00, hA01, hA10, hA11⟩ := lev_exists_GL2
    (P 2 2 * Q 0 0) (P 2 2 * Q 0 1) (P 2 2 * Q 1 0) (P 2 2 * Q 1 1)
    (Q 2 2 * P 0 0) (Q 2 2 * P 0 1) (Q 2 2 * P 1 0) (Q 2 2 * P 1 1)
    (by linear_combination (Q 0 0 * P 0 0 + Q 0 1 * P 1 0) * g22 + f00)
    (by linear_combination (Q 0 0 * P 0 1 + Q 0 1 * P 1 1) * g22 + f01)
    (by linear_combination (Q 1 0 * P 0 0 + Q 1 1 * P 1 0) * g22 + f10)
    (by linear_combination (Q 1 0 * P 0 1 + Q 1 1 * P 1 1) * g22 + f11)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [hA00, hA10]
    linear_combination P 2 2 * e00
  · rw [hA01, hA11]
    linear_combination P 2 2 * e01
  · rw [hA00, hA10]
    linear_combination P 2 2 * e10
  · rw [hA01, hA11]
    linear_combination P 2 2 * e11

/-- Integral block computation for a matrix with a zero `(1,0)`, `(2,0)` corner and inverse. -/
theorem lev_line_aux (P Q : Matrix (Fin 3) (Fin 3) ℤ) (hQP : Q * P = 1)
    (h10 : P 1 0 = 0) (h20 : P 2 0 = 0) (hq10 : Q 1 0 = 0) (hq20 : Q 2 0 = 0) :
    ∃ A : GLTwo ℤ,
      P 0 0 * A.val 0 0 = P 1 1 ∧ P 0 0 * A.val 0 1 = P 2 1 ∧
      P 0 0 * A.val 1 0 = P 1 2 ∧ P 0 0 * A.val 1 1 = P 2 2 := by
  have e0 : Q 0 0 * P 0 0 = 1 := by
    have h := lev_mul_diag Q P hQP 0
    linear_combination h - Q 0 1 * h10 - Q 0 2 * h20
  have d11 : Q 1 1 * P 1 1 + Q 1 2 * P 2 1 = 1 := by
    have h := lev_mul_diag Q P hQP 1
    linear_combination h - P 0 1 * hq10
  have d12 : Q 1 1 * P 1 2 + Q 1 2 * P 2 2 = 0 := by
    have h := lev_mul_off Q P hQP (show (1 : Fin 3) ≠ 2 by decide)
    linear_combination h - P 0 2 * hq10
  have d21 : Q 2 1 * P 1 1 + Q 2 2 * P 2 1 = 0 := by
    have h := lev_mul_off Q P hQP (show (2 : Fin 3) ≠ 1 by decide)
    linear_combination h - P 0 1 * hq20
  have d22 : Q 2 1 * P 1 2 + Q 2 2 * P 2 2 = 1 := by
    have h := lev_mul_diag Q P hQP 2
    linear_combination h - P 0 2 * hq20
  obtain ⟨A, hA00, hA01, hA10, hA11⟩ := lev_exists_GL2
    (Q 0 0 * P 1 1) (Q 0 0 * P 2 1) (Q 0 0 * P 1 2) (Q 0 0 * P 2 2)
    (P 0 0 * Q 1 1) (P 0 0 * Q 2 1) (P 0 0 * Q 1 2) (P 0 0 * Q 2 2)
    (by linear_combination (Q 1 1 * P 1 1 + Q 1 2 * P 2 1) * e0 + d11)
    (by linear_combination (Q 2 1 * P 1 1 + Q 2 2 * P 2 1) * e0 + d21)
    (by linear_combination (Q 1 1 * P 1 2 + Q 1 2 * P 2 2) * e0 + d12)
    (by linear_combination (Q 2 1 * P 1 2 + Q 2 2 * P 2 2) * e0 + d22)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · rw [hA00]
    linear_combination P 1 1 * e0
  · rw [hA01]
    linear_combination P 2 1 * e0
  · rw [hA10]
    linear_combination P 1 2 * e0
  · rw [hA11]
    linear_combination P 2 2 * e0

/-- The plane case: a plane-parabolic integral matrix acts on the plane radical through `GL₂(ℤ)`,
for every scalar `κ`. -/
theorem plane_conj_of_entries (p0 : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (Pg : Matrix.GeneralLinearGroup (Fin 3) ℝ)
    (hP : ∀ i j, Pg.val i j = ((p0.val i j : ℤ) : ℝ))
    (h20 : p0.val 2 0 = 0) (h21 : p0.val 2 1 = 0) :
    ∃ A : GLTwo ℤ, ∀ (κ : ℝ) (r : ℝ × ℝ),
      Pg⁻¹ * sideUnipotent Side.plane (κ * r.1) (κ * r.2) * Pg =
        sideUnipotent Side.plane (κ * (realAct A r).1) (κ * (realAct A r).2) := by
  have hinv : InPlaneParabolic (p0⁻¹) := inPlane_inv (And.intro h20 h21)
  have hq20 : p0.inv 2 0 = 0 := hinv.1
  have hq21 : p0.inv 2 1 = 0 := hinv.2
  obtain ⟨A, e00, e01, e10, e11⟩ :=
    lev_plane_aux p0.val p0.inv p0.val_inv p0.inv_val h20 h21 hq20 hq21
  refine ⟨A, fun κ r => ?_⟩
  refine lev_conj_eq_of_comm Pg _ _ ?_
  have h20' : Pg.val 2 0 = 0 := by
    rw [hP]
    exact_mod_cast h20
  have h21' : Pg.val 2 1 = 0 := by
    rw [hP]
    exact_mod_cast h21
  have h00' : Pg.val 0 0 * ((A.val 0 0 : ℤ) : ℝ) + Pg.val 0 1 * ((A.val 1 0 : ℤ) : ℝ) =
      Pg.val 2 2 := by
    simp only [hP]
    exact_mod_cast e00
  have h01' : Pg.val 0 0 * ((A.val 0 1 : ℤ) : ℝ) + Pg.val 0 1 * ((A.val 1 1 : ℤ) : ℝ) = 0 := by
    simp only [hP]
    exact_mod_cast e01
  have h10' : Pg.val 1 0 * ((A.val 0 0 : ℤ) : ℝ) + Pg.val 1 1 * ((A.val 1 0 : ℤ) : ℝ) = 0 := by
    simp only [hP]
    exact_mod_cast e10
  have h11' : Pg.val 1 0 * ((A.val 0 1 : ℤ) : ℝ) + Pg.val 1 1 * ((A.val 1 1 : ℤ) : ℝ) =
      Pg.val 2 2 := by
    simp only [hP]
    exact_mod_cast e11
  exact lev_plane_comm Pg.val ((A.val 0 0 : ℤ) : ℝ) ((A.val 0 1 : ℤ) : ℝ) ((A.val 1 0 : ℤ) : ℝ)
    ((A.val 1 1 : ℤ) : ℝ) h20' h21' h00' h01' h10' h11' κ r.1 r.2

/-- The line case: a line-parabolic integral matrix acts on the line radical through `GL₂(ℤ)`,
for every scalar `κ`. -/
theorem line_conj_of_entries (p0 : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (Pg : Matrix.GeneralLinearGroup (Fin 3) ℝ)
    (hP : ∀ i j, Pg.val i j = ((p0.val i j : ℤ) : ℝ))
    (h10 : p0.val 1 0 = 0) (h20 : p0.val 2 0 = 0) :
    ∃ A : GLTwo ℤ, ∀ (κ : ℝ) (r : ℝ × ℝ),
      Pg⁻¹ * sideUnipotent Side.line (κ * r.1) (κ * r.2) * Pg =
        sideUnipotent Side.line (κ * (realAct A r).1) (κ * (realAct A r).2) := by
  have hinv : InLineParabolic (p0⁻¹) := inLine_inv (And.intro h10 h20)
  have hq10 : p0.inv 1 0 = 0 := hinv.1
  have hq20 : p0.inv 2 0 = 0 := hinv.2
  obtain ⟨A, e00, e01, e10, e11⟩ :=
    lev_line_aux p0.val p0.inv p0.inv_val h10 h20 hq10 hq20
  refine ⟨A, fun κ r => ?_⟩
  refine lev_conj_eq_of_comm Pg _ _ ?_
  have h10' : Pg.val 1 0 = 0 := by
    rw [hP]
    exact_mod_cast h10
  have h20' : Pg.val 2 0 = 0 := by
    rw [hP]
    exact_mod_cast h20
  have hm00 : Pg.val 0 0 * ((A.val 0 0 : ℤ) : ℝ) = Pg.val 1 1 := by
    simp only [hP]
    exact_mod_cast e00
  have hm01 : Pg.val 0 0 * ((A.val 0 1 : ℤ) : ℝ) = Pg.val 2 1 := by
    simp only [hP]
    exact_mod_cast e01
  have hm10 : Pg.val 0 0 * ((A.val 1 0 : ℤ) : ℝ) = Pg.val 1 2 := by
    simp only [hP]
    exact_mod_cast e10
  have hm11 : Pg.val 0 0 * ((A.val 1 1 : ℤ) : ℝ) = Pg.val 2 2 := by
    simp only [hP]
    exact_mod_cast e11
  exact lev_line_comm Pg.val ((A.val 0 0 : ℤ) : ℝ) ((A.val 0 1 : ℤ) : ℝ) ((A.val 1 0 : ℤ) : ℝ)
    ((A.val 1 1 : ℤ) : ℝ) h10' h20' hm00 hm01 hm10 hm11 κ r.1 r.2

/-- The conjugate `p = g⁻¹ γ g` of an element of the rational arithmetic level by an integral
matrix and lying in the parabolic of `side` acts on the radical through an integral matrix. -/
theorem exists_of_eq (side : Side) (g : Matrix.GeneralLinearGroup (Fin 3) ℤ) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel) (p : RationalGL3)
    (hpdef : p = (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)⁻¹ * γ *
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)
    (hp : p ∈ parabolic side) :
    ∃ A : GLTwo ℤ, ∀ (κ : ℝ) (r : ℝ × ℝ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) p)⁻¹ *
          sideUnipotent side (κ * r.1) (κ * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) p =
      sideUnipotent side (κ * (realAct A r).1) (κ * (realAct A r).2) := by
  have hγ' : γ ∈ rationalInclusion.range := hγ
  obtain ⟨γ0, hγ0⟩ := MonoidHom.mem_range.1 hγ'
  have hγ1 : Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ)
      (γ0 : Matrix.GeneralLinearGroup (Fin 3) ℤ) = γ := hγ0
  obtain ⟨p0, hp0⟩ : ∃ p0 : Matrix.GeneralLinearGroup (Fin 3) ℤ,
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) p0 = p := by
    refine ⟨g⁻¹ * (γ0 : Matrix.GeneralLinearGroup (Fin 3) ℤ) * g, ?_⟩
    rw [hpdef, ← hγ1]
    simp only [map_mul, map_inv]
  have hP : ∀ i j, (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) p).val i j =
      ((p0.val i j : ℤ) : ℝ) := by
    intro i j
    rw [← hp0]
    exact lev_map_map_val p0 i j
  cases side with
  | plane =>
    have hq : InPlaneParabolic p := hp
    have h20 : p0.val 2 0 = 0 := by
      have h := hq.1
      rw [← hp0, lev_castQ_val] at h
      exact_mod_cast h
    have h21 : p0.val 2 1 = 0 := by
      have h := hq.2
      rw [← hp0, lev_castQ_val] at h
      exact_mod_cast h
    exact plane_conj_of_entries p0 (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) p) hP h20 h21
  | line =>
    have hq : InLineParabolic p := hp
    have h10 : p0.val 1 0 = 0 := by
      have h := hq.1
      rw [← hp0, lev_castQ_val] at h
      exact_mod_cast h
    have h20 : p0.val 2 0 = 0 := by
      have h := hq.2
      rw [← hp0, lev_castQ_val] at h
      exact_mod_cast h
    exact line_conj_of_entries p0 (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) p) hP h10 h20

end LeviMatrices

/-- **Levi matrix of a flag-preserving arithmetic element, with a scalar.**  If `γ` lies in the
rational arithmetic level and `p = g⁻¹ γ g` lies in the parabolic of `side`, then conjugation of
the real radical coordinates `κ r` by `p` is the column action of one integral matrix `A`,
independent of the scalar `κ`. -/
theorem exists_levi_matrix_scaled (side : Side) (g : IntegralGL3) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel)
    (hp : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3) ∈ parabolic side) :
    ∃ A : GLTwo ℤ, ∀ (κ : ℝ) (r : ℝ × ℝ),
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)))⁻¹ *
        sideUnipotent side (κ * r.1) (κ * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)) =
      sideUnipotent side (κ * (realAct A r).1) (κ * (realAct A r).2) :=
  LeviMatrices.exists_of_eq side g γ hγ _ rfl hp

/-- **Levi matrix of a flag-preserving arithmetic element.**  The case `κ = 3` of
`exists_levi_matrix_scaled`. -/
theorem exists_levi_matrix (side : Side) (g : IntegralGL3) (γ : RationalGL3)
    (hγ : γ ∈ rationalLevel)
    (hp : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3) ∈ parabolic side) :
    ∃ A : GLTwo ℤ, ∀ r : ℝ × ℝ,
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)))⁻¹ *
        sideUnipotent side (3 * r.1) (3 * r.2) *
        Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)⁻¹ * γ *
            (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : RationalGL3)) =
      sideUnipotent side (3 * (realAct A r).1) (3 * (realAct A r).2) := by
  obtain ⟨A, hA⟩ := exists_levi_matrix_scaled side g γ hγ hp
  exact ⟨A, fun r => hA 3 r⟩

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
