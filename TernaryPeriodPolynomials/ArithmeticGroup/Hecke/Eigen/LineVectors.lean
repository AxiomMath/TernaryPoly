module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.PlaneVectors

@[expose] public section


/-!
# Line-induced sections as cusp-representation-valued functions

The line analogue of `PlaneVectors`: for a line-induced section `f` and a point `h`,
`A ↦ |det A|^{-e} f(lineLevi 1 A · h)` is a cusp function of `D.cusp`, realized by the smooth
vector `lineVec D f h`. We prove the decomposition of line-parabolic elements and the left
line-parabolic equivariance of `lineVec`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.HeckeEigen

section Decomposition

variable {R : Type*} [CommRing R]

theorem lineLevi_one_one : lineLevi (1 : Rˣ) (1 : GeneralLinearGroup (Fin 2) R) = 1 :=
  (lineLeviHom R).map_one

theorem lineLevi_mul (d e : Rˣ) (A B : GeneralLinearGroup (Fin 2) R) :
    lineLevi d A * lineLevi e B = lineLevi (d * e) (A * B) :=
  ((lineLeviHom R).map_mul (d, A) (e, B)).symm

/-- Conjugating the line radical by the `GL₂` Levi block. -/
theorem lineLevi_unipotent (A : GeneralLinearGroup (Fin 2) R) (a b : R) :
    ∃ a' b' : R, lineLevi 1 A * lineUnipotent a b = lineUnipotent a' b' * lineLevi 1 A := by
  set Ai := (A⁻¹).val with hAi
  have hinv : Ai * A.val = 1 := by rw [hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e00 := congrFun (congrFun hinv 0) 0
  have e01 := congrFun (congrFun hinv 0) 1
  have e10 := congrFun (congrFun hinv 1) 0
  have e11 := congrFun (congrFun hinv 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e01 e10
  refine ⟨a * Ai 0 0 + b * Ai 1 0, a * Ai 0 1 + b * Ai 1 1, ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, lineLevi_val]
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination a * e00 + b * e10
    | linear_combination (-a) * e00 + (-b) * e10
    | linear_combination a * e01 + b * e11
    | linear_combination (-a) * e01 + (-b) * e11

/-- Decomposition of a line-parabolic element into radical, scalar and `GL₂` Levi factors. -/
theorem line_matrix_decomposition (X y : Matrix (Fin 3) (Fin 3) R) (h1 : X * y = 1)
    (h2 : y * X = 1) (hx1 : X 1 0 = 0) (hx2 : X 2 0 = 0) (hy1 : y 1 0 = 0) (hy2 : y 2 0 = 0) :
    ∃ (a b : R) (d : Rˣ) (B : GeneralLinearGroup (Fin 2) R),
      X = (lineUnipotent a b * (lineLevi d 1 * lineLevi 1 B)).val := by
  have m1 : ∀ i j, X i 0 * y 0 j + X i 1 * y 1 j + X i 2 * y 2 j =
      (1 : Matrix (Fin 3) (Fin 3) R) i j := fun i j => by
    rw [← h1, Matrix.mul_apply, Fin.sum_univ_three]
  have m2 : ∀ i j, y i 0 * X 0 j + y i 1 * X 1 j + y i 2 * X 2 j =
      (1 : Matrix (Fin 3) (Fin 3) R) i j := fun i j => by
    rw [← h2, Matrix.mul_apply, Fin.sum_univ_three]
  have hd1 : X 0 0 * y 0 0 = 1 := by
    have := m1 0 0; rw [hy1, hy2, mul_zero, mul_zero, add_zero, add_zero] at this
    simpa using this
  let d : Rˣ := ⟨X 0 0, y 0 0, hd1, by rw [mul_comm]; exact hd1⟩
  let B : GeneralLinearGroup (Fin 2) R :=
    ⟨Matrix.of fun i j => X i.succ j.succ, Matrix.of fun i j => y i.succ j.succ, by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply]
      have := m1 i.succ j.succ
      fin_cases i <;> fin_cases j <;>
        simpa [hx1, hx2] using this, by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply]
      have := m2 i.succ j.succ
      fin_cases i <;> fin_cases j <;>
        simpa [hy1, hy2] using this⟩
  have e11 : y 1 1 * X 1 1 + y 1 2 * X 2 1 = 1 := by simpa [hy1] using m2 1 1
  have e21 : y 2 1 * X 1 1 + y 2 2 * X 2 1 = 0 := by simpa [hy2] using m2 2 1
  have e12 : y 1 1 * X 1 2 + y 1 2 * X 2 2 = 0 := by simpa [hy1] using m2 1 2
  have e22 : y 2 1 * X 1 2 + y 2 2 * X 2 2 = 1 := by simpa [hy2] using m2 2 2
  refine ⟨X 0 1 * y 1 1 + X 0 2 * y 2 1, X 0 1 * y 1 2 + X 0 2 * y 2 2, d, B, ?_⟩
  rw [Units.val_mul, Units.val_mul, lineLevi_val, lineLevi_val]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three, d, B, hx1, hx2] <;>
    first
    | linear_combination X 0 1 * e11 + X 0 2 * e21
    | linear_combination (-X 0 1) * e11 + (-X 0 2) * e21
    | linear_combination X 0 1 * e12 + X 0 2 * e22
    | linear_combination (-X 0 1) * e12 + (-X 0 2) * e22

/-- Decomposition of a line-parabolic element into radical, scalar and `GL₂` Levi factors. -/
theorem lineParabolic_exists_decomposition (x : GL3 R) (hx : x ∈ lineParabolic R) :
    ∃ (a b : R) (d : Rˣ) (B : GeneralLinearGroup (Fin 2) R),
      x = lineUnipotent a b * (lineLevi d 1 * lineLevi 1 B) := by
  have hi := inLine_inv hx
  obtain ⟨a, b, d, B, h⟩ := line_matrix_decomposition x.val (x⁻¹).val
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hx.1 hx.2 hi.1 hi.2
  exact ⟨a, b, d, B, Units.ext h⟩

/-- The `GL₂` block of a line decomposition is the lower-right block. -/
theorem lineDecomp_block (a b : R) (d : Rˣ) (B : GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    (lineUnipotent a b * (lineLevi d 1 * lineLevi 1 B)).val i.succ j.succ = B.val i j := by
  rw [Units.val_mul, Units.val_mul, lineLevi_val, lineLevi_val]
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

end Decomposition

variable {n : ℕ} (D : InducingData n)

/-- The line cohomological exponent `(n+3)/2 - (1/2 - s/3)` at `s = -3/2`. -/
def lineExp (n : ℕ) : ℂ := ((n : ℂ) + 3) / 2 - inductionExponent .line cohomologicalPoint

/-- The cusp function attached to a line-induced section at a point. -/
def lineCusp (n : ℕ) (f : AdelicGL → ℂ) (h : AdelicGL) : BinaryAdelicGL → ℂ :=
  fun A => normPower (GeneralLinearGroup.det A) (-lineExp n) * f (lineLevi 1 A * h)

theorem lineCusp_mem {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (h : AdelicGL) : lineCusp n f h ∈ cuspFunctions D.cusp :=
  hf.2.2.2.2.2 h

open Classical in
/-- The smooth vector realizing `lineCusp n f h`. -/
def lineVec (f : AdelicGL → ℂ) (h : AdelicGL) : D.cusp.smooth :=
  if hm : lineCusp n f h ∈ cuspFunctions D.cusp then (LinearMap.mem_range.mp hm).choose else 0

variable {D}

theorem realize_lineVec {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (h : AdelicGL) : D.cusp.realize (lineVec D f h) = lineCusp n f h := by
  have hm := lineCusp_mem D hf h
  rw [lineVec, dite_eq_left hm]
  exact (LinearMap.mem_range.mp hm).choose_spec

theorem lineVec_eq {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (h : AdelicGL) (w : D.cusp.smooth) (hw : D.cusp.realize w = lineCusp n f h) :
    lineVec D f h = w :=
  D.cusp.injective ((realize_lineVec hf h).trans hw.symm)

theorem lineVec_value {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (h : AdelicGL) : f h = D.cusp.realize (lineVec D f h) 1 := by
  rw [realize_lineVec hf h, lineCusp, map_one, np_one, one_mul, lineLevi_one_one, one_mul]

theorem lineVec_level {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (h : AdelicGL) (k : finiteLevel) : lineVec D f (h * atFinite k.val) = lineVec D f h := by
  apply lineVec_eq hf
  rw [realize_lineVec hf]
  funext A
  simp only [lineCusp]
  rw [← mul_assoc, hf.2.1 k]

/-- **Left line-parabolic equivariance of the realizing vectors.** -/
theorem lineVec_parabolic {f : AdelicGL → ℂ} (hf : IsInduced D .line cohomologicalPoint f)
    (a b : Adeles) (s : Adelesˣ) (B : BinaryAdelicGL) (h : AdelicGL) :
    lineVec D f (lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) * h) =
      (D.chi.toMonoidHom s * normPower s (2 * inductionExponent .line cohomologicalPoint) *
        normPower (GeneralLinearGroup.det B) (lineExp n)) •
      ⟨D.cusp.π B (lineVec D f h), D.cusp.smooth_stable B _ (lineVec D f h).property⟩ := by
  apply lineVec_eq hf
  funext A
  rw [map_smul, Pi.smul_apply, D.cusp.equivariant, realize_lineVec hf, smul_eq_mul]
  simp only [lineCusp]
  obtain ⟨a', b', hab⟩ := lineLevi_unipotent A a b
  have hcomm : lineLevi 1 A * (lineLevi s 1 * lineLevi 1 B) = lineLevi s 1 * lineLevi 1 (A * B) := by
    rw [← mul_assoc, lineLevi_mul, lineLevi_mul, lineLevi_mul]
    simp
  have h1 : lineLevi 1 A * (lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) * h) =
      lineUnipotent a' b' * (lineLevi s 1 * (lineLevi 1 (A * B) * h)) := by
    calc lineLevi 1 A * (lineUnipotent a b * (lineLevi s 1 * lineLevi 1 B) * h)
        = (lineLevi 1 A * lineUnipotent a b) * (lineLevi s 1 * lineLevi 1 B) * h := by
          simp only [mul_assoc]
      _ = lineUnipotent a' b' * (lineLevi 1 A * (lineLevi s 1 * lineLevi 1 B)) * h := by
          rw [hab]; simp only [mul_assoc]
      _ = lineUnipotent a' b' * (lineLevi s 1 * (lineLevi 1 (A * B) * h)) := by
          rw [hcomm]; simp only [mul_assoc]
  rw [h1, hf.2.2.2.1, hf.2.2.2.2.1, map_mul, np_mul]
  have key := np_neg (GeneralLinearGroup.det B) (lineExp n)
  linear_combination (D.chi.toMonoidHom s *
    normPower s (2 * inductionExponent .line cohomologicalPoint) *
    normPower (GeneralLinearGroup.det A) (-lineExp n) *
    f (lineLevi 1 (A * B) * h)) * key

end TernaryPeriodPolynomials.HeckeEigen
