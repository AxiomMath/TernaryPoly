module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Rotations
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.Smooth
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SobolevSeminorms
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Height
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.AveragingSmooth
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.Module

@[expose] public section


/-!
# The archimedean vector-valued section of the line parabolic, via K-types

Given a real Iwasawa decomposition `g = b(g) k(g)` adapted to the line parabolic
(`LineIwasawaData`) and a weight vector `w` of a cuspidal representation `σ`, we build the
`σ`-valued function
`g ↦ χ(b(g)) · σ(block b(g)) · Φ(k(g))`, where `Φ` is the `M_K`-equivariant K-type polynomial
`Φ(κ) = κ₁₁^e · ((κ₂₂ - i κ₃₂)^m w₋ + (κ₂₂ + i κ₃₂)^m w₊)`.
It satisfies `Ψ(p g) = χ(p) σ(block p) Ψ(g)` for `p` in the line parabolic, is real-analytic in
`g`, and its smooth-vector version has scalar realizations that are real-analytic in `g`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (binaryRotations invertibleMatrix_val smooth_one_contDiffOn)
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## Iwasawa data -/

/-- A real Iwasawa decomposition `g = B g * K g` of `GL₃(ℝ)` relative to the line parabolic:
`B g` lies in the line parabolic with positive corner and positive block determinant, `K g` is
orthogonal, the decomposition is equivariant for the line parabolic, and both factors are
real-analytic in the matrix entries. -/
structure LineIwasawaData where
  B : RealGL3 → RealGL3
  K : RealGL3 → RealGL3
  mul_eq : ∀ g, B g * K g = g
  B_mem : ∀ g, B g ∈ lineParabolic ℝ
  B_corner_pos : ∀ g, 0 < (B g).val 0 0
  B_block_pos : ∀ g, 0 < (B g).val 1 1 * (B g).val 2 2 - (B g).val 1 2 * (B g).val 2 1
  K_orth : ∀ g, (K g).val.transpose * (K g).val = 1
  B_one : B 1 = 1
  K_one : K 1 = 1
  equivariant : ∀ p ∈ lineParabolic ℝ, ∀ g, ∃ m : RealGL3, m ∈ lineParabolic ℝ ∧
    m.val.transpose * m.val = 1 ∧ K (p * g) = m * K g ∧ B (p * g) = p * B g * m⁻¹
  B_analytic : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => (B (invertibleMatrix A)).val)
    {A | A.det ≠ 0}
  K_analytic : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => (K (invertibleMatrix A)).val)
    {A | A.det ≠ 0}

/-! ## Representation-theoretic bookkeeping -/

section Representation

variable (σ : CuspidalRepresentation)

theorem rep_atInfinity_mul (g h : BinaryRealGL) (v : σ.H) :
    σ.π (atInfinity (g * h)) v = σ.π (atInfinity g) (σ.π (atInfinity h) v) := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  exact congrArg (fun f : σ.H →ₗ[ℂ] σ.H => f v) (map_mul σ.π (atInfinity g) (atInfinity h))

theorem rep_atInfinity_one (v : σ.H) : σ.π (atInfinity (1 : BinaryRealGL)) v = v := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one]
  exact congrArg (fun f : σ.H →ₗ[ℂ] σ.H => f v) (map_one σ.π)

end Representation

/-! ## The reflection and the rotations -/

/-- The reflection `diag(1, -1)` of `GL₂(ℝ)`. -/
def binaryReflection : BinaryRealGL where
  val := !![1, 0; 0, -1]
  inv := !![1, 0; 0, -1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryReflection_val : binaryReflection.val = !![1, 0; 0, -1] := rfl

theorem binaryRotations_val (a : Circle) :
    (binaryRotations a).val = !![(a : ℂ).re, -(a : ℂ).im; (a : ℂ).im, (a : ℂ).re] := rfl

theorem binaryRotations_inv_val (a : Circle) :
    ((binaryRotations a)⁻¹).val = !![(a : ℂ).re, (a : ℂ).im; -(a : ℂ).im, (a : ℂ).re] := rfl

theorem binaryReflection_mul_self : binaryReflection * binaryReflection = 1 := by
  apply Units.ext
  rw [Units.val_mul, binaryReflection_val, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rotation_mul_reflection (a : Circle) :
    binaryRotations a * binaryReflection = binaryReflection * (binaryRotations a)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, binaryRotations_val, binaryRotations_inv_val,
    binaryReflection_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_binaryRotations (a : Circle) : (binaryRotations a).val.det = 1 := by
  rw [binaryRotations_val, Matrix.det_fin_two_of]
  have h := Circle.normSq_coe a
  rw [Complex.normSq_apply] at h
  linear_combination h

/-- The point of the circle with coordinates `(p, r)` when `p² + r² = 1`. -/
def circleOfXY (p r : ℝ) (h : p * p + r * r = 1) : Circle :=
  ⟨(p : ℂ) + (r : ℂ) * Complex.I, by
    have h2 : ‖(p : ℂ) + (r : ℂ) * Complex.I‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
      linarith
    have h3 : ‖(p : ℂ) + (r : ℂ) * Complex.I‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
    simpa [Submonoid.unitSphere] using h3⟩

theorem circleOfXY_re (p r : ℝ) (h : p * p + r * r = 1) : ((circleOfXY p r h : Circle) : ℂ).re = p := by
  change ((p : ℂ) + (r : ℂ) * Complex.I).re = p
  simp

theorem circleOfXY_im (p r : ℝ) (h : p * p + r * r = 1) : ((circleOfXY p r h : Circle) : ℂ).im = r := by
  change ((p : ℂ) + (r : ℂ) * Complex.I).im = r
  simp

/-- Every orthogonal real `2 × 2` matrix is a rotation, possibly composed with the reflection. -/
theorem orthogonal_binary (A : BinaryRealGL) (ho : A.val.transpose * A.val = 1) :
    ∃ a : Circle, A = binaryRotations a ∨ A = binaryRotations a * binaryReflection := by
  have h1 : A.val 0 0 * A.val 0 0 + A.val 1 0 * A.val 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun ho 0) 0
  have h2 : A.val 0 1 * A.val 0 1 + A.val 1 1 * A.val 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun ho 1) 1
  have h3 : A.val 0 0 * A.val 0 1 + A.val 1 0 * A.val 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun ho 0) 1
  have hd : (A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0) *
      (A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0) = 1 := by
    linear_combination (A.val 0 1 * A.val 0 1 + A.val 1 1 * A.val 1 1) * h1 + h2 -
      (A.val 0 0 * A.val 0 1 + A.val 1 0 * A.val 1 1) * h3
  obtain ⟨a, ha_re, ha_im⟩ :
      ∃ a : Circle, (a : ℂ).re = A.val 0 0 ∧ (a : ℂ).im = A.val 1 0 :=
    ⟨circleOfXY (A.val 0 0) (A.val 1 0) h1, circleOfXY_re _ _ h1, circleOfXY_im _ _ h1⟩
  refine ⟨a, ?_⟩
  rcases mul_self_eq_one_iff.1 hd with hd1 | hd1
  · left
    have hq : A.val 0 1 = -A.val 1 0 := by
      linear_combination A.val 0 0 * h3 - A.val 1 0 * hd1 - A.val 0 1 * h1
    have hs : A.val 1 1 = A.val 0 0 := by
      linear_combination A.val 1 0 * h3 + A.val 0 0 * hd1 - A.val 1 1 * h1
    apply Units.ext
    rw [binaryRotations_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha_re, ha_im, hq, hs]
  · right
    have hq : A.val 0 1 = A.val 1 0 := by
      linear_combination A.val 0 0 * h3 - A.val 1 0 * hd1 - A.val 0 1 * h1
    have hs : A.val 1 1 = -A.val 0 0 := by
      linear_combination A.val 1 0 * h3 + A.val 0 0 * hd1 - A.val 1 1 * h1
    apply Units.ext
    rw [Units.val_mul, binaryRotations_val, binaryReflection_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha_re, ha_im, hq, hs]

/-! ## The Levi projections of the line parabolic -/

/-- The corner (Levi `GL₁`) entry. -/
def lineCorner (p : RealGL3) : ℝ := p.val 0 0

/-- The lower right `2 × 2` block of a `3 × 3` matrix. -/
def lineBlockMatrix (p : RealGL3) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => p.val i.succ j.succ

@[simp] theorem lineBlockMatrix_apply_zero_zero (p : RealGL3) :
    lineBlockMatrix p 0 0 = p.val 1 1 := rfl
@[simp] theorem lineBlockMatrix_apply_zero_one (p : RealGL3) :
    lineBlockMatrix p 0 1 = p.val 1 2 := rfl
@[simp] theorem lineBlockMatrix_apply_one_zero (p : RealGL3) :
    lineBlockMatrix p 1 0 = p.val 2 1 := rfl
@[simp] theorem lineBlockMatrix_apply_one_one (p : RealGL3) :
    lineBlockMatrix p 1 1 = p.val 2 2 := rfl

/-- The block (Levi `GL₂`) component, as an element of `GL₂(ℝ)` (the identity when the block is
singular). -/
def lineBlock (p : RealGL3) : BinaryRealGL := invertibleMatrix (lineBlockMatrix p)

theorem lineParabolic_entries {p : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    p.val 1 0 = 0 ∧ p.val 2 0 = 0 := hp

theorem lineParabolic_det {p : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    p.val.det = p.val 0 0 * (p.val 1 1 * p.val 2 2 - p.val 1 2 * p.val 2 1) := by
  obtain ⟨h1, h2⟩ := lineParabolic_entries hp
  rw [Matrix.det_fin_three, h1, h2]
  ring

theorem lineBlockMatrix_det (p : RealGL3) :
    (lineBlockMatrix p).det = p.val 1 1 * p.val 2 2 - p.val 1 2 * p.val 2 1 := by
  exact Matrix.det_fin_two (lineBlockMatrix p)

theorem lineCorner_ne_zero {p : RealGL3} (hp : p ∈ lineParabolic ℝ) : lineCorner p ≠ 0 := by
  intro h
  apply Matrix.GeneralLinearGroup.det_ne_zero p
  have h' : p.val 0 0 = 0 := h
  rw [lineParabolic_det hp, h', zero_mul]

theorem lineBlockMatrix_det_ne_zero {p : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    (lineBlockMatrix p).det ≠ 0 := by
  intro h
  apply Matrix.GeneralLinearGroup.det_ne_zero p
  rw [lineBlockMatrix_det] at h
  rw [lineParabolic_det hp, h, mul_zero]

theorem lineBlock_val {p : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    (lineBlock p).val = lineBlockMatrix p :=
  invertibleMatrix_val _ (lineBlockMatrix_det_ne_zero hp)

theorem lineBlock_det {p : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    (lineBlock p).val.det = p.val 1 1 * p.val 2 2 - p.val 1 2 * p.val 2 1 := by
  rw [lineBlock_val hp, lineBlockMatrix_det]

theorem lineBlock_det_ne_zero (p : RealGL3) : (lineBlock p).val.det ≠ 0 :=
  Matrix.GeneralLinearGroup.det_ne_zero (lineBlock p)

theorem lineCorner_mul {p q : RealGL3} (_ : p ∈ lineParabolic ℝ) (hq : q ∈ lineParabolic ℝ) :
    lineCorner (p * q) = lineCorner p * lineCorner q := by
  obtain ⟨h1, h2⟩ := lineParabolic_entries hq
  simp [lineCorner, Matrix.mul_apply, Fin.sum_univ_three, h1, h2]

theorem lineBlockMatrix_mul {p q : RealGL3} (hp : p ∈ lineParabolic ℝ) :
    lineBlockMatrix (p * q) = lineBlockMatrix p * lineBlockMatrix q := by
  obtain ⟨h1, h2⟩ := lineParabolic_entries hp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h1, h2]

theorem lineBlock_mul {p q : RealGL3} (hp : p ∈ lineParabolic ℝ) (hq : q ∈ lineParabolic ℝ) :
    lineBlock (p * q) = lineBlock p * lineBlock q := by
  have hpq : p * q ∈ lineParabolic ℝ := mul_mem hp hq
  apply Units.ext
  rw [Units.val_mul, lineBlock_val hpq, lineBlock_val hp, lineBlock_val hq,
    lineBlockMatrix_mul hp]

theorem lineCorner_one : lineCorner 1 = 1 := by
  simp [lineCorner]

theorem lineBlock_one : lineBlock 1 = 1 := by
  apply Units.ext
  rw [lineBlock_val (one_mem (lineParabolic ℝ))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem lineBlock_inv {m0 : RealGL3} (hm : m0 ∈ lineParabolic ℝ) :
    lineBlock m0⁻¹ = (lineBlock m0)⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (by rw [← lineBlock_mul (inv_mem hm) hm, inv_mul_cancel, lineBlock_one])

/-- An orthogonal element of the line parabolic is block diagonal, with corner `±1` and an
orthogonal block. -/
theorem lineParabolic_orth {m0 : RealGL3} (hp : m0 ∈ lineParabolic ℝ)
    (ho : m0.val.transpose * m0.val = 1) :
    m0.val 0 1 = 0 ∧ m0.val 0 2 = 0 ∧ (m0.val 0 0 = 1 ∨ m0.val 0 0 = -1) ∧
      (lineBlock m0).val.transpose * (lineBlock m0).val = 1 := by
  obtain ⟨h10, h20⟩ := lineParabolic_entries hp
  have d00 : m0.val 0 0 * m0.val 0 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using congrFun (congrFun ho 0) 0
  have d01 : m0.val 0 0 * m0.val 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using congrFun (congrFun ho 0) 1
  have d02 : m0.val 0 0 * m0.val 0 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h10, h20] using congrFun (congrFun ho 0) 2
  have d11 : m0.val 0 1 * m0.val 0 1 + m0.val 1 1 * m0.val 1 1 + m0.val 2 1 * m0.val 2 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun ho 1) 1
  have d12 : m0.val 0 1 * m0.val 0 2 + m0.val 1 1 * m0.val 1 2 + m0.val 2 1 * m0.val 2 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun ho 1) 2
  have d22 : m0.val 0 2 * m0.val 0 2 + m0.val 1 2 * m0.val 1 2 + m0.val 2 2 * m0.val 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun ho 2) 2
  have hm00 : m0.val 0 0 ≠ 0 := by
    intro h
    rw [h] at d00
    norm_num at d00
  have h01 : m0.val 0 1 = 0 := (mul_eq_zero.1 d01).resolve_left hm00
  have h02 : m0.val 0 2 = 0 := (mul_eq_zero.1 d02).resolve_left hm00
  refine ⟨h01, h02, mul_self_eq_one_iff.1 d00, ?_⟩
  rw [h01] at d11
  rw [h01, h02] at d12
  rw [h02] at d22
  rw [lineBlock_val hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-! ## The scalar factors -/

section Factors

variable (e : ℕ) (α β : ℂ)

/-- The corner character `sgn(t)^e |t|^α`. -/
def cornerFactor (t : ℝ) : ℂ :=
  (if t < 0 then (-1 : ℂ) else 1) ^ e * Complex.exp (α * (Real.log |t| : ℝ))

/-- The block-determinant character `|t|^β`. -/
def blockFactor (t : ℝ) : ℂ := Complex.exp (β * (Real.log |t| : ℝ))

theorem negOneIf_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (if a * b < 0 then (-1 : ℂ) else 1) =
      (if a < 0 then (-1 : ℂ) else 1) * (if b < 0 then (-1 : ℂ) else 1) := by
  rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
  · rw [ite_eq_right (not_lt.2 (mul_pos_of_neg_of_neg ha' hb').le), ite_eq_left ha', ite_eq_left hb']
    norm_num
  · rw [ite_eq_left (mul_neg_of_neg_of_pos ha' hb'), ite_eq_left ha', ite_eq_right (not_lt.2 hb'.le)]
    norm_num
  · rw [ite_eq_left (mul_neg_of_pos_of_neg ha' hb'), ite_eq_right (not_lt.2 ha'.le), ite_eq_left hb']
    norm_num
  · rw [ite_eq_right (not_lt.2 (mul_pos ha' hb').le), ite_eq_right (not_lt.2 ha'.le),
      ite_eq_right (not_lt.2 hb'.le)]
    norm_num

theorem cornerFactor_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    cornerFactor e α (a * b) = cornerFactor e α a * cornerFactor e α b := by
  unfold cornerFactor
  rw [negOneIf_mul ha hb, mul_pow, abs_mul, Real.log_mul (abs_ne_zero.2 ha) (abs_ne_zero.2 hb)]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem blockFactor_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    blockFactor β (a * b) = blockFactor β a * blockFactor β b := by
  unfold blockFactor
  rw [abs_mul, Real.log_mul (abs_ne_zero.2 ha) (abs_ne_zero.2 hb)]
  push_cast
  rw [mul_add, Complex.exp_add]

theorem cornerFactor_one : cornerFactor e α 1 = 1 := by
  unfold cornerFactor
  rw [ite_eq_right (show ¬ ((1 : ℝ) < 0) by norm_num), abs_one, Real.log_one]
  simp

theorem cornerFactor_neg_one : cornerFactor e α (-1) = (-1) ^ e := by
  unfold cornerFactor
  rw [ite_eq_left (show ((-1 : ℝ) < 0) by norm_num), abs_neg, abs_one, Real.log_one]
  simp

theorem blockFactor_one : blockFactor β 1 = 1 := by
  unfold blockFactor
  rw [abs_one, Real.log_one]
  simp

theorem blockFactor_neg_one : blockFactor β (-1) = 1 := by
  unfold blockFactor
  rw [abs_neg, abs_one, Real.log_one]
  simp

theorem cornerFactor_pm1 {c : ℝ} (hc : c = 1 ∨ c = -1) : cornerFactor e α c = (c : ℂ) ^ e := by
  rcases hc with rfl | rfl
  · rw [cornerFactor_one]
    simp
  · rw [cornerFactor_neg_one]
    simp

theorem cornerFactor_of_pos {t : ℝ} (ht : 0 < t) :
    cornerFactor e α t = Complex.exp (α * (Real.log t : ℝ)) := by
  unfold cornerFactor
  rw [ite_eq_right (not_lt.2 ht.le), abs_of_pos ht]
  simp

theorem blockFactor_of_pos {t : ℝ} (ht : 0 < t) :
    blockFactor β t = Complex.exp (β * (Real.log t : ℝ)) := by
  unfold blockFactor
  rw [abs_of_pos ht]

/-- The character of the line Levi: corner character times block-determinant character. -/
def leviFactor (p : RealGL3) : ℂ :=
  cornerFactor e α (lineCorner p) * blockFactor β (lineBlock p).val.det

theorem leviFactor_mul {p q : RealGL3} (hp : p ∈ lineParabolic ℝ) (hq : q ∈ lineParabolic ℝ) :
    leviFactor e α β (p * q) = leviFactor e α β p * leviFactor e α β q := by
  have hdet : (lineBlock (p * q)).val.det = (lineBlock p).val.det * (lineBlock q).val.det := by
    rw [lineBlock_mul hp hq, Units.val_mul, Matrix.det_mul]
  unfold leviFactor
  rw [lineCorner_mul hp hq, hdet,
    cornerFactor_mul e α (lineCorner_ne_zero hp) (lineCorner_ne_zero hq),
    blockFactor_mul β (lineBlock_det_ne_zero p) (lineBlock_det_ne_zero q)]
  ring

theorem leviFactor_one : leviFactor e α β 1 = 1 := by
  unfold leviFactor
  rw [lineCorner_one, lineBlock_one, cornerFactor_one, Units.val_one, Matrix.det_one,
    blockFactor_one, mul_one]

theorem leviFactor_inv_mul {m0 : RealGL3} (hm : m0 ∈ lineParabolic ℝ) :
    leviFactor e α β m0⁻¹ * leviFactor e α β m0 = 1 := by
  rw [← leviFactor_mul e α β (inv_mem hm) hm, inv_mul_cancel, leviFactor_one]

/-- On an orthogonal element of the line parabolic the Levi character is the corner character. -/
theorem leviFactor_orth {m0 : RealGL3} (hp : m0 ∈ lineParabolic ℝ)
    (ho : m0.val.transpose * m0.val = 1) :
    leviFactor e α β m0 = cornerFactor e α (m0.val 0 0) := by
  have hBo := (lineParabolic_orth hp ho).2.2.2
  have hdet : (lineBlock m0).val.det * (lineBlock m0).val.det = 1 := by
    have h := congrArg Matrix.det hBo
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hb : blockFactor β (lineBlock m0).val.det = 1 := by
    rcases mul_self_eq_one_iff.1 hdet with h | h
    · rw [h]
      exact blockFactor_one β
    · rw [h]
      exact blockFactor_neg_one β
  unfold leviFactor lineCorner
  rw [hb, mul_one]

end Factors

/-! ## Weight vectors and the K-type polynomial -/

section KType

variable (σ : CuspidalRepresentation) (m e : ℕ) (α β : ℂ) (w : σ.H)

/-- The weight-`+m` vector `σ(ε) w` obtained from the weight-`-m` vector `w`. -/
def wPlus : σ.H := σ.π (atInfinity binaryReflection) w

theorem wPlus_mem (hw : w ∈ σ.smooth) : wPlus σ w ∈ σ.smooth := by
  unfold wPlus
  exact σ.smooth_stable _ _ hw

/-- `w` has weight `-m` for the rotation group. -/
abbrev RotationWeight : Prop :=
  ∀ a : Circle, σ.π (atInfinity (binaryRotations a)) w = ((a : ℂ) ^ (-(m : ℤ))) • w

/-- The K-type polynomial in the coordinates `(κ₁₁, κ₂₂, κ₃₂)`. -/
def kVec (t u v : ℝ) : σ.H :=
  (t : ℂ) ^ e • (((u : ℂ) - Complex.I * (v : ℂ)) ^ m • w +
    ((u : ℂ) + Complex.I * (v : ℂ)) ^ m • wPlus σ w)

/-- The K-part `Φ(κ)`. -/
def kPart (κ : RealGL3) : σ.H :=
  (((κ.val 0 0 : ℝ) : ℂ)) ^ e • ((((κ.val 1 1 : ℝ) : ℂ) - Complex.I * ((κ.val 2 1 : ℝ) : ℂ)) ^ m • w +
    (((κ.val 1 1 : ℝ) : ℂ) + Complex.I * ((κ.val 2 1 : ℝ) : ℂ)) ^ m • wPlus σ w)

theorem kPart_eq_kVec (κ : RealGL3) :
    kPart σ m e w κ = kVec σ m e w (κ.val 0 0) (κ.val 1 1) (κ.val 2 1) := rfl

theorem kPart_mem (hw : w ∈ σ.smooth) (κ : RealGL3) : kPart σ m e w κ ∈ σ.smooth := by
  unfold kPart
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hw)
    (Submodule.smul_mem _ _ (wPlus_mem σ w hw)))

/-! ### Complex-number identities -/

theorem rot_aux_eq (x y u v : ℝ) :
    ((x * u - y * v : ℝ) : ℂ) + Complex.I * ((y * u + x * v : ℝ) : ℂ) =
      ((x : ℂ) + (y : ℂ) * Complex.I) * ((u : ℂ) + Complex.I * (v : ℂ)) := by
  push_cast
  linear_combination (-(y : ℂ) * (v : ℂ)) * Complex.I_sq

theorem rot_aux_eq' (x y u v : ℝ) :
    ((x * u - y * v : ℝ) : ℂ) - Complex.I * ((y * u + x * v : ℝ) : ℂ) =
      ((x : ℂ) - (y : ℂ) * Complex.I) * ((u : ℂ) - Complex.I * (v : ℂ)) := by
  push_cast
  linear_combination (-(y : ℂ) * (v : ℂ)) * Complex.I_sq

theorem refl_aux_eq (x y u v : ℝ) :
    ((x * u + y * v : ℝ) : ℂ) + Complex.I * ((y * u - x * v : ℝ) : ℂ) =
      ((x : ℂ) + (y : ℂ) * Complex.I) * ((u : ℂ) - Complex.I * (v : ℂ)) := by
  push_cast
  linear_combination ((y : ℂ) * (v : ℂ)) * Complex.I_sq

theorem refl_aux_eq' (x y u v : ℝ) :
    ((x * u + y * v : ℝ) : ℂ) - Complex.I * ((y * u - x * v : ℝ) : ℂ) =
      ((x : ℂ) - (y : ℂ) * Complex.I) * ((u : ℂ) + Complex.I * (v : ℂ)) := by
  push_cast
  linear_combination ((y : ℂ) * (v : ℂ)) * Complex.I_sq

theorem circle_conj_inv (a : Circle) :
    (((a : ℂ).re : ℝ) : ℂ) - (((a : ℂ).im : ℝ) : ℂ) * Complex.I = (a : ℂ)⁻¹ := by
  rw [Complex.inv_def, Circle.normSq_coe]
  apply Complex.ext <;> simp

theorem inv_mul_pow_aux (A z : ℂ) (n : ℕ) : (A⁻¹ * z) ^ n = A ^ (-(n : ℤ)) * z ^ n := by
  rw [mul_pow, inv_pow, zpow_neg, zpow_natCast]

/-! ### Rotations and the reflection act on the weight vectors -/

theorem rep_rotation_wPlus (hrot : RotationWeight σ m w) (a : Circle) :
    σ.π (atInfinity (binaryRotations a)) (wPlus σ w) = ((a : ℂ) ^ m) • wPlus σ w := by
  unfold wPlus
  have h1 : σ.π (atInfinity (binaryRotations a)) (σ.π (atInfinity binaryReflection) w) =
      σ.π (atInfinity binaryReflection) (σ.π (atInfinity (binaryRotations a)⁻¹) w) := by
    rw [← rep_atInfinity_mul, rotation_mul_reflection, rep_atInfinity_mul]
  have hc : ((a⁻¹ : Circle) : ℂ) ^ (-(m : ℤ)) = (a : ℂ) ^ m := by
    rw [Circle.coe_inv, zpow_neg, zpow_natCast, inv_pow, inv_inv]
  rw [h1, ← map_inv binaryRotations a, hrot a⁻¹, map_smul, hc]

theorem rep_reflection_rotation_w (hrot : RotationWeight σ m w) (a : Circle) :
    σ.π (atInfinity (binaryRotations a * binaryReflection)) w = ((a : ℂ) ^ m) • wPlus σ w := by
  rw [rep_atInfinity_mul]
  exact rep_rotation_wPlus σ m w hrot a

theorem rep_reflection_rotation_wPlus (hrot : RotationWeight σ m w) (a : Circle) :
    σ.π (atInfinity (binaryRotations a * binaryReflection)) (wPlus σ w) =
      ((a : ℂ) ^ (-(m : ℤ))) • w := by
  unfold wPlus
  rw [rep_atInfinity_mul, ← rep_atInfinity_mul σ binaryReflection binaryReflection,
    binaryReflection_mul_self, rep_atInfinity_one, hrot a]

/-! ### Equivariance of the K-type polynomial -/

theorem kVec_rot (hrot : RotationWeight σ m w) (a : Circle) {c : ℝ} (hc : c = 1 ∨ c = -1)
    (t u v : ℝ) :
    kVec σ m e w (c * t) ((a : ℂ).re * u - (a : ℂ).im * v) ((a : ℂ).im * u + (a : ℂ).re * v) =
      cornerFactor e α c • σ.π (atInfinity (binaryRotations a)) (kVec σ m e w t u v) := by
  have hcf := cornerFactor_pm1 e α hc
  have hconj := circle_conj_inv a
  have hA := Complex.re_add_im (a : ℂ)
  have hwp := rep_rotation_wPlus σ m w hrot a
  unfold kVec
  rw [rot_aux_eq, rot_aux_eq', hA, hconj]
  simp only [map_add, map_smul, hrot a, hwp]
  rw [hcf, inv_mul_pow_aux]
  push_cast
  simp only [mul_pow]
  module

theorem kVec_refl (hrot : RotationWeight σ m w) (a : Circle) {c : ℝ} (hc : c = 1 ∨ c = -1)
    (t u v : ℝ) :
    kVec σ m e w (c * t) ((a : ℂ).re * u + (a : ℂ).im * v) ((a : ℂ).im * u - (a : ℂ).re * v) =
      cornerFactor e α c •
        σ.π (atInfinity (binaryRotations a * binaryReflection)) (kVec σ m e w t u v) := by
  have hcf := cornerFactor_pm1 e α hc
  have hconj := circle_conj_inv a
  have hA := Complex.re_add_im (a : ℂ)
  have h1 := rep_reflection_rotation_w σ m w hrot a
  have h2 := rep_reflection_rotation_wPlus σ m w hrot a
  unfold kVec
  rw [refl_aux_eq, refl_aux_eq', hA, hconj]
  simp only [map_add, map_smul, h1, h2]
  rw [hcf, inv_mul_pow_aux]
  push_cast
  simp only [mul_pow]
  module

/-- **(a) Equivariance of the K-part** under orthogonal elements of the line parabolic. -/
theorem kPart_equivariant (hrot : RotationWeight σ m w) {m0 κ : RealGL3}
    (hp : m0 ∈ lineParabolic ℝ) (ho : m0.val.transpose * m0.val = 1) :
    kPart σ m e w (m0 * κ) =
      leviFactor e α β m0 • σ.π (atInfinity (lineBlock m0)) (kPart σ m e w κ) := by
  obtain ⟨h10, h20⟩ := lineParabolic_entries hp
  obtain ⟨h01, h02, hc, hBo⟩ := lineParabolic_orth hp ho
  rw [leviFactor_orth e α β hp ho]
  have e00 : (m0 * κ).val 0 0 = m0.val 0 0 * κ.val 0 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02]
  have e11 : (m0 * κ).val 1 1 = m0.val 1 1 * κ.val 1 1 + m0.val 1 2 * κ.val 2 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10]
  have e21 : (m0 * κ).val 2 1 = m0.val 2 1 * κ.val 1 1 + m0.val 2 2 * κ.val 2 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20]
  obtain ⟨a, ha | ha⟩ := orthogonal_binary (lineBlock m0) hBo
  · have hv : lineBlockMatrix m0 =
        !![(a : ℂ).re, -(a : ℂ).im; (a : ℂ).im, (a : ℂ).re] := by
      rw [← lineBlock_val hp, ha, binaryRotations_val]
    have x11 : m0.val 1 1 = (a : ℂ).re := by
      exact congrFun (congrFun hv 0) 0
    have x12 : m0.val 1 2 = -(a : ℂ).im := by
      exact congrFun (congrFun hv 0) 1
    have x21 : m0.val 2 1 = (a : ℂ).im := by
      exact congrFun (congrFun hv 1) 0
    have x22 : m0.val 2 2 = (a : ℂ).re := by
      exact congrFun (congrFun hv 1) 1
    have hU : m0.val 1 1 * κ.val 1 1 + m0.val 1 2 * κ.val 2 1 =
        (a : ℂ).re * κ.val 1 1 - (a : ℂ).im * κ.val 2 1 := by
      rw [x11, x12]
      ring
    have hV : m0.val 2 1 * κ.val 1 1 + m0.val 2 2 * κ.val 2 1 =
        (a : ℂ).im * κ.val 1 1 + (a : ℂ).re * κ.val 2 1 := by
      rw [x21, x22]
    rw [ha]
    simp only [kPart_eq_kVec]
    rw [e00, e11, e21, hU, hV]
    exact kVec_rot σ m e α w hrot a hc _ _ _
  · have hv : lineBlockMatrix m0 =
        !![(a : ℂ).re, (a : ℂ).im; (a : ℂ).im, -(a : ℂ).re] := by
      rw [← lineBlock_val hp, ha, Units.val_mul, binaryRotations_val, binaryReflection_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have x11 : m0.val 1 1 = (a : ℂ).re := by
      exact congrFun (congrFun hv 0) 0
    have x12 : m0.val 1 2 = (a : ℂ).im := by
      exact congrFun (congrFun hv 0) 1
    have x21 : m0.val 2 1 = (a : ℂ).im := by
      exact congrFun (congrFun hv 1) 0
    have x22 : m0.val 2 2 = -(a : ℂ).re := by
      exact congrFun (congrFun hv 1) 1
    have hU : m0.val 1 1 * κ.val 1 1 + m0.val 1 2 * κ.val 2 1 =
        (a : ℂ).re * κ.val 1 1 + (a : ℂ).im * κ.val 2 1 := by
      rw [x11, x12]
    have hV : m0.val 2 1 * κ.val 1 1 + m0.val 2 2 * κ.val 2 1 =
        (a : ℂ).im * κ.val 1 1 - (a : ℂ).re * κ.val 2 1 := by
      rw [x21, x22]
      ring
    rw [ha]
    simp only [kPart_eq_kVec]
    rw [e00, e11, e21, hU, hV]
    exact kVec_refl σ m e α w hrot a hc _ _ _

/-! ## The section on `GL₃(ℝ)` -/

/-- **The archimedean line section** `g ↦ χ(b(g)) σ(block b(g)) Φ(k(g))`. Here
`χ(b) = cornerFactor (b₁₁) * blockFactor (det block b)`. -/
def lineSection (L : LineIwasawaData) (g : RealGL3) : σ.H :=
  leviFactor e α β (L.B g) • σ.π (atInfinity (lineBlock (L.B g))) (kPart σ m e w (L.K g))

/-- **(b) Equivariance** of the line section for the line parabolic. -/
theorem lineSection_equivariant (hrot : RotationWeight σ m w) (L : LineIwasawaData) {p : RealGL3}
    (hp : p ∈ lineParabolic ℝ) (g : RealGL3) :
    lineSection σ m e α β w L (p * g) =
      leviFactor e α β p • σ.π (atInfinity (lineBlock p)) (lineSection σ m e α β w L g) := by
  obtain ⟨n, hn, hno, hK, hB⟩ := L.equivariant p hp g
  have hBp : L.B g ∈ lineParabolic ℝ := L.B_mem g
  have hpB : p * L.B g ∈ lineParabolic ℝ := mul_mem hp hBp
  have hninv : n⁻¹ ∈ lineParabolic ℝ := inv_mem hn
  have hkp := kPart_equivariant σ m e α β w hrot (κ := L.K g) hn hno
  have hLev : leviFactor e α β (L.B (p * g)) =
      leviFactor e α β p * leviFactor e α β (L.B g) * leviFactor e α β n⁻¹ := by
    rw [hB, leviFactor_mul e α β hpB hninv, leviFactor_mul e α β hp hBp]
  have hBlk : lineBlock (L.B (p * g)) = lineBlock p * lineBlock (L.B g) * lineBlock n⁻¹ := by
    rw [hB, lineBlock_mul hpB hninv, lineBlock_mul hp hBp]
  have hinv : lineBlock n⁻¹ * lineBlock n = 1 := by
    rw [← lineBlock_mul hninv hn, inv_mul_cancel, lineBlock_one]
  have hLn := leviFactor_inv_mul e α β hn
  have hpi : ∀ v : σ.H, σ.π (atInfinity (lineBlock p * lineBlock (L.B g) * lineBlock n⁻¹)) v =
      σ.π (atInfinity (lineBlock p)) (σ.π (atInfinity (lineBlock (L.B g)))
        (σ.π (atInfinity (lineBlock n⁻¹)) v)) := fun v => by
    rw [rep_atInfinity_mul, rep_atInfinity_mul]
  have step : ∀ x : σ.H, σ.π (atInfinity (lineBlock n⁻¹))
      (leviFactor e α β n • σ.π (atInfinity (lineBlock n)) x) = leviFactor e α β n • x := fun x => by
    rw [map_smul, ← rep_atInfinity_mul, hinv, rep_atInfinity_one]
  unfold lineSection
  rw [hLev, hBlk, hK, hkp, hpi, step]
  simp only [map_smul, smul_smul]
  congr 1
  linear_combination (leviFactor e α β p * leviFactor e α β (L.B g)) * hLn

/-- **(c)** At the identity the section is `w₋ + w₊`. -/
theorem lineSection_one (L : LineIwasawaData) :
    lineSection σ m e α β w L 1 = w + wPlus σ w := by
  unfold lineSection
  rw [L.B_one, L.K_one, leviFactor_one, lineBlock_one, rep_atInfinity_one, one_smul]
  simp [kPart]

end KType

/-! ## Analyticity -/

section Analytic

/-- Real-analytic entries of the Iwasawa factors. -/
theorem B_entry_contDiffOn (L : LineIwasawaData) (i j : Fin 3) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => (L.B (invertibleMatrix A)).val i j)
      {A | A.det ≠ 0} :=
  contDiffOn_pi.mp (contDiffOn_pi.mp L.B_analytic i) j

theorem K_entry_contDiffOn (L : LineIwasawaData) (i j : Fin 3) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => (L.K (invertibleMatrix A)).val i j)
      {A | A.det ≠ 0} :=
  contDiffOn_pi.mp (contDiffOn_pi.mp L.K_analytic i) j

theorem contDiffOn_ofReal {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    {f : E → ℝ} (hf : ContDiffOn ℝ ⊤ f s) :
    ContDiffOn ℝ ⊤ (fun x => ((f x : ℝ) : ℂ)) s :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

/-- The corner character `exp(α log b₁₁)` as a function of the matrix entries. -/
def cornerScalar (L : LineIwasawaData) (α : ℂ) : Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun A =>
  Complex.exp (α * ((Real.log ((L.B (invertibleMatrix A)).val 0 0) : ℝ) : ℂ))

/-- The block-determinant character `exp(β log det)` as a function of the matrix entries. -/
def blockScalar (L : LineIwasawaData) (β : ℂ) : Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun A =>
  Complex.exp (β * ((Real.log ((L.B (invertibleMatrix A)).val 1 1 * (L.B (invertibleMatrix A)).val 2 2 -
    (L.B (invertibleMatrix A)).val 1 2 * (L.B (invertibleMatrix A)).val 2 1) : ℝ) : ℂ))

/-- The coefficient of `w₋` in the K-part, as a function of the matrix entries. -/
def kScalarMinus (L : LineIwasawaData) (m e : ℕ) : Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun A =>
  (((L.K (invertibleMatrix A)).val 0 0 : ℝ) : ℂ) ^ e *
    ((((L.K (invertibleMatrix A)).val 1 1 : ℝ) : ℂ) -
      Complex.I * (((L.K (invertibleMatrix A)).val 2 1 : ℝ) : ℂ)) ^ m

/-- The coefficient of `w₊` in the K-part, as a function of the matrix entries. -/
def kScalarPlus (L : LineIwasawaData) (m e : ℕ) : Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun A =>
  (((L.K (invertibleMatrix A)).val 0 0 : ℝ) : ℂ) ^ e *
    ((((L.K (invertibleMatrix A)).val 1 1 : ℝ) : ℂ) +
      Complex.I * (((L.K (invertibleMatrix A)).val 2 1 : ℝ) : ℂ)) ^ m

theorem cornerScalar_contDiffOn (L : LineIwasawaData) (α : ℂ) :
    ContDiffOn ℝ ⊤ (cornerScalar L α) {A | A.det ≠ 0} :=
  (contDiffOn_const.mul (contDiffOn_ofReal ((B_entry_contDiffOn L 0 0).log
    (fun A _ => (L.B_corner_pos (invertibleMatrix A)).ne')))).cexp

theorem blockScalar_contDiffOn (L : LineIwasawaData) (β : ℂ) :
    ContDiffOn ℝ ⊤ (blockScalar L β) {A | A.det ≠ 0} :=
  (contDiffOn_const.mul (contDiffOn_ofReal
    ((((B_entry_contDiffOn L 1 1).mul (B_entry_contDiffOn L 2 2)).sub
      ((B_entry_contDiffOn L 1 2).mul (B_entry_contDiffOn L 2 1))).log
      (fun A _ => (L.B_block_pos (invertibleMatrix A)).ne')))).cexp

theorem kScalarMinus_contDiffOn (L : LineIwasawaData) (m e : ℕ) :
    ContDiffOn ℝ ⊤ (kScalarMinus L m e) {A | A.det ≠ 0} :=
  ((contDiffOn_ofReal (K_entry_contDiffOn L 0 0)).pow e).mul
    (((contDiffOn_ofReal (K_entry_contDiffOn L 1 1)).sub
      (contDiffOn_const.mul (contDiffOn_ofReal (K_entry_contDiffOn L 2 1)))).pow m)

theorem kScalarPlus_contDiffOn (L : LineIwasawaData) (m e : ℕ) :
    ContDiffOn ℝ ⊤ (kScalarPlus L m e) {A | A.det ≠ 0} :=
  ((contDiffOn_ofReal (K_entry_contDiffOn L 0 0)).pow e).mul
    (((contDiffOn_ofReal (K_entry_contDiffOn L 1 1)).add
      (contDiffOn_const.mul (contDiffOn_ofReal (K_entry_contDiffOn L 2 1)))).pow m)

theorem lineBlockMatrix_contDiffOn (L : LineIwasawaData) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => lineBlockMatrix (L.B (invertibleMatrix A)))
      {A | A.det ≠ 0} :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => B_entry_contDiffOn L i.succ j.succ

variable (σ : CuspidalRepresentation)

/-- The orbit of a vector under the block of `B`, as a function of the matrix entries. -/
def blockOrbit (L : LineIwasawaData) (v : σ.H) : Matrix (Fin 3) (Fin 3) ℝ → σ.H := fun A =>
  σ.π (atInfinity (lineBlock (L.B (invertibleMatrix A)))) v

theorem blockOrbit_contDiffOn (L : LineIwasawaData) {v : σ.H} (hv : v ∈ σ.smooth) :
    ContDiffOn ℝ ⊤ (blockOrbit σ L v) {A | A.det ≠ 0} :=
  (TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms.smooth_orbit_contDiffOn
    σ ⟨v, hv⟩).comp (lineBlockMatrix_contDiffOn L)
    (fun A _ => lineBlockMatrix_det_ne_zero (L.B_mem (invertibleMatrix A)))

/-- The scalar realization of the block orbit, as a function of the matrix entries. -/
def realizeOrbit (L : LineIwasawaData) (v : σ.smooth) (x : BinaryAdelicGL) :
    Matrix (Fin 3) (Fin 3) ℝ → ℂ := fun A =>
  σ.realize v (x * atInfinity (lineBlock (L.B (invertibleMatrix A))))

theorem realizeOrbit_contDiffOn (L : LineIwasawaData) (v : σ.smooth) (x : BinaryAdelicGL) :
    ContDiffOn ℝ ⊤ (realizeOrbit σ L v x) {A | A.det ≠ 0} :=
  (smooth_one_contDiffOn (function := fun h : BinaryRealGL => σ.realize v (x * atInfinity h))
    (σ.scalarSmooth v x)).comp (lineBlockMatrix_contDiffOn L)
    (fun A _ => lineBlockMatrix_det_ne_zero (L.B_mem (invertibleMatrix A)))

variable (m e : ℕ) (α β : ℂ) (w : σ.H)

theorem lineSection_invertible_eq (L : LineIwasawaData) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    lineSection σ m e α β w L (invertibleMatrix A) =
      (cornerScalar L α A * blockScalar L β A) •
        (kScalarMinus L m e A • blockOrbit σ L w A +
          kScalarPlus L m e A • blockOrbit σ L (wPlus σ w) A) := by
  have hB := L.B_mem (invertibleMatrix A)
  have e1 : cornerFactor e α (lineCorner (L.B (invertibleMatrix A))) = cornerScalar L α A :=
    cornerFactor_of_pos e α (L.B_corner_pos (invertibleMatrix A))
  have e2 : blockFactor β (lineBlock (L.B (invertibleMatrix A))).val.det = blockScalar L β A := by
    rw [lineBlock_det hB]
    exact blockFactor_of_pos β (L.B_block_pos (invertibleMatrix A))
  simp only [lineSection, leviFactor, e1, e2, kPart, map_smul, map_add, kScalarMinus,
    kScalarPlus, blockOrbit]
  module

/-- **(d) Analyticity.** If `w` is a smooth vector, the line section is real-analytic in the
matrix entries on the open set of invertible matrices. -/
theorem lineSection_contDiffOn (hw : w ∈ σ.smooth) (L : LineIwasawaData) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ => lineSection σ m e α β w L (invertibleMatrix A))
      {A | A.det ≠ 0} := by
  have hs : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      (cornerScalar L α A * blockScalar L β A) •
        (kScalarMinus L m e A • blockOrbit σ L w A +
          kScalarPlus L m e A • blockOrbit σ L (wPlus σ w) A)) {A | A.det ≠ 0} :=
    ((cornerScalar_contDiffOn L α).mul (blockScalar_contDiffOn L β)).smul
      (((kScalarMinus_contDiffOn L m e).smul (blockOrbit_contDiffOn σ L hw)).add
        ((kScalarPlus_contDiffOn L m e).smul (blockOrbit_contDiffOn σ L (wPlus_mem σ w hw))))
  exact hs.congr (fun A _ => lineSection_invertible_eq σ m e α β w L A)

/-- The line section is smooth in the sense of `Smooth` on `GL₃(ℝ)`. -/
theorem lineSection_smooth (hw : w ∈ σ.smooth) (L : LineIwasawaData) :
    Smooth (fun x : Fin 1 → RealGL3 => lineSection σ m e α β w L (x 0)) := by
  unfold Smooth
  exact (lineSection_contDiffOn σ m e α β w hw L).comp
    (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)).contDiffOn (fun A hA => hA 0)

/-! ## The smooth-vector version and its scalar realizations -/

/-- The K-part as an element of the smooth vectors. -/
def kPartS (hw : w ∈ σ.smooth) (κ : RealGL3) : σ.smooth :=
  (((κ.val 0 0 : ℝ) : ℂ)) ^ e • ((((κ.val 1 1 : ℝ) : ℂ) - Complex.I * ((κ.val 2 1 : ℝ) : ℂ)) ^ m •
      (⟨w, hw⟩ : σ.smooth) +
    (((κ.val 1 1 : ℝ) : ℂ) + Complex.I * ((κ.val 2 1 : ℝ) : ℂ)) ^ m •
      (⟨wPlus σ w, wPlus_mem σ w hw⟩ : σ.smooth))

theorem kPartS_val (hw : w ∈ σ.smooth) (κ : RealGL3) :
    (kPartS σ m e w hw κ).val = kPart σ m e w κ := rfl

/-- **(e)** The line section as a smooth vector. -/
def lineSectionSmooth (hw : w ∈ σ.smooth) (L : LineIwasawaData) (g : RealGL3) : σ.smooth :=
  leviFactor e α β (L.B g) •
    (⟨σ.π (atInfinity (lineBlock (L.B g))) (kPartS σ m e w hw (L.K g)).val,
      σ.smooth_stable _ _ (kPartS σ m e w hw (L.K g)).property⟩ : σ.smooth)

theorem lineSectionSmooth_val (hw : w ∈ σ.smooth) (L : LineIwasawaData) (g : RealGL3) :
    (lineSectionSmooth σ m e α β w hw L g).val = lineSection σ m e α β w L g := by
  rfl

/-- **(e)** The realization of the smooth line section is an explicit combination of the
realizations of the two weight vectors, translated by the block of `B g`. -/
theorem lineSectionSmooth_realize (hw : w ∈ σ.smooth) (L : LineIwasawaData)
    (x : BinaryAdelicGL) (g : RealGL3) :
    σ.realize (lineSectionSmooth σ m e α β w hw L g) x =
      leviFactor e α β (L.B g) *
        ((((L.K g).val 0 0 : ℝ) : ℂ) ^ e *
          (((((L.K g).val 1 1 : ℝ) : ℂ) - Complex.I * (((L.K g).val 2 1 : ℝ) : ℂ)) ^ m *
              σ.realize ⟨w, hw⟩ (x * atInfinity (lineBlock (L.B g))) +
            ((((L.K g).val 1 1 : ℝ) : ℂ) + Complex.I * (((L.K g).val 2 1 : ℝ) : ℂ)) ^ m *
              σ.realize ⟨wPlus σ w, wPlus_mem σ w hw⟩ (x * atInfinity (lineBlock (L.B g))))) := by
  simp only [lineSectionSmooth, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [σ.equivariant]
  simp only [kPartS, map_smul, map_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem lineSectionSmooth_realize_invertible_eq (hw : w ∈ σ.smooth) (L : LineIwasawaData)
    (x : BinaryAdelicGL) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    σ.realize (lineSectionSmooth σ m e α β w hw L (invertibleMatrix A)) x =
      (cornerScalar L α A * blockScalar L β A) *
        (kScalarMinus L m e A * realizeOrbit σ L ⟨w, hw⟩ x A +
          kScalarPlus L m e A * realizeOrbit σ L ⟨wPlus σ w, wPlus_mem σ w hw⟩ x A) := by
  have hB := L.B_mem (invertibleMatrix A)
  have e1 : cornerFactor e α (lineCorner (L.B (invertibleMatrix A))) = cornerScalar L α A :=
    cornerFactor_of_pos e α (L.B_corner_pos (invertibleMatrix A))
  have e2 : blockFactor β (lineBlock (L.B (invertibleMatrix A))).val.det = blockScalar L β A := by
    rw [lineBlock_det hB]
    exact blockFactor_of_pos β (L.B_block_pos (invertibleMatrix A))
  rw [lineSectionSmooth_realize]
  simp only [leviFactor, e1, e2, kScalarMinus, kScalarPlus, realizeOrbit]
  ring

/-- **(f) Scalar analyticity.** For each fixed adelic point `x`, the realization of the smooth
line section at `x` is real-analytic in the matrix entries. -/
theorem lineSectionSmooth_realize_contDiffOn (hw : w ∈ σ.smooth) (L : LineIwasawaData)
    (x : BinaryAdelicGL) :
    ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      σ.realize (lineSectionSmooth σ m e α β w hw L (invertibleMatrix A)) x)
      {A | A.det ≠ 0} := by
  have hs : ContDiffOn ℝ ⊤ (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      (cornerScalar L α A * blockScalar L β A) *
        (kScalarMinus L m e A * realizeOrbit σ L ⟨w, hw⟩ x A +
          kScalarPlus L m e A * realizeOrbit σ L ⟨wPlus σ w, wPlus_mem σ w hw⟩ x A))
      {A | A.det ≠ 0} :=
    ((cornerScalar_contDiffOn L α).mul (blockScalar_contDiffOn L β)).mul
      (((kScalarMinus_contDiffOn L m e).mul (realizeOrbit_contDiffOn σ L ⟨w, hw⟩ x)).add
        ((kScalarPlus_contDiffOn L m e).mul (realizeOrbit_contDiffOn σ L ⟨wPlus σ w, wPlus_mem σ w hw⟩ x)))
  exact hs.congr (fun A _ => lineSectionSmooth_realize_invertible_eq σ m e α β w hw L x A)

/-- Scalar analyticity in the `Smooth` formulation on `GL₃(ℝ)`. -/
theorem lineSectionSmooth_realize_smooth (hw : w ∈ σ.smooth) (L : LineIwasawaData)
    (x : BinaryAdelicGL) :
    Smooth (fun y : Fin 1 → RealGL3 => σ.realize (lineSectionSmooth σ m e α β w hw L (y 0)) x) := by
  unfold Smooth
  exact (lineSectionSmooth_realize_contDiffOn σ m e α β w hw L x).comp
    (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)).contDiffOn (fun A hA => hA 0)

end Analytic

end TernaryPeriodPolynomials.SourceConstruction

end
