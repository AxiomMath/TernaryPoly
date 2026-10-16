module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalCocycle

@[expose] public section


/-!
# The real line parabolic: blocks and radical coordinates

For `p` in the real line parabolic (first column `(∗, 0, 0)ᵀ`) write
`p = [[d, v], [0, A]]` with corner `d = p₀₀`, row `v = (p₀₁, p₀₂)` and lower block
`A = (p_{ij})_{i,j ∈ {1,2}} ∈ GL₂(ℝ)`.  This file provides

* the block `lineLeviBlock p = A` as a group homomorphism `lineLeviBlockHom` to `GL₂(ℝ)`;
* the real numbers `lrC0 p`, `lrC1 p` (the radical coordinates of the line cocycle),
  `lrC(p) = (A₀₀ v₁ - A₀₁ v₀, A₁₀ v₁ - A₁₁ v₀) / det A`, and their cocycle law
  `lrC_mul` : `lrC(p q) - lrC(p) = (d_p / det A_p) · A_p · lrC(q)`;
* the inverse-block relations `B A = 1` for `B` the lower block of `p⁻¹`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial Matrix GeneralEisenstein
open GeneralEisenstein.Adelic (InLineParabolic lineParabolic inLine_inv)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The lower-right block -/

/-- The lower-right `2 × 2` block of a `3 × 3` matrix. -/
def lrLowerBlock (g : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![g 1 1, g 1 2; g 2 1, g 2 2]

theorem lrLowerBlock_mul (g h : Matrix (Fin 3) (Fin 3) ℝ) (g10 : g 1 0 = 0) (g20 : g 2 0 = 0) :
    lrLowerBlock (g * h) = lrLowerBlock g * lrLowerBlock h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lrLowerBlock, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, g10, g20]

theorem lrLowerBlock_one : lrLowerBlock (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The lower-right block of a line-parabolic element, as a matrix. -/
def lrBlockP (p : lineParabolic ℝ) : Matrix (Fin 2) (Fin 2) ℝ := lrLowerBlock p.1.val

theorem lrBlockP_mul (p q : lineParabolic ℝ) : lrBlockP (p * q) = lrBlockP p * lrBlockP q := by
  have hp : InLineParabolic p.1 := p.2
  exact lrLowerBlock_mul p.1.val q.1.val hp.1 hp.2

theorem lrBlockP_one : lrBlockP (1 : lineParabolic ℝ) = 1 := lrLowerBlock_one

theorem lrBlockP_mul_inv (p : lineParabolic ℝ) : lrBlockP p * lrBlockP p⁻¹ = 1 := by
  rw [← lrBlockP_mul, mul_inv_cancel, lrBlockP_one]

theorem lrBlockP_inv_mul (p : lineParabolic ℝ) : lrBlockP p⁻¹ * lrBlockP p = 1 := by
  rw [← lrBlockP_mul, inv_mul_cancel, lrBlockP_one]

/-- The lower-right block `A_p ∈ GL₂(ℝ)` of a line-parabolic element. -/
def lineLeviBlock (p : lineParabolic ℝ) : GeneralLinearGroup (Fin 2) ℝ :=
  ⟨lrBlockP p, lrBlockP p⁻¹, lrBlockP_mul_inv p, lrBlockP_inv_mul p⟩

/-- `p ↦ A_p` is a homomorphism. -/
def lineLeviBlockHom : lineParabolic ℝ →* GeneralLinearGroup (Fin 2) ℝ where
  toFun := lineLeviBlock
  map_one' := Units.ext lrBlockP_one
  map_mul' p q := Units.ext (lrBlockP_mul p q)

/-! ## The corner entry and the entries of products -/

theorem lr_corner_mul_inv {g : RealGL3} (hg : InLineParabolic g) :
    g.val 0 0 * g.inv 0 0 = 1 := by
  have hr := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 0) g.inv_mul
  simpa [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, mul_comm] using hr

theorem lr_corner_ne_zero {g : RealGL3} (hg : InLineParabolic g) : g.val 0 0 ≠ 0 := by
  intro h
  have h1 := lr_corner_mul_inv hg
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem lr_mul_e00 (p q : lineParabolic ℝ) :
    (p * q).1.val 0 0 = p.1.val 0 0 * q.1.val 0 0 := by
  have hq : InLineParabolic q.1 := q.2
  show (p.1.val * q.1.val) 0 0 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, hq.1, hq.2]
  ring

theorem lr_mul_e01 (p q : lineParabolic ℝ) :
    (p * q).1.val 0 1 =
      p.1.val 0 0 * q.1.val 0 1 + p.1.val 0 1 * q.1.val 1 1 + p.1.val 0 2 * q.1.val 2 1 := by
  show (p.1.val * q.1.val) 0 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]

theorem lr_mul_e02 (p q : lineParabolic ℝ) :
    (p * q).1.val 0 2 =
      p.1.val 0 0 * q.1.val 0 2 + p.1.val 0 1 * q.1.val 1 2 + p.1.val 0 2 * q.1.val 2 2 := by
  show (p.1.val * q.1.val) 0 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three]

theorem lr_mul_e11 (p q : lineParabolic ℝ) :
    (p * q).1.val 1 1 = p.1.val 1 1 * q.1.val 1 1 + p.1.val 1 2 * q.1.val 2 1 := by
  have hp : InLineParabolic p.1 := p.2
  show (p.1.val * q.1.val) 1 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, hp.1]
  ring

theorem lr_mul_e12 (p q : lineParabolic ℝ) :
    (p * q).1.val 1 2 = p.1.val 1 1 * q.1.val 1 2 + p.1.val 1 2 * q.1.val 2 2 := by
  have hp : InLineParabolic p.1 := p.2
  show (p.1.val * q.1.val) 1 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, hp.1]
  ring

theorem lr_mul_e21 (p q : lineParabolic ℝ) :
    (p * q).1.val 2 1 = p.1.val 2 1 * q.1.val 1 1 + p.1.val 2 2 * q.1.val 2 1 := by
  have hp : InLineParabolic p.1 := p.2
  show (p.1.val * q.1.val) 2 1 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, hp.2]
  ring

theorem lr_mul_e22 (p q : lineParabolic ℝ) :
    (p * q).1.val 2 2 = p.1.val 2 1 * q.1.val 1 2 + p.1.val 2 2 * q.1.val 2 2 := by
  have hp : InLineParabolic p.1 := p.2
  show (p.1.val * q.1.val) 2 2 = _
  rw [Matrix.mul_apply, Fin.sum_univ_three, hp.2]
  ring

/-! ## The determinant of the lower block -/

/-- The determinant of the lower-right block of a line-parabolic element. -/
def lrDet (p : lineParabolic ℝ) : ℝ := p.1.val 1 1 * p.1.val 2 2 - p.1.val 1 2 * p.1.val 2 1

theorem lrDet_mul (p q : lineParabolic ℝ) : lrDet (p * q) = lrDet p * lrDet q := by
  unfold lrDet
  rw [lr_mul_e11, lr_mul_e12, lr_mul_e21, lr_mul_e22]
  ring

theorem lrDet_ne_zero (p : lineParabolic ℝ) : lrDet p ≠ 0 := by
  have h : ((GeneralLinearGroup.det (lineLeviBlock p) : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
  exact h

/-- The determinant of the complexified element is the corner times the block determinant. -/
theorem lr_det3_map (p : lineParabolic ℝ) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) p.1) : ℂˣ) : ℂ) =
      algebraMap ℝ ℂ (p.1.val 0 0 * lrDet p) := by
  have hp : InLineParabolic p.1 := p.2
  have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) p.1) : ℂˣ) : ℂ) =
      algebraMap ℝ ℂ p.1.val.det := by
    rw [GeneralLinearGroup.val_det_apply]
    exact (RingHom.map_det (algebraMap ℝ ℂ) p.1.val).symm
  rw [h1]
  congr 1
  rw [Matrix.det_fin_three]
  simp only [lrDet, hp.1, hp.2]
  ring

/-! ## The inverse block -/

/-- `B A = 1` for the lower block `B` of the inverse and the lower block `A` of `g`. -/
theorem lr_inv_block {g : RealGL3} (hg : InLineParabolic g) :
    g.inv 1 1 * g.val 1 1 + g.inv 1 2 * g.val 2 1 = 1 ∧
    g.inv 1 1 * g.val 1 2 + g.inv 1 2 * g.val 2 2 = 0 ∧
    g.inv 2 1 * g.val 1 1 + g.inv 2 2 * g.val 2 1 = 0 ∧
    g.inv 2 1 * g.val 1 2 + g.inv 2 2 * g.val 2 2 = 1 := by
  have h10 : g.inv 1 0 = 0 := (inLine_inv hg).1
  have h20 : g.inv 2 0 = 0 := (inLine_inv hg).2
  have e : ∀ i j : Fin 3, (g.inv * g.val) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j :=
    fun i j => congrFun (congrFun g.inv_mul i) j
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := e 1 1
    rw [Matrix.mul_apply, Fin.sum_univ_three, h10, zero_mul, zero_add, Matrix.one_apply_eq] at h
    exact h
  · have h := e 1 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, h10, zero_mul, zero_add,
      Matrix.one_apply_ne (show (1 : Fin 3) ≠ 2 by decide)] at h
    exact h
  · have h := e 2 1
    rw [Matrix.mul_apply, Fin.sum_univ_three, h20, zero_mul, zero_add,
      Matrix.one_apply_ne (show (2 : Fin 3) ≠ 1 by decide)] at h
    exact h
  · have h := e 2 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, h20, zero_mul, zero_add, Matrix.one_apply_eq] at h
    exact h

/-! ## The radical coordinates -/

/-- First radical coordinate: `(A₀₀ v₁ - A₀₁ v₀) / det A` for `v = (p₀₁, p₀₂)` and `A` the lower
block. -/
def lrC0 (p : lineParabolic ℝ) : ℝ :=
  (p.1.val 1 1 * p.1.val 0 2 - p.1.val 1 2 * p.1.val 0 1) / lrDet p

/-- Second radical coordinate: `(A₁₀ v₁ - A₁₁ v₀) / det A`. -/
def lrC1 (p : lineParabolic ℝ) : ℝ :=
  (p.1.val 2 1 * p.1.val 0 2 - p.1.val 2 2 * p.1.val 0 1) / lrDet p

theorem lrNum0_mul (p q : lineParabolic ℝ) :
    (p * q).1.val 1 1 * (p * q).1.val 0 2 - (p * q).1.val 1 2 * (p * q).1.val 0 1 =
      (p.1.val 1 1 * p.1.val 0 2 - p.1.val 1 2 * p.1.val 0 1) * lrDet q +
        p.1.val 0 0 *
          (p.1.val 1 1 * (q.1.val 1 1 * q.1.val 0 2 - q.1.val 1 2 * q.1.val 0 1) +
            p.1.val 1 2 * (q.1.val 2 1 * q.1.val 0 2 - q.1.val 2 2 * q.1.val 0 1)) := by
  rw [lr_mul_e11, lr_mul_e12, lr_mul_e01, lr_mul_e02]
  unfold lrDet
  ring

theorem lrNum1_mul (p q : lineParabolic ℝ) :
    (p * q).1.val 2 1 * (p * q).1.val 0 2 - (p * q).1.val 2 2 * (p * q).1.val 0 1 =
      (p.1.val 2 1 * p.1.val 0 2 - p.1.val 2 2 * p.1.val 0 1) * lrDet q +
        p.1.val 0 0 *
          (p.1.val 2 1 * (q.1.val 1 1 * q.1.val 0 2 - q.1.val 1 2 * q.1.val 0 1) +
            p.1.val 2 2 * (q.1.val 2 1 * q.1.val 0 2 - q.1.val 2 2 * q.1.val 0 1)) := by
  rw [lr_mul_e21, lr_mul_e22, lr_mul_e01, lr_mul_e02]
  unfold lrDet
  ring

/-- **The cocycle law of the radical coordinates**:
`lrC(p q) - lrC(p) = (d_p / det A_p) · A_p · lrC(q)`. -/
theorem lrC_mul (p q : lineParabolic ℝ) :
    lrC0 (p * q) - lrC0 p =
        p.1.val 0 0 / lrDet p * (p.1.val 1 1 * lrC0 q + p.1.val 1 2 * lrC1 q) ∧
    lrC1 (p * q) - lrC1 p =
        p.1.val 0 0 / lrDet p * (p.1.val 2 1 * lrC0 q + p.1.val 2 2 * lrC1 q) := by
  have hp := lrDet_ne_zero p
  have hq := lrDet_ne_zero q
  constructor
  · simp only [lrC0, lrC1]
    rw [lrDet_mul, lrNum0_mul p q]
    field_simp
    ring
  · simp only [lrC0, lrC1]
    rw [lrDet_mul, lrNum1_mul p q]
    field_simp
    ring

/-- The radical coordinates vanish when the row `v` vanishes. -/
theorem lrC_of_zero (p : lineParabolic ℝ) (h1 : p.1.val 0 1 = 0) (h2 : p.1.val 0 2 = 0) :
    lrC0 p = 0 ∧ lrC1 p = 0 := by
  constructor
  · simp [lrC0, h1, h2]
  · simp [lrC1, h1, h2]

end TernaryPeriodPolynomials.SourceConstruction

end
