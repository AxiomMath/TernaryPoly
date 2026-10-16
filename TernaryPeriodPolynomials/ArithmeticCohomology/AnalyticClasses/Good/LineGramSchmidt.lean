module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineRealLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismTranslation

@[expose] public section


/-!
# The explicit Iwasawa factorization of the real good-line argument

The real good-line argument is `g(u) = w⁻¹ n_Q(u) γ_good = [[0,1,0],[1,0,0],[u₂,u₁,1]]`.
Gram–Schmidt from the last row gives the explicit factorization `g(u) = b(u) k(u)` with

* `b(u) = [[1/α, -u₁u₂/(Rα), u₁/R], [0, α/R, u₂/R], [0, 0, R]]` upper triangular with positive
  diagonal, in the plane parabolic, and
* `k(u) = [[0, 1/α, -u₁/α], [α/R, -u₁u₂/(Rα), -u₂/(Rα)], [u₂/R, u₁/R, 1/R]]` orthogonal,

where `α = √(1 + u₁²)` and `R = √(1 + u₁² + u₂²)`. Both factors depend continuously on `u`, so the
map `p g(u) ↦ p b(u)` is a continuous plane-equivariant vertex map on the big cell. Its point of the
upper half-plane is `z(u) = A(u)·i = -u₁u₂/(1+u₁²) + i R/(1+u₁²)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- `α(u) = √(1 + u₁²)`. -/
def gsAlpha (u : ℝ × ℝ) : ℝ := Real.sqrt (1 + u.1 ^ 2)

/-- `R(u) = √(1 + u₁² + u₂²)`. -/
def gsRadius (u : ℝ × ℝ) : ℝ := Real.sqrt (1 + u.1 ^ 2 + u.2 ^ 2)

theorem gsAlpha_pos (u : ℝ × ℝ) : 0 < gsAlpha u := Real.sqrt_pos.mpr (by positivity)

theorem gsRadius_pos (u : ℝ × ℝ) : 0 < gsRadius u := Real.sqrt_pos.mpr (by positivity)

theorem gsAlpha_sq (u : ℝ × ℝ) : gsAlpha u ^ 2 = 1 + u.1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem gsRadius_sq (u : ℝ × ℝ) : gsRadius u ^ 2 = 1 + u.1 ^ 2 + u.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem continuous_gsAlpha : Continuous gsAlpha := by
  unfold gsAlpha; fun_prop

theorem continuous_gsRadius : Continuous gsRadius := by
  unfold gsRadius; fun_prop

/-- The upper triangular Iwasawa factor. -/
def gsUpperMatrix (u : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / gsAlpha u, -(u.1 * u.2) / (gsRadius u * gsAlpha u), u.1 / gsRadius u;
    0, gsAlpha u / gsRadius u, u.2 / gsRadius u;
    0, 0, gsRadius u]

/-- The orthogonal Iwasawa factor. -/
def gsOrthMatrix (u : ℝ × ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1 / gsAlpha u, -u.1 / gsAlpha u;
    gsAlpha u / gsRadius u, -(u.1 * u.2) / (gsRadius u * gsAlpha u), -u.2 / (gsRadius u * gsAlpha u);
    u.2 / gsRadius u, u.1 / gsRadius u, 1 / gsRadius u]

theorem gsUpperMatrix_mul_gsOrthMatrix (u : ℝ × ℝ) :
    gsUpperMatrix u * gsOrthMatrix u = (standardGoodLineRealArgument u).val := by
  have ha := gsAlpha_pos u
  have hr := gsRadius_pos u
  have ha2 := gsAlpha_sq u
  have hr2 := gsRadius_sq u
  rw [standardGoodLineRealArgument_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gsUpperMatrix, gsOrthMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> first | nlinarith [ha2, hr2] | linear_combination u.1 * ha2 - u.1 * hr2

theorem gsOrthMatrix_transpose_mul (u : ℝ × ℝ) :
    (gsOrthMatrix u).transpose * gsOrthMatrix u = 1 := by
  have ha := gsAlpha_pos u
  have hr := gsRadius_pos u
  have ha2 := gsAlpha_sq u
  have hr2 := gsRadius_sq u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gsOrthMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> first | nlinarith [ha2, hr2] | linear_combination u.1 * ha2 - u.1 * hr2

theorem gsOrthMatrix_mul_transpose (u : ℝ × ℝ) :
    gsOrthMatrix u * (gsOrthMatrix u).transpose = 1 :=
  mul_eq_one_comm.mp (gsOrthMatrix_transpose_mul u)

/-- The orthogonal factor as an invertible matrix. -/
def gsOrth (u : ℝ × ℝ) : RealGL3 :=
  ⟨gsOrthMatrix u, (gsOrthMatrix u).transpose, gsOrthMatrix_mul_transpose u,
    gsOrthMatrix_transpose_mul u⟩

theorem gsOrth_val (u : ℝ × ℝ) : (gsOrth u).val = gsOrthMatrix u := rfl

theorem gsOrth_orthogonal (u : ℝ × ℝ) : (gsOrth u).val.transpose * (gsOrth u).val = 1 :=
  gsOrthMatrix_transpose_mul u

/-- The upper triangular factor as an invertible matrix: `b(u) = g(u) k(u)⁻¹`. -/
def gsUpper (u : ℝ × ℝ) : RealGL3 := standardGoodLineRealArgument u * (gsOrth u)⁻¹

theorem gsUpper_val (u : ℝ × ℝ) : (gsUpper u).val = gsUpperMatrix u := by
  have e : (gsUpper u).val = (standardGoodLineRealArgument u).val * (gsOrthMatrix u).transpose := rfl
  rw [e, ← gsUpperMatrix_mul_gsOrthMatrix, Matrix.mul_assoc, gsOrthMatrix_mul_transpose,
    Matrix.mul_one]

/-- **The Iwasawa factorization** `g(u) = b(u) k(u)`. -/
theorem standardGoodLineRealArgument_eq_gsUpper_mul (u : ℝ × ℝ) :
    standardGoodLineRealArgument u = gsUpper u * gsOrth u := by
  rw [gsUpper, inv_mul_cancel_right]

theorem gsUpper_mem_planeParabolic (u : ℝ × ℝ) : gsUpper u ∈ planeParabolic ℝ := by
  refine ⟨?_, ?_⟩
  · change (gsUpper u).val 2 0 = 0
    rw [gsUpper_val]; simp [gsUpperMatrix]
  · change (gsUpper u).val 2 1 = 0
    rw [gsUpper_val]; simp [gsUpperMatrix]

theorem continuous_gsOrthMatrix : Continuous gsOrthMatrix := by
  have ha : ∀ u, gsAlpha u ≠ 0 := fun u => (gsAlpha_pos u).ne'
  have hr : ∀ u, gsRadius u ≠ 0 := fun u => (gsRadius_pos u).ne'
  have hra : ∀ u, gsRadius u * gsAlpha u ≠ 0 := fun u => mul_ne_zero (hr u) (ha u)
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have cA := continuous_gsAlpha
  have cR := continuous_gsRadius
  fin_cases i <;> fin_cases j <;> simp only [gsOrthMatrix] <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;>
    first
    | exact continuous_const
    | exact (continuous_const.div cA ha)
    | exact ((continuous_fst.neg).div cA ha)
    | exact (cA.div cR hr)
    | exact (((continuous_fst.mul continuous_snd).neg).div (cR.mul cA) hra)
    | exact ((continuous_snd.neg).div (cR.mul cA) hra)
    | exact (continuous_snd.div cR hr)
    | exact (continuous_fst.div cR hr)
    | exact (continuous_const.div cR hr)

theorem continuous_gsUpperMatrix : Continuous gsUpperMatrix := by
  have e : gsUpperMatrix = fun u => (standardGoodLineRealArgument u).val * (gsOrthMatrix u).transpose := by
    funext u
    rw [← gsUpperMatrix_mul_gsOrthMatrix, Matrix.mul_assoc, gsOrthMatrix_mul_transpose, Matrix.mul_one]
  rw [e]
  have cg : Continuous fun u : ℝ × ℝ => (standardGoodLineRealArgument u).val := by
    have e' : (fun u : ℝ × ℝ => (standardGoodLineRealArgument u).val) =
        fun u => !![0,1,0;1,0,0;u.2,u.1,1] := funext standardGoodLineRealArgument_val
    rw [e']
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  exact cg.matrix_mul continuous_gsOrthMatrix.matrix_transpose


/-! ### The plane-equivariant Gram–Schmidt vertex map

For `y = p g(u)` with `p` in the plane parabolic, the last row of `y` is `p₂₂ (u₂, u₁, 1)`, so `u` is
read off from the last row. The map `y ↦ y k(u(y))⁻¹` is therefore plane-equivariant, moves every
vertex by an orthogonal matrix, and lands in the plane parabolic on the big cell `y₂₂ ≠ 0`. -/

/-- The big-cell coordinate read off from the last row. -/
def gsChart (y : RealGL3) : ℝ × ℝ := (y.val 2 1 / y.val 2 2, y.val 2 0 / y.val 2 2)

/-- The plane-equivariant Gram–Schmidt vertex map. -/
def gsVertex (y : RealGL3) : RealGL3 := y * (gsOrth (gsChart y))⁻¹

theorem gsChart_standard (u : ℝ × ℝ) : gsChart (standardGoodLineRealArgument u) = u := by
  simp [gsChart, standardGoodLineRealArgument_val]

theorem planeParabolic_corner_ne_zero {p : RealGL3} (hp : p ∈ planeParabolic ℝ) : p.val 2 2 ≠ 0 := by
  obtain ⟨h0, h1⟩ := hp
  intro h2
  have hdet : p.val.det = 0 := by
    rw [Matrix.det_fin_three]
    change p.val 2 0 = 0 at h0
    change p.val 2 1 = 0 at h1
    rw [h0, h1, h2]
    ring
  exact (Matrix.isUnit_iff_isUnit_det _).mp p.isUnit |>.ne_zero hdet

theorem planeParabolic_mul_lastRow {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (y : RealGL3) (j : Fin 3) :
    (p * y).val 2 j = p.val 2 2 * y.val 2 j := by
  obtain ⟨h0, h1⟩ := hp
  change p.val 2 0 = 0 at h0
  change p.val 2 1 = 0 at h1
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, h0, h1]
  ring

theorem gsChart_plane_mul {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (y : RealGL3) :
    gsChart (p * y) = gsChart y := by
  have hc := planeParabolic_corner_ne_zero hp
  simp only [gsChart, planeParabolic_mul_lastRow hp]
  rw [mul_div_mul_left _ _ hc, mul_div_mul_left _ _ hc]

theorem gsVertex_plane_mul {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (y : RealGL3) :
    gsVertex (p * y) = p * gsVertex y := by
  rw [gsVertex, gsVertex, gsChart_plane_mul hp, mul_assoc]

theorem gsVertex_standard (u : ℝ × ℝ) : gsVertex (standardGoodLineRealArgument u) = gsUpper u := by
  rw [gsVertex, gsChart_standard, gsUpper]

theorem gsVertex_plane_standard {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (u : ℝ × ℝ) :
    gsVertex (p * standardGoodLineRealArgument u) = p * gsUpper u := by
  rw [gsVertex_plane_mul hp, gsVertex_standard]

theorem gsVertex_plane_standard_mem {p : RealGL3} (hp : p ∈ planeParabolic ℝ) (u : ℝ × ℝ) :
    gsVertex (p * standardGoodLineRealArgument u) ∈ planeParabolic ℝ := by
  rw [gsVertex_plane_standard hp]
  exact (planeParabolic ℝ).mul_mem hp (gsUpper_mem_planeParabolic u)

/-- The vertex map moves every vertex by an orthogonal matrix on the right. -/
theorem gsVertex_eq_mul (y : RealGL3) : gsVertex y = y * (gsOrth (gsChart y))⁻¹ := rfl

theorem gsOrth_inv_orthogonal (u : ℝ × ℝ) :
    ((gsOrth u)⁻¹).val.transpose * ((gsOrth u)⁻¹).val = 1 := by
  change (gsOrthMatrix u).transpose.transpose * (gsOrthMatrix u).transpose = 1
  rw [Matrix.transpose_transpose, gsOrthMatrix_mul_transpose]

end TernaryPeriodPolynomials.AnalyticClasses
