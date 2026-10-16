module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Symmetric.ProjectionSmooth

@[expose] public section


/-!
# The derivative of the Gram matrix and the projection at orthogonal matrices

The Gram matrix `S(y) = y yᵀ` has derivative `W ↦ W kᵀ + k Wᵀ` at `k`; this file records its
entries as continuous linear maps, together with the continuous linear maps `W ↦ S'_{·2}` and
`W ↦ S'₀₁ + (i / 2) (S'₀₀ - S'₁₁)` that are the derivatives of the radical coordinate and of the
Levi point at an orthogonal matrix. At an orthogonal matrix `k` the Gram matrix and its Schur
complement are identity matrices, the radical coordinate vanishes and the Levi point is `i`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.AnalyticClasses

/-! ### Linear maps -/

/-- The derivative `W ↦ W kᵀ + k Wᵀ` of the Gram matrix at `k`. -/
def gramDerivLinear (k : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℝ where
  toFun W := W * kᵀ + k * Wᵀ
  map_add' W V := by
    rw [Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add]
    abel
  map_smul' c W := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, smul_add]

theorem gramDerivLinear_apply (k W : Matrix (Fin 3) (Fin 3) ℝ) :
    gramDerivLinear k W = W * kᵀ + k * Wᵀ := rfl

/-- The entry `(a, b)` of a matrix, as a linear map. -/
def entryLinear (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℝ where
  toFun W := W a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The entry `(a, b)` of a matrix, as a continuous linear map. -/
def entryCLM (a b : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (entryLinear a b)

theorem entryCLM_apply (W : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    entryCLM a b W = W a b := rfl

/-- The entry `(a, b)` of the derivative `W ↦ W kᵀ + k Wᵀ` of the Gram matrix at `k`. -/
def gramEntryDeriv (k : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (entryLinear a b ∘ₗ gramDerivLinear k)

theorem gramEntryDeriv_apply (k W : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    gramEntryDeriv k a b W = (W * kᵀ + k * Wᵀ) a b := rfl

/-- The derivative `W ↦ S'(W)_{·2}` of the radical coordinate at an orthogonal matrix `k`,
where `S'(W) = W kᵀ + k Wᵀ`. -/
def radicalDeriv (k : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.pi fun i : Fin 2 => entryLinear i.castSucc 2 ∘ₗ gramDerivLinear k)

theorem radicalDeriv_apply (k W : Matrix (Fin 3) (Fin 3) ℝ) :
    radicalDeriv k W = fun i => (W * kᵀ + k * Wᵀ) i.castSucc 2 := rfl

/-- The `ℝ`-linear map `W ↦ S'₀₁ + (i / 2) (S'₀₀ - S'₁₁)`, `S'(W) = W kᵀ + k Wᵀ`. -/
def pointDerivLinear (k : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] ℂ where
  toFun W := ((W * kᵀ + k * Wᵀ) 0 1 : ℂ) +
    (Complex.I / 2) * (((W * kᵀ + k * Wᵀ) 0 0 : ℂ) - ((W * kᵀ + k * Wᵀ) 1 1 : ℂ))
  map_add' W V := by
    simp only [Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add, Matrix.add_apply,
      Complex.ofReal_add]
    ring
  map_smul' c W := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring

/-- The derivative of the Levi point at an orthogonal matrix `k`. -/
def pointDeriv (k : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (pointDerivLinear k)

theorem pointDeriv_apply (k W : Matrix (Fin 3) (Fin 3) ℝ) :
    pointDeriv k W = ((W * kᵀ + k * Wᵀ) 0 1 : ℂ) +
      (Complex.I / 2) * (((W * kᵀ + k * Wᵀ) 0 0 : ℂ) - ((W * kᵀ + k * Wᵀ) 1 1 : ℂ)) := rfl

/-! ### Values at orthogonal matrices -/

theorem gramMatrix_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    gramMatrix k = 1 := by
  rw [gramMatrix, mul_eq_one_comm.mp hk]

theorem symmetricSchur_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricSchur k = 1 := by
  have hS := gramMatrix_orthogonal hk
  funext i j
  simp only [symmetricSchur, hS]
  fin_cases i <;> fin_cases j <;> simp

/-- The radical coordinate vanishes at orthogonal matrices. -/
theorem symmetricRadical_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricRadical k = 0 := by
  have hS := gramMatrix_orthogonal hk
  funext i
  simp only [symmetricRadical, hS]
  fin_cases i <;> simp

theorem positivePoint_one : positivePoint 1 = Complex.I := by
  simp [positivePoint]

/-- The Levi point of an orthogonal matrix is `i`. -/
theorem symmetricPoint_orthogonal {k : Matrix (Fin 3) (Fin 3) ℝ} (hk : kᵀ * k = 1) :
    symmetricPoint k = Complex.I := by
  rw [symmetricPoint, symmetricSchur_orthogonal hk, positivePoint_one]

/-! ### Derivatives -/

theorem hasFDerivAt_gramMatrix_apply (k : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) :
    HasFDerivAt (fun y => gramMatrix y a b) (gramEntryDeriv k a b) k := by
  have e : ∀ i j, HasFDerivAt (fun y : Matrix (Fin 3) (Fin 3) ℝ => y i j) (entryCLM i j) k :=
    fun i j => (entryCLM i j).hasFDerivAt
  have sum := HasFDerivAt.fun_sum (u := Finset.univ) fun m _ => (e a m).mul (e b m)
  have hfun : (fun y => gramMatrix y a b) = fun y => ∑ m, y a m * y b m := by
    funext y
    exact gramMatrix_apply y a b
  rw [hfun]
  refine sum.congr_fderiv (ContinuousLinearMap.ext fun W => ?_)
  change _ = (W * kᵀ + k * Wᵀ) a b
  simp only [_root_.sum_apply, _root_.add_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  all_goals exact Finset.sum_congr rfl fun m _ => mul_comm _ _

end TernaryPeriodPolynomials.AnalyticClasses
