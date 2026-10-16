module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Jets
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Translations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TranslatedJets

open SmoothJets

def tupleLeftMul {size arity : ℕ} (left : MatrixTuples size arity) :
    MatrixTuples size arity →ₗ[ℝ] MatrixTuples size arity where
  toFun matrices index := left index * matrices index
  map_add' first second := by
    funext index
    exact Matrix.mul_add _ _ _
  map_smul' scalar matrices := by
    funext index
    change left index * (scalar • matrices index) = scalar • (left index * matrices index)
    exact Matrix.mul_smul _ _ _

def tupleLeftMulL {size arity : ℕ} (left : MatrixTuples size arity) :
    MatrixTuples size arity →L[ℝ] MatrixTuples size arity :=
  (tupleLeftMul left).toContinuousLinearMap

def leftMulLinear {size arity : ℕ} :
    MatrixTuples size arity →ₗ[ℝ] (MatrixTuples size arity →L[ℝ] MatrixTuples size arity) where
  toFun := tupleLeftMulL
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro matrices
    funext index
    change (first index + second index) * matrices index =
      first index * matrices index + second index * matrices index
    exact Matrix.add_mul _ _ _
  map_smul' scalar left := by
    apply ContinuousLinearMap.ext
    intro matrices
    funext index
    change (scalar • left index) * matrices index = scalar • (left index * matrices index)
    exact Matrix.smul_mul _ _ _

theorem leftMul_continuous {size arity : ℕ} :
    Continuous (tupleLeftMulL (size := size) (arity := arity)) :=
  leftMulLinear.toContinuousLinearMap.continuous

theorem invertibleMatrix_mul_left {size : ℕ}
    (left : GeneralLinearGroup (Fin size) ℝ) (matrix : Matrix (Fin size) (Fin size) ℝ)
    (invertible : matrix.det ≠ 0) :
    invertibleMatrix (left.val * matrix) = left * invertibleMatrix matrix := by
  have productInvertible : (left.val * matrix).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (GeneralLinearGroup.det_ne_zero left) invertible
  unfold invertibleMatrix
  rw [dite_eq_left productInvertible, dite_eq_left invertible]
  apply Units.ext
  rfl

theorem preimage_domain {size arity : ℕ}
    (left : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    (tupleLeftMulL (fun index => (left index).val)) ⁻¹' domain size arity = domain size arity := by
  ext matrices
  change (∀ index, ((left index).val * matrices index).det ≠ 0) ↔
    ∀ index, (matrices index).det ≠ 0
  simp only [Matrix.det_mul, mul_ne_zero_iff]
  constructor
  · intro membership index
    exact (membership index).2
  · intro membership index
    exact ⟨GeneralLinearGroup.det_ne_zero _, membership index⟩

theorem jet_mul_left {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (order : ℕ)
    (left right : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    jet order (fun elements => function (fun index => left index * elements index)) right =
      (jet order function (fun index => left index * right index)).compContinuousLinearMap
        (fun _ => tupleLeftMulL (fun index => (left index).val)) := by
  let linear := tupleLeftMulL (fun index => (left index).val)
  have pointMem : (fun index => (right index).val) ∈ domain size arity :=
    fun index => GeneralLinearGroup.det_ne_zero _
  have maps : linear (fun index => (right index).val) ∈ domain size arity := by
    rw [← preimage_domain left] at pointMem
    exact pointMem
  have smooth' : ContDiffOn ℝ ⊤ (matrixExtension function) (domain size arity) := smooth
  have preimage : linear ⁻¹' domain size arity = domain size arity := preimage_domain left
  have derivative := linear.iteratedFDerivWithin_comp_right
    (f := matrixExtension function) smooth' (domain_open size arity).uniqueDiffOn
    (by erw [preimage]; exact (domain_open size arity).uniqueDiffOn) maps
    (i := order) (by simp)
  erw [preimage] at derivative
  have agrees : Set.EqOn
      (matrixExtension (fun elements => function (fun index => left index * elements index)))
      (matrixExtension function ∘ linear) (domain size arity) := by
    intro matrices membership
    unfold matrixExtension
    dsimp only [Function.comp_def]
    congr 1
    funext index
    exact (invertibleMatrix_mul_left (left index) (matrices index) (membership index)).symm
  exact (iteratedFDerivWithin_congr agrees pointMem order).trans derivative

theorem jet_mul_left_continuous {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (order : ℕ) :
    Continuous (fun pair : (Fin arity → GeneralLinearGroup (Fin size) ℝ) ×
        (Fin arity → GeneralLinearGroup (Fin size) ℝ) =>
      jet order (fun elements => function (fun index => pair.1 index * elements index)) pair.2) := by
  let compose := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin order => MatrixTuples size arity)
    (fun _ : Fin order => MatrixTuples size arity) E
  have leftContinuous : Continuous (fun left : Fin arity → GeneralLinearGroup (Fin size) ℝ =>
      tupleLeftMulL (fun index => (left index).val)) :=
    leftMul_continuous.comp (continuous_pi (fun index =>
      Units.continuous_val.comp (continuous_apply index)))
  have operators : Continuous (fun pair : (Fin arity → GeneralLinearGroup (Fin size) ℝ) ×
      (Fin arity → GeneralLinearGroup (Fin size) ℝ) =>
      compose (fun _ : Fin order => tupleLeftMulL (fun index => (pair.1 index).val))) := compose.cont.comp
    (continuous_pi (fun _ : Fin order => leftContinuous.comp continuous_fst))
  have values : Continuous (fun pair : (Fin arity → GeneralLinearGroup (Fin size) ℝ) ×
      (Fin arity → GeneralLinearGroup (Fin size) ℝ) =>
      jet order function (pair.1 * pair.2)) :=
    (jet_continuous function smooth order).comp (continuous_fst.mul continuous_snd)
  have composed := operators.clm_apply values
  convert composed using 1
  all_goals try rfl
  all_goals
    apply heq_of_eq
    funext pair
    rw [jet_mul_left function smooth]
    rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.TranslatedJets
