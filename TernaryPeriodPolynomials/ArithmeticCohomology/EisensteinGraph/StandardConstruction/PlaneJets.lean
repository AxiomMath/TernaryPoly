module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.AffineJets

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PlaneJets

open SmoothJets

theorem block_add (first second : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    planeBlock (first + second) (a + b) = planeBlock first a + planeBlock second b := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [planeBlock]

theorem block_smul (scalar : ℝ) (matrix : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    planeBlock (scalar • matrix) (scalar * a) = scalar • planeBlock matrix a := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [planeBlock]

theorem block_det (matrix : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    (planeBlock matrix a).det = matrix.det * a := by
  simp [planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

def linear {arity : ℕ} (right : MatrixTuples 3 arity) :
    MatrixTuples 2 arity →ₗ[ℝ] MatrixTuples 3 arity where
  toFun matrices index := planeBlock (matrices index) 0 * right index
  map_add' first second := by
    funext index
    change planeBlock (first index + second index) 0 * right index = _
    rw [show planeBlock (first index + second index) 0 =
      planeBlock (first index) 0 + planeBlock (second index) 0 by
        simpa using block_add (first index) (second index) 0 0, Matrix.add_mul]
    rfl
  map_smul' scalar matrices := by
    funext index
    change planeBlock (scalar • matrices index) 0 * right index = _
    rw [show planeBlock (scalar • matrices index) 0 = scalar • planeBlock (matrices index) 0 by
      simpa using block_smul scalar (matrices index) 0, Matrix.smul_mul]
    rfl

def linearL {arity : ℕ} (right : MatrixTuples 3 arity) :
    MatrixTuples 2 arity →L[ℝ] MatrixTuples 3 arity :=
  (linear right).toContinuousLinearMap

def rightLinear {arity : ℕ} :
    MatrixTuples 3 arity →ₗ[ℝ] (MatrixTuples 2 arity →L[ℝ] MatrixTuples 3 arity) where
  toFun := linearL
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro matrices
    funext index
    change planeBlock (matrices index) 0 * (first index + second index) =
      planeBlock (matrices index) 0 * first index + planeBlock (matrices index) 0 * second index
    exact Matrix.mul_add _ _ _
  map_smul' scalar right := by
    apply ContinuousLinearMap.ext
    intro matrices
    funext index
    change planeBlock (matrices index) 0 * (scalar • right index) =
      scalar • (planeBlock (matrices index) 0 * right index)
    exact Matrix.mul_smul _ _ _

theorem linearL_continuous {arity : ℕ} : Continuous (linearL (arity := arity)) :=
  rightLinear.toContinuousLinearMap.continuous

def constant {arity : ℕ} (right : MatrixTuples 3 arity) : MatrixTuples 3 arity :=
  fun index => planeBlock 0 1 * right index

theorem affine_formula {arity : ℕ} (right : MatrixTuples 3 arity) (matrices : MatrixTuples 2 arity) :
    linearL right matrices + constant right =
      fun index => planeBlock (matrices index) 1 * right index := by
  funext index
  change planeBlock (matrices index) 0 * right index + planeBlock 0 1 * right index = _
  rw [← Matrix.add_mul, ← block_add]
  simp

theorem affine_preimage {arity : ℕ} (right : Fin arity → RealGL3) :
    (fun matrices => linearL (fun index => (right index).val) matrices +
      constant (fun index => (right index).val)) ⁻¹' domain 3 arity = domain 2 arity := by
  ext matrices
  simp only [Set.mem_preimage, affine_formula, domain, Set.mem_ofPred_eq, Matrix.det_mul,
    block_det, mul_one, mul_ne_zero_iff]
  constructor
  · intro membership index
    exact (membership index).1
  · intro membership index
    exact ⟨membership index, GeneralLinearGroup.det_ne_zero _⟩

theorem invertibleMatrix_block (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (invertible : matrix.det ≠ 0) :
    invertibleMatrix (planeBlock matrix 1) = planeLevi (invertibleMatrix matrix) 1 := by
  have blockInvertible : (planeBlock matrix 1).det ≠ 0 := by simpa [block_det] using invertible
  unfold invertibleMatrix
  rw [dite_eq_left blockInvertible, dite_eq_left invertible]
  apply Units.ext
  rfl

theorem jet_plane {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → RealGL3) → E) (smooth : Smooth function) (order : ℕ)
    (right : Fin arity → RealGL3) (binary : Fin arity → BinaryRealGL) :
    jet order (fun elements => function (fun index => planeLevi (elements index) 1 * right index)) binary =
      (jet order function (fun index => planeLevi (binary index) 1 * right index)).compContinuousLinearMap
        (fun _ => linearL (fun index => (right index).val)) := by
  let matrices := fun index => (right index).val
  have preimage := affine_preimage right
  have pointMem : (fun index => (binary index).val) ∈ domain 2 arity :=
    fun index => GeneralLinearGroup.det_ne_zero _
  have maps : linearL matrices (fun index => (binary index).val) + constant matrices ∈ domain 3 arity := by
    rw [← preimage] at pointMem
    exact pointMem
  have derivative := AffineJets.iterated_affine (matrixExtension function) (domain 3 arity)
    (domain_open 3 arity) smooth (linearL matrices) (constant matrices)
    (fun index => (binary index).val) maps order
  erw [preimage] at derivative
  have agrees : Set.EqOn
      (matrixExtension (fun elements => function (fun index => planeLevi (elements index) 1 * right index)))
      (fun input => matrixExtension function (linearL matrices input + constant matrices))
      (domain 2 arity) := by
    intro input membership
    dsimp only
    erw [affine_formula]
    change function (fun index => planeLevi (invertibleMatrix (input index)) 1 * right index) =
      function (fun index => invertibleMatrix (planeBlock (input index) 1 * (right index).val))
    apply congrArg function
    funext index
    rw [SmoothTranslations.invertibleMatrix_mul_right _ (by simpa [block_det] using membership index),
      invertibleMatrix_block _ (membership index)]
  have equality := (iteratedFDerivWithin_congr agrees pointMem order).trans derivative
  have coordinates : linearL matrices (fun index => (binary index).val) + constant matrices =
      fun index => (planeLevi (binary index) 1 * right index).val := affine_formula _ _
  erw [coordinates] at equality
  exact equality

theorem planeLevi_continuous : Continuous (fun binary : BinaryRealGL => planeLevi binary 1) := by
  rw [Units.continuous_iff]
  constructor
  all_goals
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    fin_cases row <;> fin_cases column <;>
      simp only [Function.comp_def, planeLevi, planeBlock, Matrix.of_apply] <;> fun_prop

theorem jet_plane_continuous {arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → RealGL3) → E) (smooth : Smooth function) (order : ℕ) :
    Continuous (fun pair : (Fin arity → RealGL3) × (Fin arity → BinaryRealGL) =>
      jet order (fun elements => function (fun index => planeLevi (elements index) 1 * pair.1 index)) pair.2) := by
  let compose := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin order => MatrixTuples 2 arity) (fun _ : Fin order => MatrixTuples 3 arity) E
  have operators : Continuous (fun pair : (Fin arity → RealGL3) × (Fin arity → BinaryRealGL) =>
      compose (fun _ : Fin order => linearL (fun index => (pair.1 index).val))) :=
    compose.cont.comp (continuous_pi (fun _ => linearL_continuous.comp
      (continuous_pi (fun index => Units.continuous_val.comp ((continuous_apply index).comp continuous_fst)))))
  have values : Continuous (fun pair : (Fin arity → RealGL3) × (Fin arity → BinaryRealGL) =>
      jet order function (fun index => planeLevi (pair.2 index) 1 * pair.1 index)) :=
    (jet_continuous function smooth order).comp (continuous_pi (fun index =>
      (planeLevi_continuous.comp ((continuous_apply index).comp continuous_snd)).mul
        ((continuous_apply index).comp continuous_fst)))
  have composed := operators.clm_apply values
  convert composed using 1
  all_goals try rfl
  all_goals
    apply heq_of_eq
    funext pair
    rw [jet_plane function smooth]
    rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PlaneJets
