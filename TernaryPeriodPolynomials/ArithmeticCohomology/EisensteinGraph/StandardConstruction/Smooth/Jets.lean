module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Continuity
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothJets

abbrev MatrixTuples (size arity : ℕ) := Fin arity → Matrix (Fin size) (Fin size) ℝ

instance matrixJetNormed {size arity order : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin order => MatrixTuples size arity) E) :=
  ContinuousMultilinearMap.normedAddCommGroup'

def domain (size arity : ℕ) : Set (MatrixTuples size arity) :=
  {matrices | ∀ index, (matrices index).det ≠ 0}

theorem domain_open (size arity : ℕ) : IsOpen (domain size arity) := by
  have equality : domain size arity =
      ⋂ index : Fin arity, {matrices : MatrixTuples size arity | (matrices index).det ≠ 0} := by
    ext matrices
    simp [domain]
  rw [equality]
  apply isOpen_iInter_of_finite
  intro index
  exact isOpen_ne.preimage (continuous_apply index).matrix_det

def matrixExtension {size arity : ℕ} {E : Type}
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E) :
    MatrixTuples size arity → E :=
  fun matrices => function (fun index => invertibleMatrix (matrices index))

def jet {size arity : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (order : ℕ) (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (elements : Fin arity → GeneralLinearGroup (Fin size) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => MatrixTuples size arity) E :=
  iteratedFDerivWithin ℝ order (matrixExtension function) (domain size arity)
    (fun index => (elements index).val)

theorem jet_continuous {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (order : ℕ) : Continuous (jet order function) := by
  have continuous : ContinuousOn
      (iteratedFDerivWithin ℝ order (matrixExtension function) (domain size arity))
      (domain size arity) :=
    smooth.continuousOn_iteratedFDerivWithin (by simp) (domain_open size arity).uniqueDiffOn
  have coordinates : Continuous
      (fun elements : Fin arity → GeneralLinearGroup (Fin size) ℝ =>
        fun index => (elements index).val) :=
    continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index))
  exact continuous.comp_continuous coordinates
    (fun elements index => (GeneralLinearGroup.det (elements index)).ne_zero)

theorem jet_bounded {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (order : ℕ)
    (set : Set (Fin arity → GeneralLinearGroup (Fin size) ℝ)) (compact : IsCompact set) :
    ∃ bound : ℝ, ∀ elements ∈ set, ‖jet order function elements‖ ≤ bound :=
  compact.exists_bound_of_continuousOn (jet_continuous function smooth order).continuousOn

/-- A single compact bound controls every derivative up to any fixed finite order. -/
theorem finite_jets_bounded {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E)
    (smooth : Smooth function) (order : ℕ)
    (set : Set (Fin arity → GeneralLinearGroup (Fin size) ℝ)) (compact : IsCompact set) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ elements ∈ set, ∀ derivative ≤ order,
      ‖jet derivative function elements‖ ≤ bound := by
  have continuous : Continuous (fun elements =>
      ∑ derivative ∈ Finset.range (order + 1), ‖jet derivative function elements‖) := by
    apply continuous_finsetSum
    intro derivative _
    exact (jet_continuous function smooth derivative).norm
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn continuous.continuousOn
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro elements membership derivative atMost
  have estimate := bounded elements membership
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at estimate
  have single : ‖jet derivative function elements‖ ≤
      ∑ index ∈ Finset.range (order + 1), ‖jet index function elements‖ :=
    Finset.single_le_sum (s := Finset.range (order + 1)) (a := derivative)
      (f := fun index => ‖jet index function elements‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
  exact single.trans (estimate.trans (le_max_left _ _))

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothJets
