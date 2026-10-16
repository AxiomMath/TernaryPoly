module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.FlatUniqueness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.MaximalCompact

theorem orthogonal_entry_bound {size : ℕ}
    (matrix : Matrix (Fin size) (Fin size) ℝ)
    (orthogonal : matrix.transpose * matrix = 1) (row column : Fin size) :
    matrix row column ∈ Set.Icc (-1 : ℝ) 1 := by
  have diagonal := congrArg (fun value => value column column) orthogonal
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at diagonal
  have bound : matrix row column * matrix row column ≤ 1 := by
    rw [← diagonal]
    exact Finset.single_le_sum (fun index _ => mul_self_nonneg (matrix index column))
      (Finset.mem_univ row)
  constructor <;> nlinarith [sq_nonneg (matrix row column + 1),
    sq_nonneg (matrix row column - 1)]

theorem orthogonal_inverse {size : ℕ}
    (element : GeneralLinearGroup (Fin size) ℝ)
    (orthogonal : element.val.transpose * element.val = 1) :
    element.inv = element.val.transpose := by
  calc
    element.inv = 1 * element.inv := (one_mul _).symm
    _ = (element.val.transpose * element.val) * element.inv := by rw [orthogonal]
    _ = element.val.transpose := by rw [mul_assoc, element.val_inv, mul_one]

theorem real_isCompact {size : ℕ} :
    IsCompact {element : GeneralLinearGroup (Fin size) ℝ |
      element.val.transpose * element.val = 1} := by
  let box : Set (Matrix (Fin size) (Fin size) ℝ) := (Set.Icc (-1 : ℝ) 1).matrix
  have boxCompact : IsCompact box := isCompact_Icc.matrix
  have pairsCompact := boxCompact.prod (boxCompact.image MulOpposite.continuous_op)
  have unitsCompact := Units.isClosedEmbedding_embedProduct.isCompact_preimage pairsCompact
  apply unitsCompact.of_isClosed_subset
  · exact isClosed_eq (Units.continuous_val.matrix_transpose.mul Units.continuous_val)
      continuous_const
  · intro element orthogonal
    constructor
    · exact Set.mem_matrix.mpr (orthogonal_entry_bound element.val orthogonal)
    · refine ⟨element.inv, ?_, rfl⟩
      rw [orthogonal_inverse element orthogonal]
      exact Set.mem_matrix.mpr (fun row column =>
        orthogonal_entry_bound element.val orthogonal column row)

theorem combineGL_continuous {size : ℕ} :
    Continuous (fun components : GeneralLinearGroup (Fin size) ℝ ×
      GeneralLinearGroup (Fin size) FiniteAdeles => combineGL components.1 components.2) := by
  have realValue : Continuous (fun element : GeneralLinearGroup (Fin size) ℝ => element.val) :=
    Units.continuous_val
  have finiteValue : Continuous
      (fun element : GeneralLinearGroup (Fin size) FiniteAdeles => element.val) :=
    Units.continuous_val
  have realInverse : Continuous (fun element : GeneralLinearGroup (Fin size) ℝ => element.inv) :=
    Units.continuous_coe_inv
  have finiteInverse : Continuous
      (fun element : GeneralLinearGroup (Fin size) FiniteAdeles => element.inv) :=
    Units.continuous_coe_inv
  apply Units.continuous_iff.mpr
  constructor
  ·
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    apply Continuous.prodMk
    · exact (continuous_apply column).comp ((continuous_apply row).comp
        (realValue.comp continuous_fst))
    · exact (continuous_apply column).comp ((continuous_apply row).comp
        (finiteValue.comp continuous_snd))
  ·
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    apply Continuous.prodMk
    · exact (continuous_apply column).comp ((continuous_apply row).comp
        (realInverse.comp continuous_fst))
    · exact (continuous_apply column).comp ((continuous_apply row).comp
        (finiteInverse.comp continuous_snd))

theorem isCompact : IsCompact {element : AdelicGL | inMaximalCompact element} := by
  have finiteCompact : IsCompact
      (Set.range (GeneralLinearGroup.map (n := Fin 3) integralEmbedding)) :=
    isCompact_range TopologicalMatrices.integralGL_isOpenEmbedding.continuous
  have compactImage := (real_isCompact (size := 3)).prod finiteCompact |>.image
    (combineGL_continuous (size := 3))
  convert compactImage using 1
  ext element
  constructor
  · rintro ⟨real, finite⟩
    refine ⟨(realGroup element, finiteGroup element), ⟨real, finite⟩, ?_⟩
    exact InducedContinuity.adelic_ext
      (AdelicDecomposition.realGroup_combine _ _) (AdelicDecomposition.finiteGroup_combine _ _)
  · rintro ⟨⟨real, finite⟩, ⟨orthogonal, integral⟩, rfl⟩
    exact ⟨by simpa only [AdelicDecomposition.realGroup_combine, Set.mem_ofPred_eq] using orthogonal,
      by simpa only [AdelicDecomposition.finiteGroup_combine] using integral⟩

theorem induced_bounded {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) (function : AdelicGL → ℂ)
    (induced : IsInduced data side parameter function) :
    ∃ bound : ℝ, ∀ element, inMaximalCompact element → ‖function element‖ ≤ bound :=
  isCompact.exists_bound_of_continuousOn
    (InducedContinuity.induced_continuous data side parameter function induced).continuousOn

theorem flat_compact_value {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (parameter : ℂ) (element : AdelicGL) (membership : inMaximalCompact element) :
    extension parameter element = extension cohomologicalPoint element := by
  have equality := flat.2.2 parameter 1 element membership
  have identity : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  simpa [normPower, identity] using equality

theorem flat_bounded {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ bound : ℝ, ∀ parameter element, inMaximalCompact element →
      ‖extension parameter element‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := induced_bounded data .plane cohomologicalPoint
    (extension cohomologicalPoint) (flat.1 cohomologicalPoint)
  refine ⟨bound, ?_⟩
  intro parameter element membership
  rw [flat_compact_value data extension flat parameter element membership]
  exact bounded element membership

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.MaximalCompact
