module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.LocalDecomposition
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealDecomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicDecomposition

def productUnit {Index : Type} {Rings : Index → Type}
    [∀ index, CommRing (Rings index)] (components : ∀ index, GL3 (Rings index)) :
    GL3 (∀ index, Rings index) where
  val row column index := (components index).val row column
  inv row column index := (components index).inv row column
  val_inv := by
    ext row column index
    change (∑ middle : Fin 3, (fun index => (components index).val row middle) *
      (fun index => (components index).inv middle column)) index =
        (if row = column then (1 : ∀ index, Rings index) else 0) index
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.mul_apply]
    have equation := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) (Rings index) =>
      matrix row column) (components index).mul_inv
    split_ifs with equality
    all_goals simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, equality] using equation
  inv_val := by
    ext row column index
    change (∑ middle : Fin 3, (fun index => (components index).inv row middle) *
      (fun index => (components index).val middle column)) index =
        (if row = column then (1 : ∀ index, Rings index) else 0) index
    simp only [Fin.sum_univ_three, Pi.add_apply, Pi.mul_apply]
    have equation := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) (Rings index) =>
      matrix row column) (components index).inv_mul
    split_ifs with equality
    all_goals simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, equality] using equation

theorem finiteGLAt_productUnit
    (components : ∀ place : FinitePlace, GL3 (place.adicCompletionIntegers ℚ))
    (place : FinitePlace) :
    finiteGLAt place (GeneralLinearGroup.map integralEmbedding (productUnit components)) =
      GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (components place) := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finite_planeCompact (element : FiniteGL) :
    ∃ compact : GL3 IntegralAdeles,
      element * (GeneralLinearGroup.map integralEmbedding compact)⁻¹ ∈
        planeParabolic FiniteAdeles := by
  have localDecomposition : ∀ place : FinitePlace,
      ∃ compact : GL3 (place.adicCompletionIntegers ℚ),
        finiteGLAt place element *
            (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype compact)⁻¹ ∈
          planeParabolic (place.adicCompletion ℚ) := by
    intro place
    exact LocalDecomposition.valuation_planeCompact Valued.v (finiteGLAt place element)
  choose components membership using localDecomposition
  refine ⟨productUnit components, ?_, ?_⟩
  · apply FiniteAdeleRing.ext ℚ
    intro place
    have first := (membership place).1
    have mapped : finiteGLAt place
        (element * (GeneralLinearGroup.map integralEmbedding (productUnit components))⁻¹) =
      finiteGLAt place element *
        (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (components place))⁻¹ := by
      rw [map_mul, map_inv, finiteGLAt_productUnit]
    exact (congrArg (fun matrix => matrix.val 2 0) mapped).trans first
  · apply FiniteAdeleRing.ext ℚ
    intro place
    have second := (membership place).2
    have mapped : finiteGLAt place
        (element * (GeneralLinearGroup.map integralEmbedding (productUnit components))⁻¹) =
      finiteGLAt place element *
        (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (components place))⁻¹ := by
      rw [map_mul, map_inv, finiteGLAt_productUnit]
    exact (congrArg (fun matrix => matrix.val 2 1) mapped).trans second

theorem realGroup_combine (real : GL3 ℝ) (finite : FiniteGL) :
    realGroup (combineGL real finite) = real := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem finiteGroup_combine (real : GL3 ℝ) (finite : FiniteGL) :
    finiteGroup (combineGL real finite) = finite := by
  apply GeneralLinearGroup.ext
  intro row column
  rfl

theorem adelic_planeCompact (element : AdelicGL) :
    ∃ parabolic compact : AdelicGL, parabolic ∈ planeParabolic Adeles ∧
      inMaximalCompact compact ∧ element = parabolic * compact := by
  obtain ⟨realParabolic, realCompact, realMembership, orthogonal, realDecomposition⟩ :=
    RealDecomposition.real_planeCompact (realGroup element)
  obtain ⟨finiteCompact, finiteMembership⟩ := finite_planeCompact (finiteGroup element)
  let compact : AdelicGL := combineGL realCompact
    (GeneralLinearGroup.map integralEmbedding finiteCompact)
  have compactReal : realGroup compact = realCompact := realGroup_combine _ _
  have compactFinite : finiteGroup compact =
      GeneralLinearGroup.map integralEmbedding finiteCompact := finiteGroup_combine _ _
  have realProduct : realGroup (element * compact⁻¹) = realParabolic := by
    rw [map_mul, map_inv, compactReal, realDecomposition, mul_inv_cancel_right]
  have finiteProduct : finiteGroup (element * compact⁻¹) =
      finiteGroup element * (GeneralLinearGroup.map integralEmbedding finiteCompact)⁻¹ := by
    rw [map_mul, map_inv, compactFinite]
  refine ⟨element * compact⁻¹, compact, ?_, ?_, ?_⟩
  · constructor
    · apply Prod.ext
      · exact (congrArg (fun matrix => matrix.val 2 0) realProduct).trans realMembership.1
      · exact (congrArg (fun matrix => matrix.val 2 0) finiteProduct).trans finiteMembership.1
    · apply Prod.ext
      · exact (congrArg (fun matrix => matrix.val 2 1) realProduct).trans realMembership.2
      · exact (congrArg (fun matrix => matrix.val 2 1) finiteProduct).trans finiteMembership.2
  · exact ⟨compactReal ▸ orthogonal, ⟨finiteCompact, compactFinite.symm⟩⟩
  · simp only [mul_assoc, inv_mul_cancel, mul_one]

theorem adelic_planeDecomposition (element : AdelicGL) :
    ∃ first second : Adeles, ∃ binary : BinaryAdelicGL, ∃ unit : Adelesˣ,
      ∃ compact : AdelicGL, inMaximalCompact compact ∧
        element = planeUnipotent first second * planeLevi binary unit * compact := by
  obtain ⟨parabolic, compact, membership, compactMembership, decomposition⟩ :=
    adelic_planeCompact element
  obtain ⟨first, second, binary, unit, parabolicDecomposition⟩ :=
    ParabolicDecomposition.plane_decomposition_exists parabolic membership
  exact ⟨first, second, binary, unit, compact, compactMembership,
    decomposition.trans (congrArg (fun value => value * compact) parabolicDecomposition)⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicDecomposition
