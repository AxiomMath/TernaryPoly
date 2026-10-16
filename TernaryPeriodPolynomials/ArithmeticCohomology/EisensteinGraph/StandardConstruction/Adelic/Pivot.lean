module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Decomposition

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicPivot

theorem valued_ratios {K Value : Type} [Field K] [LinearOrderedCommGroupWithZero Value]
    (valuation : Valuation K Value) (first second : K) (nonzero : first ≠ 0 ∨ second ≠ 0) :
    ∃ shift left right : valuation.integer,
      first = (first + second * shift.val) * left.val ∧
        second = (first + second * shift.val) * right.val := by
  by_cases dominates : valuation second ≤ valuation first
  · have firstNonzero : first ≠ 0 := by
      intro zero
      have secondZero : second = 0 := by
        apply (map_eq_zero valuation).mp
        simpa only [zero, map_zero, le_zero_iff] using dominates
      exact nonzero.elim (fun h => h zero) (fun h => h secondZero)
    refine ⟨0, 1, ⟨second / first, LocalDecomposition.ratio_integral valuation second first firstNonzero dominates⟩, ?_, ?_⟩
    · simp
    · simp [mul_div_cancel₀, firstNonzero]
  · have strict : valuation first < valuation second := lt_of_not_ge dominates
    have valSum : valuation (first + second) = valuation second := valuation.map_add_eq_of_lt_right strict
    have sumNonzero : first + second ≠ 0 := by
      intro zero
      rw [zero, map_zero] at valSum
      have : valuation first < 0 := valSum ▸ strict
      exact (not_lt_of_ge zero_le) this
    have leftIntegral : first / (first + second) ∈ valuation.integer :=
      LocalDecomposition.ratio_integral valuation first (first + second) sumNonzero (by rw [valSum]; exact strict.le)
    have rightIntegral : second / (first + second) ∈ valuation.integer :=
      LocalDecomposition.ratio_integral valuation second (first + second) sumNonzero (by rw [valSum])
    refine ⟨1, ⟨_, leftIntegral⟩, ⟨_, rightIntegral⟩, ?_, ?_⟩
    all_goals simp [mul_div_cancel₀, sumNonzero]

theorem field_ratios {K : Type*} [Field K] (first second : K) (nonzero : first ≠ 0 ∨ second ≠ 0) :
    ∃ shift left right : K, first = (first + second * shift) * left ∧
      second = (first + second * shift) * right := by
  by_cases firstNonzero : first ≠ 0
  · exact ⟨0, 1, second / first, by simp, by simp [mul_div_cancel₀, firstNonzero]⟩
  · have firstZero := not_ne_iff.mp firstNonzero
    have secondNonzero : second ≠ 0 := nonzero.resolve_left firstNonzero
    exact ⟨1, 0, 1, by simp [firstZero], by simp [firstZero]⟩

theorem unimodular_ratios (first second leftInverse rightInverse : Adeles)
    (unimodular : first * leftInverse + second * rightInverse = 1) :
    ∃ shift left right : Adeles, first = (first + second * shift) * left ∧
      second = (first + second * shift) * right := by
  have realNonzero : first.1 ≠ 0 ∨ second.1 ≠ 0 := by
    by_contra bothZero
    push Not at bothZero
    have equation := congrArg Prod.fst unimodular
    change first.1 * leftInverse.1 + second.1 * rightInverse.1 = 1 at equation
    simp [bothZero.1, bothZero.2] at equation
  obtain ⟨realShift, realLeft, realRight, realFirst, realSecond⟩ := field_ratios first.1 second.1 realNonzero
  have localRatios : ∀ place : FinitePlace, ∃ shift left right : place.adicCompletionIntegers ℚ,
      first.2 place = (first.2 place + second.2 place * shift.val) * left.val ∧
        second.2 place = (first.2 place + second.2 place * shift.val) * right.val := by
    intro place
    apply valued_ratios Valued.v
    by_contra bothZero
    push Not at bothZero
    have equation := congrArg (fun value : Adeles => value.2 place) unimodular
    change first.2 place * leftInverse.2 place + second.2 place * rightInverse.2 place = 1 at equation
    simp [bothZero.1, bothZero.2] at equation
  choose shifts lefts rights firstEquation secondEquation using localRatios
  refine ⟨(realShift, integralEmbedding shifts), (realLeft, integralEmbedding lefts),
    (realRight, integralEmbedding rights), ?_, ?_⟩
  · apply Prod.ext realFirst
    apply FiniteAdeleRing.ext ℚ
    exact firstEquation
  · apply Prod.ext realSecond
    apply FiniteAdeleRing.ext ℚ
    exact secondEquation

theorem unit_pivot (first second leftInverse rightInverse : Adeles)
    (unimodular : first * leftInverse + second * rightInverse = 1) :
    ∃ shift : Adeles, ∃ pivot : Adelesˣ, pivot.val = first + second * shift := by
  obtain ⟨shift, left, right, firstEquation, secondEquation⟩ :=
    unimodular_ratios first second leftInverse rightInverse unimodular
  have inverse : (first + second * shift) * (left * leftInverse + right * rightInverse) = 1 := by
    calc
      _ = ((first + second * shift) * left) * leftInverse +
          ((first + second * shift) * right) * rightInverse := by ring
      _ = 1 := by rw [← firstEquation, ← secondEquation, unimodular]
  exact ⟨shift, Units.mkOfMulEqOne _ _ inverse, rfl⟩

theorem matrix_unit_pivot (matrix : BinaryAdelicGL) :
    ∃ shift : Adeles, ∃ pivot : Adelesˣ, pivot.val = matrix.val 0 0 + matrix.val 1 0 * shift := by
  apply unit_pivot _ _ (matrix.inv 0 0) (matrix.inv 0 1)
  have equation := congrArg (fun m : Matrix (Fin 2) (Fin 2) Adeles => m 0 0) matrix.inv_val
  simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, mul_comm] using equation

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.AdelicPivot
