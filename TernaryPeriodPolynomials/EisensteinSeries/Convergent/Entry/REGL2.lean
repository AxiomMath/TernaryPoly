module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.REEuler

@[expose] public section


/-!
# R-e: Column reduction in `GL₂(𝔸_f)`

`gl2_column_reduction`: every `A ∈ GL₂(𝔸_f)` becomes lower triangular after right multiplication by an element of `SL₂(Ẑ)` (valuation-subring dichotomy at each place, assembled in the product of the integers).

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- Local column reduction in a valuation subring: one column operation of determinant one kills the
`(0,1)` entry of the row `(a,b)`. -/
theorem local_column_reduction {K : Type*} [Field K] (O : ValuationSubring K) (a b : K) :
    ∃ k₀₁ k₁₀ k₀₀ k₁₁ : O, k₀₀ * k₁₁ - k₀₁ * k₁₀ = 1 ∧ a * k₀₁ + b * k₁₁ = 0 := by
  by_cases hb : b = 0
  · exact ⟨0, 0, 1, 1, by simp, by simp [hb]⟩
  · by_cases ha : a = 0
    · exact ⟨-1, 1, 0, 0, by simp, by simp [ha]⟩
    · rcases O.mem_or_inv_mem (a / b) with h | h
      · refine ⟨-1, 1, 0, ⟨a / b, h⟩, by simp, ?_⟩
        push_cast
        field_simp
        ring
      · have h' : b / a ∈ O := by simpa [inv_div] using h
        refine ⟨⟨-(b / a), O.neg_mem _ h'⟩, 0, 1, 1, by simp, ?_⟩
        push_cast
        field_simp
        ring

/-- Global column reduction: every `A ∈ GL₂(𝔸_f)` becomes lower triangular after right multiplication by an
integral matrix of determinant one. -/
theorem gl2_column_reduction (A : GeneralLinearGroup (Fin 2) FiniteAdeles) :
    ∃ k : Matrix.SpecialLinearGroup (Fin 2) IntegralAdeles,
      (A.val * (k.val.map integralEmbedding)) 0 1 = 0 := by
  choose k₀₁ k₁₀ k₀₀ k₁₁ hdet hrel using fun place : FinitePlace =>
    local_column_reduction (place.adicCompletionIntegers ℚ) (finiteEvaluation place (A.val 0 0))
      (finiteEvaluation place (A.val 0 1))
  let K : Matrix (Fin 2) (Fin 2) IntegralAdeles := !![k₀₀, k₀₁; k₁₀, k₁₁]
  have determinant : K.det = 1 := by
    rw [Matrix.det_fin_two]
    funext place
    exact hdet place
  refine ⟨⟨K, determinant⟩, ?_⟩
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro place
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  exact hrel place

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
