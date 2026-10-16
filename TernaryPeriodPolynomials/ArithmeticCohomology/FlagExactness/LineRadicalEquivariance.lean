module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.RadicalEquivariance

@[expose] public section


/-!
# Radical equivariance of flag evaluations of line source cocycles

Line-side analogue of `rationalEvaluation_radical_equivariant`: the evaluation
`x ↦ c(x)(q⁻¹)` of a line source cocycle at a rational flag `q` is equivariant
under the whole rational conjugate line radical `q N_Q(ℚ) q⁻¹`. This uses left
invariance of line-induced sections under the full adelic line radical.

Ingredient of the line half of the stabilizer exactness obligation `FlagExact`
of `general_eisenstein_graph`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- The real embedding of a rational line-radical element is an adelic line-radical element. -/
theorem atInfinity_lineUnipotent (s t : ℚ) :
    atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineUnipotent s t)) =
      lineUnipotent (((s : ℝ), (0 : FiniteAdeles)) : Adeles) (((t : ℝ), (0 : FiniteAdeles)) : Adeles) := by
  apply adelic_ext
  · rw [realGroup_atInfinity']
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realGroup, lineUnipotent, upperUnipotent, Matrix.GeneralLinearGroup.map_apply]
  · rw [finiteGroup_atInfinity']
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGroup, lineUnipotent, upperUnipotent, Matrix.GeneralLinearGroup.map_apply]

/-- Radical equivariance of the flag evaluation of a line source cocycle. -/
theorem rationalEvaluation_line_radical_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .line source) (q : RationalGL3) (s t : ℚ)
    (vertices : Fin 3 → RationalGL3) :
    TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation source
        (fun index => (q * lineUnipotent s t * q⁻¹) * vertices index) q =
      rationalCoefficientComponent degree data.chi (q * lineUnipotent s t * q⁻¹)
        (TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation source vertices q) := by
  have verticesEquality :
      (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((q * lineUnipotent s t * q⁻¹) * vertices index)) =
      (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * lineUnipotent s t * q⁻¹) *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) := by
    funext index
    exact map_mul _ _ _
  unfold TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation
  rw [verticesEquality, isSource.2.2.1]
  change realCoefficientComponent degree data.chi
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * lineUnipotent s t * q⁻¹)) _ =
    realCoefficientComponent degree data.chi
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * lineUnipotent s t * q⁻¹)) _
  congr 1
  rw [rationalGroup_inv_mul_atInfinity, atInfinity_lineUnipotent]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
    monomial).2.2.2.1 _ _ _

end TernaryPeriodPolynomials.FlagExactness
