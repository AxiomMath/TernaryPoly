module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.Comparison

@[expose] public section


/-!
# Radical equivariance of flag evaluations of plane source cocycles

The evaluation `x ↦ c(x)(q⁻¹)` of a plane source cocycle at a rational flag `q`
is equivariant under the whole rational conjugate radical `q N_P(ℚ) q⁻¹`, not only
under the arithmetic stabilizer. This comes from left invariance of induced sections
under the full adelic radical `N_P(𝔸)`.

This is a first ingredient of the stabilizer exactness obligation `FlagExact` of
`general_eisenstein_graph` (constant-term averaging along the radical).

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

theorem adelic_ext (first second : AdelicGL)
    (real : realGroup first = realGroup second)
    (finite : finiteGroup first = finiteGroup second) : first = second := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · exact congrArg (fun matrix => matrix.val row column) real
  · exact congrArg (fun matrix => matrix.val row column) finite

theorem realGroup_atInfinity' (matrix : RealGL3) : realGroup (atInfinity matrix) = matrix := by
  apply Units.ext
  rfl

theorem finiteGroup_atInfinity' (matrix : RealGL3) : finiteGroup (atInfinity matrix) = 1 := by
  apply Units.ext
  rfl

theorem realGroup_rationalGroup (matrix : RationalGL3) :
    realGroup (rationalGroup matrix) = GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix := by
  apply Units.ext
  rfl

/-- The real embedding of a rational radical element is an adelic radical element. -/
theorem atInfinity_planeUnipotent (s t : ℚ) :
    atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) (planeUnipotent s t)) =
      planeUnipotent (((s : ℝ), (0 : FiniteAdeles)) : Adeles) (((t : ℝ), (0 : FiniteAdeles)) : Adeles) := by
  apply adelic_ext
  · rw [realGroup_atInfinity']
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [realGroup, planeUnipotent, Matrix.GeneralLinearGroup.map_apply]
  · rw [finiteGroup_atInfinity']
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [finiteGroup, planeUnipotent, Matrix.GeneralLinearGroup.map_apply]

/-- The key adelic identity: right real translation by `q n q⁻¹` at the point `q⁻¹` is
left translation by the real radical element `n`. -/
theorem rationalGroup_inv_mul_atInfinity (q n : RationalGL3) :
    rationalGroup q⁻¹ * atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * n * q⁻¹)) =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) n) * rationalGroup q⁻¹ := by
  apply adelic_ext
  · rw [realGroup.map_mul, realGroup.map_mul, realGroup_atInfinity', realGroup_atInfinity',
      realGroup_rationalGroup, ← map_mul, ← map_mul]
    congr 1
    group
  · rw [finiteGroup.map_mul, finiteGroup.map_mul, finiteGroup_atInfinity',
      finiteGroup_atInfinity', mul_one, one_mul]

/-- Radical equivariance of the flag evaluation of a plane source cocycle. -/
theorem rationalEvaluation_radical_equivariant {degree : ℕ} (data : InducingData degree)
    (source : (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree)
    (isSource : IsSourceCocycle data .plane source) (q : RationalGL3) (s t : ℚ)
    (vertices : Fin 3 → RationalGL3) :
    TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation source
        (fun index => (q * planeUnipotent s t * q⁻¹) * vertices index) q =
      rationalCoefficientComponent degree data.chi (q * planeUnipotent s t * q⁻¹)
        (TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation source vertices q) := by
  have verticesEquality :
      (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ)
        ((q * planeUnipotent s t * q⁻¹) * vertices index)) =
      (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * planeUnipotent s t * q⁻¹) *
        GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index)) := by
    funext index
    exact map_mul _ _ _
  unfold TernaryPeriodPolynomials.GraphPieces.Comparison.rationalEvaluation
  rw [verticesEquality, isSource.2.2.1]
  change realCoefficientComponent degree data.chi
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * planeUnipotent s t * q⁻¹)) _ =
    realCoefficientComponent degree data.chi
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (q * planeUnipotent s t * q⁻¹)) _
  congr 1
  rw [rationalGroup_inv_mul_atInfinity, atInfinity_planeUnipotent]
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  exact (isSource.1 (fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (vertices index))
    monomial).2.2.2.1 _ _ _

end TernaryPeriodPolynomials.FlagExactness
