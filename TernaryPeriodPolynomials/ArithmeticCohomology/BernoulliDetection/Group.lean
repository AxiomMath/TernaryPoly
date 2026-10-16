module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BernoulliDetection.Radical

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open Matrix MvPolynomial

namespace TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers

theorem rationalCoefficient_coe {degree : ℕ} (element : RationalGL3)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter element polynomial).val =
      action (-1) (GeneralLinearGroup.map (algebraMap ℚ ℂ) element) polynomial.val := by
  change (1 : ℂ) • action (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) element)) polynomial.val = _
  rw [one_smul]
  congr 2

theorem line_radical_coefficient {degree : ℕ} (first second : ℚ)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter (lineUnipotent first second)
      polynomial).val =
        bind₁ ![X 0 - C (first : ℂ) * X 1 - C (second : ℂ) * X 2, X 1, X 2]
          polynomial.val := by
  rw [rationalCoefficient_coe, action_apply]
  have determinant : determinantCharacter (-1)
      (GeneralLinearGroup.map (algebraMap ℚ ℂ) (lineUnipotent first second)) = 1 := by
    simp [determinantCharacter, GeneralLinearGroup.det, lineUnipotent, upperUnipotent,
      Matrix.det_fin_three]
  rw [determinant, one_smul]
  unfold substitute
  congr 1
  ext index
  fin_cases index <;>
    simp [linearForm, ← map_inv, lineUnipotent, upperUnipotent, Fin.sum_univ_three]
  ring

theorem line_radical_integral_mem (first second : ℤ) :
    (lineUnipotent first second : IntegralGL3) ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (lineUnipotent first second)).val = lastRow
  ext index
  fin_cases index <;>
    simp [lastRow, reductionThree, Matrix.vecMul, lineUnipotent, upperUnipotent]

theorem line_radical_rational_mem (first second : ℤ) :
    lineUnipotent (first : ℚ) (second : ℚ) ∈ rationalLevel := by
  refine ⟨⟨lineUnipotent first second, line_radical_integral_mem first second⟩, ?_⟩
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalInclusion, lineUnipotent, upperUnipotent]

theorem line_standard_flag_fixed (element : RationalGL3)
    (parabolic_mem : element ∈ parabolic .line) :
    element⁻¹ • (QuotientGroup.mk 1 : Flags .line) = QuotientGroup.mk 1 := by
  change (QuotientGroup.mk (element⁻¹ * 1) : Flags .line) = QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  simpa using parabolic_mem

theorem line_radical_flag_fixed (first second : ℚ) :
    (lineUnipotent first second)⁻¹ • (QuotientGroup.mk 1 : Flags .line) =
      QuotientGroup.mk 1 := by
  apply line_standard_flag_fixed
  change InLineParabolic (lineUnipotent first second)
  simp [InLineParabolic, lineUnipotent, upperUnipotent]

noncomputable def primitiveRadical {degree : ℕ}
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (pair : ℤ × ℤ) : HomogeneousPoly degree :=
  primitive.val ![1, lineUnipotent (pair.1 : ℚ) (pair.2 : ℚ)] (QuotientGroup.mk 1)

theorem primitiveRadical_cocycle {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) (firstPair secondPair : ℤ × ℤ) :
    primitiveRadical primitive (firstPair + secondPair) = primitiveRadical primitive firstPair +
      rationalCoefficientComponent degree trivialCharacter
        (lineUnipotent (firstPair.1 : ℚ) (firstPair.2 : ℚ))
          (primitiveRadical primitive secondPair) := by
  have equality := line_primitive_radical_cocycle cocycle primitive primitive_eq
    ⟨lineUnipotent (firstPair.1 : ℚ) (firstPair.2 : ℚ),
      line_radical_rational_mem firstPair.1 firstPair.2⟩
    ⟨lineUnipotent (secondPair.1 : ℚ) (secondPair.2 : ℚ),
      line_radical_rational_mem secondPair.1 secondPair.2⟩
    (QuotientGroup.mk 1) (line_radical_flag_fixed firstPair.1 firstPair.2)
    (pure.1 firstPair.1 firstPair.2 secondPair.1 secondPair.2)
  simpa only [primitiveRadical, Prod.fst_add, Prod.snd_add, Int.cast_add,
    lineUnipotent_add] using equality

noncomputable def specializeFirst (second third : ℂ) (polynomial : Poly) : Polynomial ℂ :=
  (finSuccEquiv ℂ 2 polynomial).map (eval ![second, third])

theorem specializeFirst_eval (polynomial : Poly) (first second third : ℂ) :
    (specializeFirst second third polynomial).eval first = eval ![first, second, third] polynomial := by
  have coordinates : Fin.cons first ![second, third] = ![first, second, third] := by
    ext coordinate
    fin_cases coordinate <;> rfl
  simpa only [specializeFirst, coordinates] using
    (eval_eq_eval_mv_eval' ![second, third] first polynomial).symm

theorem specializeFirst_degree {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (second third : ℂ) : (specializeFirst second third polynomial.val).natDegree ≤ degree := by
  apply (Polynomial.natDegree_map_le).trans
  rw [natDegree_finSuccEquiv]
  apply (degreeOf_le_totalDegree polynomial.val 0).trans
  by_cases zero : polynomial.val = 0
  · simp [zero]
  · rw [polynomial.property.totalDegree zero]

theorem specializeFirst_radical {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (firstShift secondShift : ℚ) (second third : ℂ) :
    specializeFirst second third
      (rationalCoefficientComponent degree trivialCharacter
        (lineUnipotent firstShift secondShift) polynomial).val =
      Polynomial.taylor (-((firstShift : ℂ) * second + (secondShift : ℂ) * third))
        (specializeFirst second third polynomial.val) := by
  apply Polynomial.funext
  intro first
  rw [specializeFirst_eval, Polynomial.taylor_eval, specializeFirst_eval,
    line_radical_coefficient, eval_bind]
  have coordinates :
      (fun index => eval ![first, second, third]
        (![X 0 - C (firstShift : ℂ) * X 1 - C (secondShift : ℂ) * X 2, X 1, X 2] index)) =
      ![first + -((firstShift : ℂ) * second + (secondShift : ℂ) * third), second, third] := by
    ext index
    fin_cases index <;> simp
    ring
  rw [coordinates]

theorem primitiveRadical_specialize_cocycle {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (primitive : MaximalCochains degree trivialCharacter .line 1)
    (primitive_eq : ∀ vertices flag, cocycle.val.val vertices =
      primitive.val ![vertices 1, vertices 2] flag -
        primitive.val ![vertices 0, vertices 2] flag +
        primitive.val ![vertices 0, vertices 1] flag)
    (pure : PureMixedBadLine cocycle) (second third : ℂ) (firstPair secondPair : ℤ × ℤ) :
    specializeFirst second third (primitiveRadical primitive (firstPair + secondPair)).val =
      specializeFirst second third (primitiveRadical primitive firstPair).val +
        Polynomial.taylor (-((firstPair.1 : ℂ) * second + (firstPair.2 : ℂ) * third))
          (specializeFirst second third (primitiveRadical primitive secondPair).val) := by
  rw [primitiveRadical_cocycle cocycle primitive primitive_eq pure]
  have add_specialize (left right : Poly) : specializeFirst second third (left + right) =
      specializeFirst second third left + specializeFirst second third right := by
    simp [specializeFirst]
  rw [Submodule.coe_add, add_specialize, specializeFirst_radical]
  rfl

end TernaryPeriodPolynomials.PolynomialBernoulliDetection.Helpers
