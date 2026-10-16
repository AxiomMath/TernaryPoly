module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Frames

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers TernaryPeriodPolynomials.PolynomialBadLineNormalization.Geometry TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths TernaryPeriodPolynomials.PolynomialBadLineNormalization.Frames

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization.Normalization

theorem realized_at_identity {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {paths : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional paths cocycle)
    (first second : rationalLevel) :
    cocycle.val.val ![1, first.val, first.val * second.val] =
      functional (paths first + translateChain first.val (paths second) - paths (first * second)) := by
  simpa only [Subgroup.coe_one, Subgroup.coe_mul, inv_one, one_mul, map_one,
    Module.End.one_apply, inv_mul_cancel_left] using realization 1 first (first * second)

theorem radical_mul (first second third fourth : ℚ) :
    lineUnipotent first second * lineUnipotent third fourth =
      lineUnipotent (first + third) (second + fourth) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, add_comm]

theorem normalized_pure {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {original : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional (normalizedPaths original) cocycle) :
    PureMixedBadLine cocycle := by
  constructor
  · intro first second third fourth
    let left : rationalLevel := ⟨lineUnipotent (first : ℚ) (second : ℚ),
      unipotent_in_level first second⟩
    let right : rationalLevel := ⟨lineUnipotent (third : ℚ) (fourth : ℚ),
      unipotent_in_level third fourth⟩
    have left_radical : IsRationalRadical left.val := ⟨_, _, rfl⟩
    have right_radical : IsRationalRadical right.val := ⟨_, _, rfl⟩
    have product_radical : IsRationalRadical (left * right).val :=
      ⟨_, _, radical_mul _ _ _ _⟩
    rw [show lineUnipotent (first : ℚ) (second : ℚ) = left.val from rfl,
      show lineUnipotent (third : ℚ) (fourth : ℚ) = right.val from rfl,
      realized_at_identity realization left right,
      normalizedPaths_radical original left left_radical,
      normalizedPaths_radical original right right_radical,
      normalizedPaths_radical original (left * right) product_radical]
    simp
  · intro first second first_levi second_levi
    let left : rationalLevel := ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) first,
      integral_in_level first first_levi.1⟩
    let right : rationalLevel := ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) second,
      integral_in_level second second_levi.1⟩
    have left_levi : IsRationalLevi left.val := integral_levi first first_levi
    have right_levi : IsRationalLevi right.val := integral_levi second second_levi
    have product_levi : IsRationalLevi (left * right).val := levi_mul left_levi right_levi
    rw [map_mul]
    change cocycle.val.val ![1, left.val, left.val * right.val] = 0
    rw [realized_at_identity realization left right,
      normalizedPaths_levi original left left_levi,
      normalizedPaths_levi original right right_levi,
      normalizedPaths_levi original (left * right) product_levi]
    rw [map_sub (translateChain left.val)]
    simp only [Subgroup.coe_mul, translateChain_mul]
    have cancellation : connector - translateChain left.val connector +
        (translateChain left.val connector -
          translateChain left.val (translateChain right.val connector)) -
        (connector - translateChain left.val (translateChain right.val connector)) = 0 := by abel
    rw [cancellation, map_zero]

theorem binary_conjugate_radical (element : RationalGL3)
    (binary : element = binaryA ∨ element = binaryB ∨ element = binaryR)
    (first second : ℚ) :
    IsRationalRadical (element⁻¹ * (lineUnipotent first second * element)) := by
  rcases binary with rfl | rfl | rfl
  · refine ⟨first + 3 * second, -first - 2 * second, ?_⟩
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryA, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two] <;> ring
  · refine ⟨-first - 3 * second, second, ?_⟩
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryB, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two, sub_eq_add_neg, mul_comm]
  · refine ⟨-first, second, ?_⟩
    apply Units.ext
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [binaryR, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.cons_val_two]

theorem normalized_mixedBarEdge {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {original : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional (normalizedPaths original) cocycle)
    (element : RationalGL3)
    (binary : element = binaryA ∨ element = binaryB ∨ element = binaryR)
    (first second : ℤ) :
    mixedBarEdge cocycle element (lineUnipotent (first : ℚ) (second : ℚ)) =
      -(functional (translateChain (lineUnipotent (first : ℚ) (second : ℚ))
        (connector - translateChain element connector) -
        (connector - translateChain element connector))).val := by
  let levi : rationalLevel := ⟨element, binary_in_level element binary⟩
  let radical : rationalLevel := ⟨lineUnipotent (first : ℚ) (second : ℚ),
    unipotent_in_level first second⟩
  have levi_property : IsRationalLevi levi.val := binary_levi element binary
  have radical_property : IsRationalRadical radical.val := ⟨_, _, rfl⟩
  have conjugate_property : IsRationalRadical (levi⁻¹ * (radical * levi)).val :=
    binary_conjugate_radical element binary _ _
  have first_value := realization 1 levi (radical * levi)
  have second_value := realization 1 radical (radical * levi)
  simp only [Subgroup.coe_one, Subgroup.coe_mul, inv_one, one_mul, map_one,
    Module.End.one_apply, inv_mul_cancel_left,
    normalizedPaths_levi original levi levi_property,
    normalizedPaths_radical original radical radical_property,
    normalizedPaths_radical original (levi⁻¹ * (radical * levi)) conjugate_property,
    map_zero, add_zero, zero_add] at first_value second_value
  change (cocycle.val.val ![1, levi.val, (radical * levi).val]).val -
    (cocycle.val.val ![1, radical.val, (radical * levi).val]).val = _
  simp only [Subgroup.coe_mul]
  rw [first_value, second_value]
  simp only [map_sub, Submodule.coe_sub]
  abel

theorem bernoulliOperator_neg (degree : ℕ) (parameter polynomial : Poly) :
    bernoulliOperator degree parameter (-polynomial) =
      -bernoulliOperator degree parameter polynomial := by
  have derivatives : ∀ order : ℕ,
      ((fun value : Poly => MvPolynomial.pderiv 0 value)^[order]) (-polynomial) =
        -((fun value : Poly => MvPolynomial.pderiv 0 value)^[order]) polynomial := by
    intro order
    induction order with
    | zero => rfl
    | succ order induction_hypothesis =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', induction_hypothesis,
        map_neg]
  simp only [bernoulliOperator, derivatives, mul_neg, Finset.sum_neg_distrib]

theorem bernoulliOperator_zero (degree : ℕ) (parameter : Poly) :
    bernoulliOperator degree parameter 0 = 0 := by
  have derivatives : ∀ order : ℕ,
      ((fun value : Poly => MvPolynomial.pderiv 0 value)^[order]) 0 = 0 := by
    intro order
    induction order with
    | zero => rfl
    | succ order induction_hypothesis =>
      rw [Function.iterate_succ_apply', induction_hypothesis, map_zero]
  simp [bernoulliOperator, derivatives]

theorem normalized_coordinate_A {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (properties : IsPolynomialFunctional polynomial functional)
    {original : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional (normalizedPaths original) cocycle) :
    mixedBernoulliCoordinate cocycle binaryA = -bernoulliObstruction polynomial := by
  have first_edge := normalized_mixedBarEdge realization binaryA (Or.inl rfl) 1 0
  have second_edge := normalized_mixedBarEdge realization binaryA (Or.inl rfl) 0 1
  simp only [Int.cast_one, Int.cast_zero, first_radical_apartment,
    rationalFrame, frameOne_value properties] at first_edge
  simp only [Int.cast_one, Int.cast_zero, second_radical_apartments,
    map_add, Submodule.coe_add, rationalFrame, frameOne_value properties,
    frameTwo_value properties, frameThree_value properties] at second_edge
  simp only [mixedBernoulliCoordinate, first_edge, second_edge,
    bernoulliOperator_neg, bernoulliObstruction]
  simp only [sub_eq_add_neg, mul_neg, neg_add_rev, neg_neg]
  abel

theorem normalized_coordinate_zero {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {original : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional (normalizedPaths original) cocycle)
    (element : RationalGL3) (binary : element = binaryB ∨ element = binaryR) :
    mixedBernoulliCoordinate cocycle element = 0 := by
  have fixed : connector - translateChain element connector = 0 := by
    rw [binary_connector_fixed element binary, sub_self]
  have first_edge := normalized_mixedBarEdge realization element (Or.inr binary) 1 0
  have second_edge := normalized_mixedBarEdge realization element (Or.inr binary) 0 1
  simp only [fixed, map_zero, sub_self, Submodule.coe_zero, neg_zero,
    Int.cast_one, Int.cast_zero] at first_edge second_edge
  simp only [mixedBernoulliCoordinate, first_edge, second_edge,
    bernoulliOperator_zero, mul_zero, sub_self]

theorem normalized_bad_line {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (properties : IsPolynomialFunctional polynomial functional)
    {original : rationalLevel → EdgeChains}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realization : RealizesPathClass functional (normalizedPaths original) cocycle) :
    NormalizedBadLine polynomial cocycle :=
  ⟨normalized_pure realization, normalized_coordinate_A properties realization,
    normalized_coordinate_zero realization binaryB (Or.inl rfl),
    normalized_coordinate_zero realization binaryR (Or.inr rfl)⟩

end TernaryPeriodPolynomials.PolynomialBadLineNormalization.Normalization
