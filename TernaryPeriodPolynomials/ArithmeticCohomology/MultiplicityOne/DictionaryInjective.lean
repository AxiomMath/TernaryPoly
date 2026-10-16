module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarNonvanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.CongruenceFactorization

@[expose] public section


/-!
# Injectivity of the level-three dictionary

A nonzero smooth vector fixed by the level `{k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` has a nonzero scalar
realization (`levelThreeForm_eq_zero`). The proof is that of the spherical case
(`cuspScalarWeightedRealization_identity_nonzero`), with strong approximation for this level in
place of `GL₂(ℤ̂)`: every finite adelic matrix is a rational matrix times an element of the level
(`finiteGL_rational_levelThree_factorization`), because the second row of an element of `GL₂(ℤ̂)`
can be moved to `(0, 1)` modulo three by an integer matrix.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Manifold
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- An integer row with a unit entry is the second row of an invertible integer matrix. -/
theorem integerRow_exists_matrix_binary (row : Fin 2 → ℤ) (pivot : Fin 2)
    (unit : IsUnit (row pivot)) :
    ∃ matrix : GeneralLinearGroup (Fin 2) ℤ, (fun column => matrix.val 1 column) = row := by
  have exists_matrix : ∃ matrix : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit matrix ∧ (fun column => matrix 1 column) = row := by
    fin_cases pivot
    · refine ⟨!![0, 1; row 0, row 1], ?_, ?_⟩
      · apply (Matrix.isUnit_iff_isUnit_det _).mpr
        simpa [Matrix.det_fin_two] using unit.neg
      · funext column
        fin_cases column <;> rfl
    · refine ⟨!![1, 0; row 0, row 1], ?_, ?_⟩
      · apply (Matrix.isUnit_iff_isUnit_det _).mpr
        simpa [Matrix.det_fin_two] using unit
      · funext column
        fin_cases column <;> rfl
  obtain ⟨matrix, ⟨lift, lifted⟩, last_row⟩ := exists_matrix
  exact ⟨lift, by simpa only [lifted] using last_row⟩

/-- A nonzero residue row at three lifts to the second row of an invertible integer matrix. -/
theorem zmodThreeRow_exists_integral_matrix_binary (row : Fin 2 → ZMod 3) (nonzero : row ≠ 0) :
    ∃ matrix : GeneralLinearGroup (Fin 2) ℤ,
      ∀ column, (matrix.val 1 column : ZMod 3) = row column := by
  choose lift lifted unit using fun column => zmodThree_exists_centered_lift (row column)
  obtain ⟨pivot, pivot_nonzero⟩ : ∃ pivot, row pivot ≠ 0 := by
    by_contra none
    push Not at none
    exact nonzero (funext none)
  obtain ⟨matrix, equality⟩ := integerRow_exists_matrix_binary lift pivot (unit pivot pivot_nonzero)
  exact ⟨matrix, fun column => (congrArg (fun value : ℤ => (value : ZMod 3))
    (congrFun equality column)).trans (lifted column)⟩

/-- Every element of `GL₂(ℤ̂)` is an integer matrix times an element of the level at three. -/
theorem integralGL_binary_congruence_factorization
    (matrix : GeneralLinearGroup (Fin 2) IntegralAdeles) :
    ∃ (integer : GeneralLinearGroup (Fin 2) ℤ)
      (compact : GeneralLinearGroup (Fin 2) IntegralAdeles), PlaneLeviLevel compact ∧
      matrix = GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integer * compact := by
  let reduction := GeneralLinearGroup.map integralReduction matrix
  have row_ne : (fun column => (reduction⁻¹).val 1 column) ≠ 0 := by
    intro zero
    have diagonal := congrArg (fun value : GeneralLinearGroup (Fin 2) (ZMod 3) => value.val 1 1)
      (inv_mul_cancel reduction)
    change (∑ column, (reduction⁻¹).val 1 column * reduction.val column 1) = 1 at diagonal
    have entry_zero (column : Fin 2) : (reduction⁻¹).val 1 column = 0 := congrFun zero column
    simp only [entry_zero, zero_mul, Finset.sum_const_zero] at diagonal
    exact zero_ne_one diagonal
  obtain ⟨lift, lifted⟩ := zmodThreeRow_exists_integral_matrix_binary
    (fun column => (reduction⁻¹).val 1 column) row_ne
  let mapped := GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) lift
  let compact := mapped * matrix
  have second_row (column : Fin 2) :
      (GeneralLinearGroup.map integralReduction mapped).val 1 column =
        (reduction⁻¹).val 1 column := by
    simpa [mapped, GeneralLinearGroup.map_apply] using lifted column
  have product : GeneralLinearGroup.map integralReduction compact =
      GeneralLinearGroup.map integralReduction mapped * reduction :=
    map_mul (GeneralLinearGroup.map integralReduction) mapped matrix
  have entry (column : Fin 2) : (GeneralLinearGroup.map integralReduction compact).val 1 column =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 column := by
    have identity := congrArg (fun value : GeneralLinearGroup (Fin 2) (ZMod 3) =>
      value.val 1 column) (inv_mul_cancel reduction)
    simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.coe_one] at identity
    rw [product, GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, second_row 0,
      second_row 1]
    exact identity
  have level : PlaneLeviLevel compact :=
    And.intro ((entry 0).trans (by simp)) ((entry 1).trans (by simp))
  refine ⟨lift⁻¹, compact, level, ?_⟩
  rw [map_inv]
  change matrix = mapped⁻¹ * (mapped * matrix)
  rw [inv_mul_cancel_left]

/-- Every finite adelic matrix is a rational matrix times an element of the level at three. -/
theorem finiteGL_rational_levelThree_factorization (finite : BinaryFiniteGL) :
    ∃ (rational : BinaryRationalGL) (compact : GeneralLinearGroup (Fin 2) IntegralAdeles),
      PlaneLeviLevel compact ∧
      finite = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding compact := by
  obtain ⟨rational, integral, factorization⟩ := finiteGL_rational_integral_factorization finite
  obtain ⟨integer, compact, level, compact_factorization⟩ :=
    integralGL_binary_congruence_factorization integral
  refine ⟨rational * GeneralLinearGroup.map (Int.castRingHom ℚ) integer, compact, level, ?_⟩
  rw [factorization, compact_factorization]
  simp only [map_mul, mul_assoc, finiteGL_map_integer]

/-- Moving a rational finite matrix past the real factor. -/
theorem atInfinity_mul_atFinite_rational (rational : BinaryRationalGL) (real : BinaryRealGL) :
    atInfinity real * atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) =
      GeneralLinearGroup.map rationalAdele rational *
        atInfinity ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * real) := by
  have commute := atInfinity_commute_atFinite (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)
    (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)
  have conjugate : atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) *
      atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) *
        (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational))⁻¹ =
      atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) := by
    rw [commute.eq, mul_inv_cancel_right]
  rw [binaryRationalMatrix_split, atInfinity_mul, atInfinity_inv]
  calc atInfinity real * atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)
      = atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) * atInfinity real :=
        (atInfinity_commute_atFinite _ _).eq
    _ = (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) *
        atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational) *
          (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational))⁻¹) * atInfinity real := by
        rw [conjugate]
    _ = _ := mul_assoc _ _ _

/-- Strong approximation for the level at three. -/
theorem binaryAdelic_rational_real_levelThree (matrix : BinaryAdelicGL) :
    ∃ (rational : BinaryRationalGL) (real : BinaryRealGL)
      (compact : GeneralLinearGroup (Fin 2) IntegralAdeles), PlaneLeviLevel compact ∧
      matrix = GeneralLinearGroup.map rationalAdele rational * atInfinity real *
        atFinite (GeneralLinearGroup.map integralEmbedding compact) := by
  obtain ⟨real, finite, split⟩ := binaryAdelic_exists_real_finite matrix
  obtain ⟨rational, compact, level, finite_split⟩ :=
    finiteGL_rational_levelThree_factorization finite
  refine ⟨rational, (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * real, compact, level, ?_⟩
  rw [split, finite_split, atFinite_mul,
    ← mul_assoc (atInfinity real)
      (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational))
      (atFinite (GeneralLinearGroup.map integralEmbedding compact)),
    atInfinity_mul_atFinite_rational]

/-- A nonzero level-three vector has a nonzero real-group realization. -/
theorem levelThree_realization_exists_real_nonzero (σ : CuspidalRepresentation) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ) (nonzero : v ≠ 0) :
    ∃ real : BinaryRealGL, σ.realize v (atInfinity real) ≠ 0 := by
  obtain ⟨base, base_nonzero⟩ := cuspScalarWeightedRealization_nonzero σ 0 v nonzero
  rw [cuspScalarWeightedRealization_I] at base_nonzero
  obtain ⟨rational, real, compact, level, split⟩ := binaryAdelic_rational_real_levelThree base
  refine ⟨real, ?_⟩
  rw [split, mul_assoc, σ.leftRational,
    cuspRealization_right_eigenvector σ v _ 1 (by simpa only [one_smul] using hv compact level),
    one_mul] at base_nonzero
  exact base_nonzero

theorem planeLeviLevel_reflection :
    PlaneLeviLevel (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
      binaryIntegerReflection) := by
  refine And.intro ?_ ?_
  · simp [GeneralLinearGroup.map_apply, binaryIntegerReflection]
  · simp [GeneralLinearGroup.map_apply, binaryIntegerReflection]

theorem levelThree_realization_reflection (σ : CuspidalRepresentation) (v : σ.smooth)
    (hv : v.val ∈ levelThreeValues σ) (matrix : BinaryRealGL) :
    σ.realize v (atInfinity (UpperHalfPlane.J * matrix)) = σ.realize v (atInfinity matrix) := by
  have real_equality : GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryIntegerReflection) = UpperHalfPlane.J := by
    rw [← binaryIntegerReflection_real]
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply]
    change algebraMap ℚ ℝ (binaryIntegerReflection.val row column : ℚ) =
      (binaryIntegerReflection.val row column : ℝ)
    simp only [map_intCast]
  have fixed : σ.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryIntegerReflection))) v.val = v.val := by
    rw [finiteGL_map_integer]
    exact hv _ planeLeviLevel_reflection
  simpa only [real_equality] using cuspRealization_rational_real σ v
    (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryIntegerReflection) fixed matrix

theorem levelThree_realization_exists_positive_nonzero (σ : CuspidalRepresentation)
    (v : σ.smooth) (hv : v.val ∈ levelThreeValues σ) (nonzero : v ≠ 0) :
    ∃ real : BinaryRealGL, 0 < real.val.det ∧ σ.realize v (atInfinity real) ≠ 0 := by
  obtain ⟨real, real_nonzero⟩ := levelThree_realization_exists_real_nonzero σ v hv nonzero
  by_cases positive : 0 < real.val.det
  · exact ⟨real, positive, real_nonzero⟩
  · refine ⟨UpperHalfPlane.J * real, ?_, ?_⟩
    · have negative : real.val.det < 0 :=
        lt_of_le_of_ne (le_of_not_gt positive) (GeneralLinearGroup.det_ne_zero real)
      have reflection_det : UpperHalfPlane.J.val.det = -1 := by
        norm_num [UpperHalfPlane.val_J, Matrix.det_fin_two]
      rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, reflection_det, neg_one_mul]
      exact neg_pos.mpr negative
    · rwa [levelThree_realization_reflection σ v hv]

/-- A nonzero classical level-three vector has a nonzero scalar function. -/
theorem levelThree_scalar_exists_nonzero (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (v : σ.smooth) (hv : v ∈ levelThreeClassicalVectors σ halfWeight)
    (nonzero : v ≠ 0) :
    ∃ point : UpperHalfPlane, cuspScalarWeightedRealization σ halfWeight v 1 point ≠ 0 := by
  obtain ⟨real, positive, real_nonzero⟩ :=
    levelThree_realization_exists_positive_nonzero σ v hv.1 nonzero
  refine ⟨real • UpperHalfPlane.I, ?_⟩
  intro zero
  have identity := cuspScalarWeightedRealization_positive σ central_positive halfWeight v hv.2.1
    real positive UpperHalfPlane.I
  rw [zero, mul_zero] at identity
  exact real_nonzero (by simpa only [UpperHalfPlane.coe_I, cuspScalarWeightedRealization_I] using
    identity)

/-- **Injectivity of the dictionary**: a classical level-three vector with zero cusp form is
zero. -/
theorem levelThreeForm_eq_zero (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) (v : σ.smooth)
    (hv : v ∈ levelThreeClassicalVectors σ halfWeight)
    (zero : levelThreeForm σ halfWeight negative v hv = 0) : v = 0 := by
  by_contra nonzero
  obtain ⟨point, point_nonzero⟩ := levelThree_scalar_exists_nonzero σ central_positive halfWeight
    v hv nonzero
  apply point_nonzero
  have equal := congrArg (fun form : CuspForm LevelThree.LevelThreeHeckeSum.levelThree
    (-2 * halfWeight) => (form : UpperHalfPlane → ℂ) point) zero
  exact equal

theorem levelThreeToCuspForm_injective (σ : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → σ.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (negative : halfWeight < 0) :
    Function.Injective (levelThreeToCuspForm σ halfWeight negative) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  exact levelThreeForm_eq_zero σ central_positive halfWeight negative x.1 x.2 hx

end TernaryPeriodPolynomials.MultiplicityOne
