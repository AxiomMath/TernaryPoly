module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Paths

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers TernaryPeriodPolynomials.PolynomialBadLineNormalization.Geometry TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization.Frames

def rationalFrame (frame : IntegralGL3) : RationalGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) frame

theorem quotient_smul (first second : RationalGL3) :
    first • (QuotientGroup.mk second : Edges) = QuotientGroup.mk (first * second) := rfl

def frameOne : IntegralGL3 :=
  ⟨!![0,-1,0;0,-1,-1;1,-2,-2], !![0,-2,1;-1,0,0;1,-1,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

def frameTwo : IntegralGL3 :=
  ⟨!![0,1,-2;0,0,-1;1,1,-2], !![-1,0,1;1,-2,0;0,-1,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

def frameThree : IntegralGL3 :=
  ⟨!![0,-2,-1;0,-1,-1;1,-2,-2], !![0,-2,1;-1,1,0;1,-2,0], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

theorem frameOne_value {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (properties : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frameOne))).val =
      MvPolynomial.bind₁ ![MvPolynomial.X 2 - 2 * MvPolynomial.X 1,
        -MvPolynomial.X 0, MvPolynomial.X 0 - MvPolynomial.X 1] polynomial.val := by
  have evaluation := properties.2 frameOne (by intro column; fin_cases column <;> decide)
  have determinant : (GeneralLinearGroup.det frameOne : ℤ) = 1 := by
    norm_num [GeneralLinearGroup.det, frameOne, Matrix.det_fin_three, Matrix.cons_val_two]
  have forms : linearForm ((GeneralLinearGroup.map (Int.castRingHom ℂ) frameOne)⁻¹).val =
      ![MvPolynomial.X 2 - 2 * MvPolynomial.X 1,
        -MvPolynomial.X 0, MvPolynomial.X 0 - MvPolynomial.X 1] := by
    rw [← map_inv]
    funext index
    fin_cases index <;>
      simp [linearForm, frameOne, GeneralLinearGroup.map_apply,
        Fin.sum_univ_three, Matrix.cons_val_two] <;> ring
  simpa only [determinant, Int.cast_one, MvPolynomial.C_1, one_mul, substitute, forms]
    using evaluation

theorem frameTwo_value {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (properties : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frameTwo))).val =
      -MvPolynomial.bind₁ ![MvPolynomial.X 2 - MvPolynomial.X 0,
        MvPolynomial.X 0 - 2 * MvPolynomial.X 1, -MvPolynomial.X 1] polynomial.val := by
  have evaluation := properties.2 frameTwo (by intro column; fin_cases column <;> decide)
  have determinant : (GeneralLinearGroup.det frameTwo : ℤ) = -1 := by
    norm_num [GeneralLinearGroup.det, frameTwo, Matrix.det_fin_three, Matrix.cons_val_two]
  have forms : linearForm ((GeneralLinearGroup.map (Int.castRingHom ℂ) frameTwo)⁻¹).val =
      ![MvPolynomial.X 2 - MvPolynomial.X 0,
        MvPolynomial.X 0 - 2 * MvPolynomial.X 1, -MvPolynomial.X 1] := by
    rw [← map_inv]
    funext index
    fin_cases index <;>
      simp [linearForm, frameTwo, GeneralLinearGroup.map_apply,
        Fin.sum_univ_three, Matrix.cons_val_two] <;> ring
  simpa only [determinant, Int.cast_neg, Int.cast_one, map_neg, MvPolynomial.C_1,
    neg_one_mul, substitute, forms] using evaluation

theorem frameThree_value {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (properties : IsPolynomialFunctional polynomial functional) :
    (functional (apartment (GeneralLinearGroup.map (Int.castRingHom ℚ) frameThree))).val =
      MvPolynomial.bind₁ ![MvPolynomial.X 2 - 2 * MvPolynomial.X 1,
        MvPolynomial.X 1 - MvPolynomial.X 0, MvPolynomial.X 0 - 2 * MvPolynomial.X 1]
        polynomial.val := by
  have evaluation := properties.2 frameThree (by intro column; fin_cases column <;> decide)
  have determinant : (GeneralLinearGroup.det frameThree : ℤ) = 1 := by
    norm_num [GeneralLinearGroup.det, frameThree, Matrix.det_fin_three, Matrix.cons_val_two]
  have forms : linearForm ((GeneralLinearGroup.map (Int.castRingHom ℂ) frameThree)⁻¹).val =
      ![MvPolynomial.X 2 - 2 * MvPolynomial.X 1,
        MvPolynomial.X 1 - MvPolynomial.X 0, MvPolynomial.X 0 - 2 * MvPolynomial.X 1] := by
    rw [← map_inv]
    funext index
    fin_cases index <;>
      simp [linearForm, frameThree, GeneralLinearGroup.map_apply,
        Fin.sum_univ_three, Matrix.cons_val_two] <;> ring
  simpa only [determinant, Int.cast_one, MvPolynomial.C_1, one_mul, substitute, forms]
    using evaluation


theorem first_radical_apartment :
    translateChain (lineUnipotent 1 0) (connector - translateChain binaryA connector) -
      (connector - translateChain binaryA connector) = apartment (rationalFrame frameOne) := by
  have edge_first : (QuotientGroup.mk (lineUnipotent 1 0 * (weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_second : (QuotientGroup.mk ((weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl ^ 2 * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_third : (QuotientGroup.mk (lineUnipotent 1 0 * (weyl ^ 2)) : Edges) =
      QuotientGroup.mk (weyl ^ 2) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_fourth : (QuotientGroup.mk (lineUnipotent 1 0 * (binaryA * (weyl * swapFirstTwo))) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_fifth : (QuotientGroup.mk (binaryA * (weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl ^ 2) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_sixth : (QuotientGroup.mk (lineUnipotent 1 0 * (binaryA * (weyl ^ 2))) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_seventh : (QuotientGroup.mk (binaryA * (weyl ^ 2)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, weyl, swapFirstTwo, binaryA, upperUnipotent,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  simp only [connector, map_sub, translateChain_single, apartment, quotient_smul]
  rw [edge_first, edge_second, edge_third, edge_fourth, edge_fifth, edge_sixth, edge_seventh]
  abel


theorem second_radical_apartments :
    translateChain (lineUnipotent 0 1) (connector - translateChain binaryA connector) -
      (connector - translateChain binaryA connector) =
      apartment (rationalFrame frameOne) + apartment (rationalFrame frameTwo) +
        apartment (rationalFrame frameThree) := by
  have edge_first : (QuotientGroup.mk (lineUnipotent 0 1 * (weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameTwo * weyl) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_second : (QuotientGroup.mk ((weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl ^ 2 * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_third : (QuotientGroup.mk (lineUnipotent 0 1 * (weyl ^ 2)) : Edges) =
      QuotientGroup.mk (rationalFrame frameTwo * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_fourth : (QuotientGroup.mk (weyl ^ 2) : Edges) =
      QuotientGroup.mk (rationalFrame frameTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_fifth : (QuotientGroup.mk (lineUnipotent 0 1 * (binaryA * (weyl * swapFirstTwo))) : Edges) =
      QuotientGroup.mk (rationalFrame frameTwo * weyl * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_sixth : (QuotientGroup.mk (binaryA * (weyl * swapFirstTwo)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl ^ 2) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_seventh : (QuotientGroup.mk (lineUnipotent 0 1 * (binaryA * (weyl ^ 2))) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree * weyl) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_eighth : (QuotientGroup.mk (binaryA * (weyl ^ 2)) : Edges) =
      QuotientGroup.mk (rationalFrame frameOne * weyl * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_ninth : (QuotientGroup.mk (rationalFrame frameOne) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree * weyl ^ 2 * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    simp only [pow_two, rationalFrame, ← map_inv]
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_tenth : (QuotientGroup.mk (rationalFrame frameOne * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree * weyl ^ 2) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    simp only [pow_two, rationalFrame, _root_.mul_inv_rev, ← map_inv]
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_eleventh : (QuotientGroup.mk (rationalFrame frameOne * weyl) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree * weyl * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    simp only [rationalFrame, _root_.mul_inv_rev, ← map_inv]
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_twelfth : (QuotientGroup.mk (rationalFrame frameTwo * weyl ^ 2) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree * swapFirstTwo) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    simp only [pow_two, rationalFrame, _root_.mul_inv_rev, ← map_inv]
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  have edge_thirteenth : (QuotientGroup.mk (rationalFrame frameTwo * weyl ^ 2 * swapFirstTwo) : Edges) =
      QuotientGroup.mk (rationalFrame frameThree) := by
    apply QuotientGroup.eq.mpr
    change InPlaneParabolic _ ∧ InLineParabolic _
    simp only [pow_two, rationalFrame, _root_.mul_inv_rev, ← map_inv]
    repeat' constructor <;>
      norm_num [pow_two, rationalFrame, frameOne, frameTwo, frameThree, weyl,
        swapFirstTwo, binaryA, upperUnipotent, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, GeneralLinearGroup.map_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  simp only [connector, map_sub, translateChain_single, apartment, quotient_smul]
  rw [edge_first, edge_second, edge_third, edge_fourth, edge_fifth, edge_sixth, edge_seventh, edge_eighth, edge_ninth, edge_tenth, edge_eleventh, edge_twelfth, edge_thirteenth]
  abel

end TernaryPeriodPolynomials.PolynomialBadLineNormalization.Frames
