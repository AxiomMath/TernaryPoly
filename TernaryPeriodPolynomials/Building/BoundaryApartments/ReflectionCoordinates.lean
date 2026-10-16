module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.PureMixed
public import TernaryPeriodPolynomials.Building.BoundaryApartments.ZeroBridge

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix Homogeneous

def integralBinaryB : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,-3,1], !![1,0,0;0,-1,0;0,-3,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralBinaryR : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,0,1], !![1,0,0;0,-1,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem integralBinaryB_levi : BadLineLevi integralBinaryB := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  change lastRow ᵥ* (reductionThree integralBinaryB).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index
  · rfl
  · change (-3 : ZMod 3) = 0
    decide
  · rfl

theorem integralBinaryR_levi : BadLineLevi integralBinaryR := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  change lastRow ᵥ* (reductionThree integralBinaryR).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index <;> rfl

def arithmeticBinaryB : rationalLevel := integralImage integralBinaryB integralBinaryB_levi.1

def arithmeticBinaryR : rationalLevel := integralImage integralBinaryR integralBinaryR_levi.1

theorem arithmeticBinaryB_val : arithmeticBinaryB.val = binaryB := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [arithmeticBinaryB, integralImage, integralBinaryB, binaryB,
      GeneralLinearGroup.map_apply]

theorem arithmeticBinaryR_val : arithmeticBinaryR.val = binaryR := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    norm_num [arithmeticBinaryR, integralImage, integralBinaryR, binaryR,
      GeneralLinearGroup.map_apply]

theorem fixes_edge_of_firstColumn {matrix : RationalGL3}
    (fixed_column : ∀ index, matrix.val index 2 = (1 : Matrix (Fin 3) (Fin 3) ℚ) index 2)
    (preserves_firstPlane : matrix.val 1 0 = 0)
    (preserves_secondPlane : matrix.val 0 1 = 0) :
    translateChain matrix connectingChain = connectingChain := by
  have fixes_other : matrix • otherEdge = otherEdge := by
    change (QuotientGroup.mk (matrix * otherEdgeFrame) : Edges) = QuotientGroup.mk otherEdgeFrame
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    change ((otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 2 0 = 0 ∧
      (otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 2 1 = 0) ∧
      (otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 1 0 = 0 ∧
      (otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 2 0 = 0
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp [otherEdgeFrame, _root_.mul_inv_rev, Adelic.weyl, swapFirstTwo,
        Matrix.mul_apply, Fin.sum_univ_three, fixed_column,
        preserves_secondPlane,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
  have fixes_base : matrix • baseEdge = baseEdge := by
    change (QuotientGroup.mk (matrix * baseEdgeFrame) : Edges) = QuotientGroup.mk baseEdgeFrame
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    change ((baseEdgeFrame⁻¹ * (matrix * baseEdgeFrame)).val 2 0 = 0 ∧
      (baseEdgeFrame⁻¹ * (matrix * baseEdgeFrame)).val 2 1 = 0) ∧
      (baseEdgeFrame⁻¹ * (matrix * baseEdgeFrame)).val 1 0 = 0 ∧
      (baseEdgeFrame⁻¹ * (matrix * baseEdgeFrame)).val 2 0 = 0
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
      simp [baseEdgeFrame, Adelic.weyl, pow_two,
        Matrix.mul_apply, Fin.sum_univ_three, fixed_column,
        preserves_firstPlane,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail]
  simp only [connectingChain, map_sub, translateChain, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, fixes_other, fixes_base]

theorem binaryB_fixes_connectingChain : translateChain binaryB connectingChain = connectingChain := by
  apply fixes_edge_of_firstColumn
  · intro index
    fin_cases index <;> rfl
  · rfl
  · rfl

theorem binaryR_fixes_connectingChain : translateChain binaryR connectingChain = connectingChain := by
  apply fixes_edge_of_firstColumn
  · intro index
    fin_cases index <;> rfl
  · rfl
  · rfl

theorem specialPaths_binaryB : specialPaths arithmeticBinaryB = 0 := by
  unfold arithmeticBinaryB
  rw [specialPaths_integralLevi integralBinaryB integralBinaryB_levi]
  change connectingChain - translateChain arithmeticBinaryB.val connectingChain = 0
  rw [arithmeticBinaryB_val, binaryB_fixes_connectingChain, sub_self]

theorem specialPaths_binaryR : specialPaths arithmeticBinaryR = 0 := by
  unfold arithmeticBinaryR
  rw [specialPaths_integralLevi integralBinaryR integralBinaryR_levi]
  change connectingChain - translateChain arithmeticBinaryR.val connectingChain = 0
  rw [arithmeticBinaryR_val, binaryR_fixes_connectingChain, sub_self]

theorem integralRadical_conjugate_coordinates (levi : rationalLevel) (first second : ℤ)
    (levi_line : levi.val ∈ Adelic.lineParabolic ℚ) :
    ∃ left right : ℚ, (levi⁻¹ * integralRadical first second * levi).val =
      Adelic.lineUnipotent left right := by
  have conjugate_line : (levi⁻¹ * integralRadical first second * levi).val ∈
      Adelic.lineParabolic ℚ := by
    exact Adelic.inLine_mul
      (Adelic.inLine_mul (Adelic.inLine_inv levi_line) (by
        rw [integralRadical_val]
        exact ⟨rfl, rfl⟩)) levi_line
  have levi_eq := lineLevi_upper_mul (first : ℚ) (second : ℚ) levi.val levi_line
  have conjugate_levi : lineLevi ⟨(levi⁻¹ * integralRadical first second * levi).val,
      conjugate_line⟩ = 1 := by
    have product := lineLevi_mul
      (⟨levi.val⁻¹, Adelic.inLine_inv levi_line⟩ : Adelic.lineParabolic ℚ)
      ⟨(integralRadical first second).val * levi.val,
        Adelic.inLine_mul (by rw [integralRadical_val]; exact ⟨rfl,rfl⟩) levi_line⟩
    change lineLevi ⟨levi.val⁻¹ * ((integralRadical first second).val * levi.val), _⟩ =
      lineLevi ⟨levi.val⁻¹, _⟩ * lineLevi ⟨(integralRadical first second).val * levi.val, _⟩
      at product
    have inverse_eq : lineLevi ⟨levi.val⁻¹, Adelic.inLine_inv levi_line⟩ =
        (lineLevi ⟨levi.val, levi_line⟩)⁻¹ :=
      lineLevi_inv (⟨levi.val, levi_line⟩ : Adelic.lineParabolic ℚ)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, integralRadical_val,
      levi_eq, inverse_eq, inv_mul_cancel, mul_assoc] using product
  have radical := lineRadical_upper
    (⟨(levi⁻¹ * integralRadical first second * levi).val, conjugate_line⟩ :
      Adelic.lineParabolic ℚ)
  refine ⟨(lineRadical ⟨(levi⁻¹ * integralRadical first second * levi).val,
    conjugate_line⟩).val 0 1, (lineRadical ⟨(levi⁻¹ * integralRadical first second * levi).val,
    conjugate_line⟩).val 0 2, ?_⟩
  simpa only [lineRadical, conjugate_levi, inv_one, mul_one] using radical

theorem mixedBarEdge_zero_of_fixedLevi {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle)
    (levi : rationalLevel) (first second : ℤ)
    (levi_line : levi.val ∈ Adelic.lineParabolic ℚ)
    (levi_path : specialPaths levi = 0) :
    mixedBarEdge cocycle levi.val (Adelic.lineUnipotent (first : ℚ) (second : ℚ)) = 0 := by
  obtain ⟨left, right, conjugate_eq⟩ := integralRadical_conjugate_coordinates levi first second levi_line
  simpa only [integralRadical_val] using mixedBarEdge_zero_of_specialPaths realizes
    levi (integralRadical first second)
    (specialPaths_radical _ _ _ (integralRadical_val _ _))
    (specialPaths_radical _ _ _ conjugate_eq)
    (specialPaths_radical_mul _ _ _ _ (integralRadical_val _ _) levi_line) levi_path

theorem mixedBernoulliCoordinate_binaryB {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle binaryB = 0 := by
  have first := mixedBarEdge_zero_of_fixedLevi realizes arithmeticBinaryB 1 0
    (by rw [arithmeticBinaryB_val]; exact ⟨rfl,rfl⟩) specialPaths_binaryB
  have second := mixedBarEdge_zero_of_fixedLevi realizes arithmeticBinaryB 0 1
    (by rw [arithmeticBinaryB_val]; exact ⟨rfl,rfl⟩) specialPaths_binaryB
  simp only [arithmeticBinaryB_val, Int.cast_one, Int.cast_zero] at first second
  simp [mixedBernoulliCoordinate, first, second, bernoulliOperator_zero]

theorem mixedBernoulliCoordinate_binaryR {degree : ℕ}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
    (realizes : RealizesPathClass functional specialPaths cocycle) :
    mixedBernoulliCoordinate cocycle binaryR = 0 := by
  have first := mixedBarEdge_zero_of_fixedLevi realizes arithmeticBinaryR 1 0
    (by rw [arithmeticBinaryR_val]; exact ⟨rfl,rfl⟩) specialPaths_binaryR
  have second := mixedBarEdge_zero_of_fixedLevi realizes arithmeticBinaryR 0 1
    (by rw [arithmeticBinaryR_val]; exact ⟨rfl,rfl⟩) specialPaths_binaryR
  simp only [arithmeticBinaryR_val, Int.cast_one, Int.cast_zero] at first second
  simp [mixedBernoulliCoordinate, first, second, bernoulliOperator_zero]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
