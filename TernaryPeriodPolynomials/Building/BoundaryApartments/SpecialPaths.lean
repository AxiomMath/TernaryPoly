module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.LineDecomposition

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

def otherEdgeFrame : RationalGL3 := Adelic.weyl * swapFirstTwo

def otherEdge : Edges := QuotientGroup.mk otherEdgeFrame

def otherBase : BuildingVertices := Sum.inl (endpoint .plane otherEdge)

def connectingChain : EdgeChains := Finsupp.single otherEdge 1 - Finsupp.single baseEdge 1

theorem otherEdgeFrame_entries :
    otherEdgeFrame.val = !![0,0,1;0,1,0;1,0,0] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [otherEdgeFrame, Adelic.weyl, swapFirstTwo, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem otherEdge_line : endpoint .line otherEdge = endpoint .line baseEdge := by
  apply (line_flag_eq_of_column 1 _).symm
  intro index
  change otherEdgeFrame.val index 0 = 1 * baseEdgeFrame.val index 0
  rw [otherEdgeFrame_entries, baseEdgeFrame_entries, one_mul]
  fin_cases index <;> rfl

theorem otherEdge_plane_good : GoodFlag .plane (endpoint .plane otherEdge) := by
  apply plane_good_of_firstColumn otherEdgeFrame
  intro index
  rw [otherEdgeFrame_entries]
  fin_cases index <;> rfl

theorem connectingChain_good : GoodChain connectingChain := by
  apply goodChain_sub _ baseEdge_good
  apply goodChain_single otherEdge_plane_good
  rw [otherEdge_line]
  exact baseEdge_line_good

theorem connectingChain_boundary : chainBoundary connectingChain =
    Finsupp.single otherBase 1 - Finsupp.single pathBase 1 := by
  simp only [connectingChain, map_sub, chainBoundary_single, otherEdge_line, baseEdge_plane]
  change _ = Finsupp.single (Sum.inl (endpoint .plane otherEdge)) 1 -
    Finsupp.single (Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)) 1
  abel

theorem blockLevi_fixes_otherBase (matrix : RationalGL3)
    (first_row : matrix.val 0 1 = 0 ∧ matrix.val 0 2 = 0) :
    translateVertex matrix otherBase = otherBase := by
  change Sum.inl (matrix • (QuotientGroup.mk otherEdgeFrame : Flags .plane)) =
    Sum.inl (QuotientGroup.mk otherEdgeFrame : Flags .plane)
  congr 1
  change (QuotientGroup.mk (matrix * otherEdgeFrame) : Flags .plane) =
    QuotientGroup.mk otherEdgeFrame
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 2 0 = 0 ∧
    (otherEdgeFrame⁻¹ * (matrix * otherEdgeFrame)).val 2 1 = 0
  constructor <;>
    simp [otherEdgeFrame, _root_.mul_inv_rev, Adelic.weyl, swapFirstTwo,
      Matrix.mul_apply, Fin.sum_univ_three, first_row.1, first_row.2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]

theorem radical_fixes_pathBase (first second : ℚ) :
    translateVertex (Adelic.lineUnipotent first second) pathBase = pathBase := by
  change Sum.inl (Adelic.lineUnipotent first second •
    (QuotientGroup.mk swapLastTwo : Flags .plane)) =
      Sum.inl (QuotientGroup.mk swapLastTwo : Flags .plane)
  congr 1
  change (QuotientGroup.mk (Adelic.lineUnipotent first second * swapLastTwo) : Flags .plane) = _
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (swapLastTwo⁻¹ * (Adelic.lineUnipotent first second * swapLastTwo)).val 2 0 = 0 ∧
    (swapLastTwo⁻¹ * (Adelic.lineUnipotent first second * swapLastTwo)).val 2 1 = 0
  constructor <;>
    simp [swapLastTwo, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

def specialLinePath (matrix : badLineSubgroup) : EdgeChains :=
  translateChain (arithmeticRadical matrix).val
    (connectingChain - translateChain (arithmeticLevi matrix).val connectingChain)

theorem specialLinePath_good (matrix : badLineSubgroup) : GoodChain (specialLinePath matrix) := by
  exact goodChain_translate (arithmeticRadical matrix)
    (goodChain_sub connectingChain_good
      (goodChain_translate (arithmeticLevi matrix) connectingChain_good))

theorem translateVertex_comp (first second : RationalGL3) (vertex : BuildingVertices) :
    translateVertex first (translateVertex second vertex) =
      translateVertex (first * second) vertex := by
  cases vertex <;> simp only [translateVertex, mul_smul]

theorem arithmeticLevi_fixes_otherBase (matrix : badLineSubgroup) :
    translateVertex (arithmeticLevi matrix).val otherBase = otherBase :=
  blockLevi_fixes_otherBase _ ⟨rfl,rfl⟩

theorem arithmeticRadical_fixes_pathBase (matrix : badLineSubgroup) :
    translateVertex (arithmeticRadical matrix).val pathBase = pathBase := by
  rw [arithmeticRadical_val, lineRadical_upper]
  exact radical_fixes_pathBase _ _

theorem specialLinePath_boundary (matrix : badLineSubgroup) :
    chainBoundary (specialLinePath matrix) =
      Finsupp.single (translateVertex matrix.val pathBase) 1 - Finsupp.single pathBase 1 := by
  simp only [specialLinePath, chainBoundary_translate, map_sub, connectingChain_boundary,
    translateVertexChain, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, arithmeticLevi_fixes_otherBase,
    arithmeticRadical_fixes_pathBase, translateVertex_comp]
  have product_eq := congrArg Subtype.val (arithmeticRadical_mul_levi matrix)
  simp only [Subgroup.coe_mul] at product_eq
  rw [product_eq]
  abel

def specialPaths (matrix : rationalLevel) : EdgeChains := by
  classical
  exact if matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ then
    specialLinePath ⟨matrix.val, matrix.property, matrix_line⟩
  else goodPaths matrix

theorem specialPaths_isPathFamily : IsPathFamily specialPaths := by
  classical
  intro matrix
  by_cases matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ
  · rw [specialPaths, dite_eq_left matrix_line]
    exact ⟨specialLinePath_good _, specialLinePath_boundary _⟩
  · rw [specialPaths, dite_eq_right matrix_line]
    exact goodPaths_isPathFamily matrix

theorem specialPaths_on_line (matrix : rationalLevel)
    (matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ) :
    specialPaths matrix = specialLinePath ⟨matrix.val, matrix.property, matrix_line⟩ := by
  classical
  rw [specialPaths, dite_eq_left matrix_line]

theorem lineLevi_upper (first second : ℚ) :
    lineLevi ⟨Adelic.lineUnipotent first second, ⟨rfl,rfl⟩⟩ = 1 := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;> rfl

theorem specialPaths_radical (matrix : rationalLevel) (first second : ℚ)
    (matrix_eq : matrix.val = Adelic.lineUnipotent first second) : specialPaths matrix = 0 := by
  have matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ := by
    rw [matrix_eq]
    exact ⟨rfl,rfl⟩
  rw [specialPaths_on_line matrix matrix_line]
  have levi_eq : (arithmeticLevi (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val = 1 := by
    change lineLevi ⟨matrix.val, matrix_line⟩ = 1
    simpa only [matrix_eq] using lineLevi_upper first second
  simp [specialLinePath, levi_eq, translateChain_one]

theorem lineLevi_block (matrix : RationalGL3)
    (matrix_line : matrix ∈ Adelic.lineParabolic ℚ)
    (matrix_block : matrix.val 0 1 = 0 ∧ matrix.val 0 2 = 0) :
    lineLevi ⟨matrix, matrix_line⟩ = matrix := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [lineLevi, lineBlock, matrix_line.1, matrix_line.2,
      matrix_block.1, matrix_block.2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem specialPaths_levi (matrix : rationalLevel)
    (matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ)
    (matrix_block : matrix.val.val 0 1 = 0 ∧ matrix.val.val 0 2 = 0) :
    specialPaths matrix = connectingChain - translateChain matrix.val connectingChain := by
  rw [specialPaths_on_line matrix matrix_line]
  have levi_eq : (arithmeticLevi (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val = matrix.val :=
    lineLevi_block _ matrix_line matrix_block
  have radical_eq : (arithmeticRadical (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val = 1 := by
    change matrix.val * (arithmeticLevi (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val⁻¹ = 1
    rw [levi_eq, mul_inv_cancel]
  rw [specialLinePath, radical_eq, levi_eq, translateChain_one]

theorem lineLevi_upper_mul (first second : ℚ) (matrix : RationalGL3)
    (matrix_line : matrix ∈ Adelic.lineParabolic ℚ) :
    lineLevi ⟨Adelic.lineUnipotent first second * matrix,
      Adelic.inLine_mul ⟨rfl,rfl⟩ matrix_line⟩ = lineLevi ⟨matrix,matrix_line⟩ := by
  have product_eq := lineLevi_mul
    (⟨Adelic.lineUnipotent first second, ⟨rfl,rfl⟩⟩ : Adelic.lineParabolic ℚ)
    ⟨matrix, matrix_line⟩
  change lineLevi ⟨Adelic.lineUnipotent first second * matrix,
    Adelic.inLine_mul ⟨rfl,rfl⟩ matrix_line⟩ = _ at product_eq
  simpa only [lineLevi_upper, one_mul] using product_eq

theorem specialPaths_radical_mul (radical matrix : rationalLevel) (first second : ℚ)
    (radical_eq : radical.val = Adelic.lineUnipotent first second)
    (matrix_line : matrix.val ∈ Adelic.lineParabolic ℚ) :
    specialPaths (radical * matrix) = translateChain radical.val (specialPaths matrix) := by
  have radical_line : radical.val ∈ Adelic.lineParabolic ℚ := by
    rw [radical_eq]
    exact ⟨rfl,rfl⟩
  have product_line : (radical * matrix).val ∈ Adelic.lineParabolic ℚ :=
    Adelic.inLine_mul radical_line matrix_line
  rw [specialPaths_on_line _ product_line, specialPaths_on_line _ matrix_line]
  have levi_eq :
      (arithmeticLevi (⟨(radical * matrix).val, (radical * matrix).property, product_line⟩ : badLineSubgroup)).val =
        (arithmeticLevi (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val := by
    change lineLevi ⟨radical.val * matrix.val, product_line⟩ = lineLevi ⟨matrix.val, matrix_line⟩
    simpa only [radical_eq] using lineLevi_upper_mul first second matrix.val matrix_line
  have radical_product :
      (arithmeticRadical (⟨(radical * matrix).val, (radical * matrix).property, product_line⟩ : badLineSubgroup)).val =
        radical.val * (arithmeticRadical (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val := by
    change (radical.val * matrix.val) *
      (arithmeticLevi (⟨(radical * matrix).val, (radical * matrix).property, product_line⟩ : badLineSubgroup)).val⁻¹ =
      radical.val * (matrix.val *
        (arithmeticLevi (⟨matrix.val, matrix.property, matrix_line⟩ : badLineSubgroup)).val⁻¹)
    rw [levi_eq, mul_assoc]
  simp only [specialLinePath, radical_product, levi_eq, translateChain_mul]

theorem integral_radical_arithmetic (first second : ℤ) :
    Adelic.lineUnipotent first second ∈ arithmeticLevel := by
  change lastRow ᵥ* (reductionThree (Adelic.lineUnipotent first second)).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index <;> rfl

def integralImage (matrix : IntegralGL3) (matrix_arithmetic : matrix ∈ arithmeticLevel) :
    rationalLevel :=
  ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) matrix, ⟨⟨matrix, matrix_arithmetic⟩, rfl⟩⟩

def integralRadical (first second : ℤ) : rationalLevel :=
  integralImage (Adelic.lineUnipotent first second) (integral_radical_arithmetic first second)

theorem integralRadical_val (first second : ℤ) :
    (integralRadical first second).val = Adelic.lineUnipotent (first : ℚ) (second : ℚ) := by
  apply GeneralLinearGroup.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [integralRadical, integralImage, GeneralLinearGroup.map_apply,
      Adelic.lineUnipotent, Adelic.upperUnipotent, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem integralRadical_mul (first second third fourth : ℤ) :
    integralRadical first second * integralRadical third fourth =
      integralRadical (first + third) (second + fourth) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, integralRadical_val, Int.cast_add, Adelic.lineUnipotent_add]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
