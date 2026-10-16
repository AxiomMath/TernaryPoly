module

public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles
public import TernaryPeriodPolynomials.Building.BadEdge.NormalForm

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientHorizontalGeometry
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodIntegralNormalization GoodAugmentedNormalForm PrimitiveLineHeight
open AmbientDependentTriangles

/-- Negate only the second vector of an actual integral frame. -/
def flipSecondMatrix : Matrix (Fin 3) (Fin 3) ℤ := !![1,0,0;0,-1,0;0,0,1]

def flipSecond : IntegralGL :=
  ⟨flipSecondMatrix,flipSecondMatrix,by decide +kernel,by decide +kernel⟩

def differenceVector (g : IntegralGL) : IntegralVector := g.val.col 0 - g.val.col 1

def differenceLine (g : IntegralGL) : RationalLine := augmentedLine (g * flipSecond) 3

theorem flipSecond_line_zero (g : IntegralGL) : augmentedLine (g * flipSecond) 0 = augmentedLine g 0 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
  have he : flipSecond.val.mulVec (GoodAugmentedNormalForm.integralTemplate 0) =
      GoodAugmentedNormalForm.integralTemplate 0 := by decide +kernel
  rw [he,GoodAugmentedNormalForm.rationalVector_integralTemplate]

theorem flipSecond_line_two (g : IntegralGL) : augmentedLine (g * flipSecond) 2 = augmentedLine g 2 := by
  apply BadEdgeNormalForm.augmentedLine_mul_of_template
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
  have he : flipSecond.val.mulVec (GoodAugmentedNormalForm.integralTemplate 2) =
      GoodAugmentedNormalForm.integralTemplate 2 := by decide +kernel
  rw [he,GoodAugmentedNormalForm.rationalVector_integralTemplate]

theorem flipSecond_line_one (g : IntegralGL) : augmentedLine (g * flipSecond) 1 = augmentedLine g 1 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g*flipSecond) (template 1)} = _
  have he : rationalRepresentation flipSecond (template 1) = -template 1 := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
    decide +kernel
  rw [map_mul,LinearEquiv.mul_apply,he,map_neg,← neg_one_smul ℚ]
  rw [Submodule.span_singleton_smul_eq (show IsUnit (-1 : ℚ) by norm_num)]
  rfl

theorem differenceVector_eq_mulVec (g : IntegralGL) :
    differenceVector g = g.val.mulVec (![1,-1,0] : IntegralVector) := by
  funext i
  simp [differenceVector,Matrix.col,Matrix.mulVec,dotProduct,Fin.sum_univ_three,sub_eq_add_neg]

theorem differenceVector_primitive (g : IntegralGL) : Primitive (differenceVector g) := by
  rw [differenceVector_eq_mulVec]
  apply primitive_mulVec
  unfold Primitive content
  decide +kernel

theorem differenceLine_val (g : IntegralGL) :
    (differenceLine g).val = Submodule.span ℚ {rationalVector (differenceVector g)} := by
  change Submodule.span ℚ {rationalRepresentation (g*flipSecond) (template 3)} = _
  have he : rationalRepresentation flipSecond (template 3) =
      rationalVector (![1,-1,0] : IntegralVector) := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
    decide +kernel
  rw [map_mul,LinearEquiv.mul_apply,he,← rationalVector_mulVec,← differenceVector_eq_mulVec]

/-- The difference vertex of a horizontal edge has exactly height zero. -/
theorem difference_height_zero (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL)
    (hh : F (g.val.col 0) = F (g.val.col 1)) : height F (differenceLine g) = 0 := by
  rw [height_eq_natAbs F (differenceLine g) (differenceVector_primitive g) (differenceLine_val g).symm]
  simp only [differenceVector,map_sub,hh,sub_self,Int.natAbs_zero]

/-- The common replacement vertex depends only on the two literal endpoint vectors. -/
theorem differenceLine_eq_of_columns (g h : IntegralGL)
    (h0 : g.val.col 0 = h.val.col 0) (h1 : g.val.col 1 = h.val.col 1) :
    differenceLine g = differenceLine h := by
  apply Subtype.ext
  rw [differenceLine_val,differenceLine_val,differenceVector,differenceVector,h0,h1]

/-- The horizontal-edge subdivision is an actual augmented tetrahedron. -/
theorem horizontal_tetrahedron (g : IntegralGL) :
    {differenceLine g,augmentedLine g 0,augmentedLine g 1,augmentedLine g 2} ∈ ambient := by
  apply subset_augmentedFrame_mem (g*flipSecond) (by simp)
  have hm (i : Fin 4) : augmentedLine (g*flipSecond) i ∈ augmentedFrame (g*flipSecond) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact hm 3
  · rw [← flipSecond_line_zero]; exact hm 0
  · rw [← flipSecond_line_one]; exact hm 1
  · rw [← flipSecond_line_two]; exact hm 2

/-- Both replacement triangles are actual independent integral triples. -/
theorem horizontal_replacement_bases (g : IntegralGL) :
    (∃ h : IntegralGL, augmentedLine h 0 = differenceLine g ∧
      augmentedLine h 1 = augmentedLine g 0 ∧ augmentedLine h 2 = augmentedLine g 2) ∧
    (∃ h : IntegralGL, augmentedLine h 0 = differenceLine g ∧
      augmentedLine h 1 = augmentedLine g 1 ∧ augmentedLine h 2 = augmentedLine g 2) := by
  constructor
  · obtain ⟨h,h0,h1,h2⟩ := core_pair_complement_basis (g*flipSecond) 2 0 (by decide)
    exact ⟨h,h0,h1.trans (flipSecond_line_zero g),h2.trans (flipSecond_line_two g)⟩
  · obtain ⟨h,h0,h1,h2⟩ := core_pair_complement_basis (g*flipSecond) 2 1 (by decide)
    exact ⟨h,h0,h1.trans (flipSecond_line_one g),h2.trans (flipSecond_line_two g)⟩

end TernaryPoly.AmbientHorizontalGeometry
