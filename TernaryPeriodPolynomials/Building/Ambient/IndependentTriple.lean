module

public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Topology.Rational.LineBasis
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

@[expose] public section


open scoped BigOperators
noncomputable section
namespace TernaryPoly.AmbientIndependentTriple
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces

abbrev IntegralMatrix := Matrix (Fin 3) (Fin 3) ℤ

/-- Select any ordered triple of columns from the literal four-vector augmented template. -/
def templateMatrix (idx : Fin 3 → Fin 4) : IntegralMatrix :=
  fun i j => integralTemplate (idx j) i

/-- Exhaustive determinant calculation on all 64 ordered template triples. -/
theorem templateMatrix_det_zero_or_unit (idx : Fin 3 → Fin 4) :
    (templateMatrix idx).det = 0 ∨ (templateMatrix idx).det.natAbs = 1 := by
  have h : ∀ a b c : Fin 4,
      (templateMatrix ![a,b,c]).det = 0 ∨ (templateMatrix ![a,b,c]).det.natAbs = 1 := by
    decide +kernel
  have he : (![idx 0,idx 1,idx 2] : Fin 3 → Fin 4) = idx := by
    ext j
    fin_cases j <;> rfl
  simpa only [he] using h (idx 0) (idx 1) (idx 2)

/-- A primitive vector on one of the actual augmented lines is its template generator up to a unit. -/
theorem primitive_eq_unit_template (g : IntegralGL) (i : Fin 4)
    {v : IntegralVector} (hv : Primitive v)
    (hspan : Submodule.span ℚ {rationalVector v} = (augmentedLine g i).val) :
    ∃ u : ℤˣ, v = (u : ℤ) • g.val.mulVec (integralTemplate i) := by
  have hs : Submodule.span ℚ {rationalVector v} =
      Submodule.span ℚ {rationalVector (g.val.mulVec (integralTemplate i))} := by
    rw [rationalVector_mulVec,rationalVector_integralTemplate]
    exact hspan
  rcases primitive_eq_or_neg_of_span_eq hv
      (primitive_mulVec g (integralTemplate_primitive i)) hs with h | h
  · exact ⟨1,by simpa using h⟩
  · exact ⟨-1,by simpa using h⟩

/-- Primitive columns on an actual ambient triple admit the exact matrix factorization by signs. -/
theorem matrix_factorization_of_ambient (M : IntegralMatrix)
    (hprim : ∀ j, Primitive (M.col j)) (L : Fin 3 → RationalLine)
    (hL : ∀ j, Submodule.span ℚ {rationalVector (M.col j)} = (L j).val)
    (hface : Finset.univ.image L ∈ ambient) :
    ∃ (g : IntegralGL) (idx : Fin 3 → Fin 4) (u : Fin 3 → ℤˣ),
      M = g.val * templateMatrix idx * Matrix.diagonal (fun j => (u j : ℤ)) := by
  classical
  obtain ⟨_,g,hg⟩ := hface
  have hi (j : Fin 3) : ∃ i : Fin 4, augmentedLine g i = L j := by
    have hm := hg (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    exact ⟨i,hi⟩
  choose idx hidx using hi
  have hu (j : Fin 3) : ∃ u : ℤˣ,
      M.col j = (u : ℤ) • g.val.mulVec (integralTemplate (idx j)) := by
    apply primitive_eq_unit_template g (idx j) (hprim j)
    rw [hL,hidx]
  choose u hu using hu
  refine ⟨g,idx,u,?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have h := congrFun (hu j) i
  change M i j = (u j : ℤ) * (g.val.mulVec (integralTemplate (idx j))) i at h
  rw [h,mul_comm]
  rfl

/-- An independent ambient triple with primitive integer columns is an actual unimodular basis. -/
theorem det_natAbs_eq_one_of_ambient (M : IntegralMatrix)
    (hprim : ∀ j, Primitive (M.col j)) (hdet : M.det ≠ 0)
    (L : Fin 3 → RationalLine)
    (hL : ∀ j, Submodule.span ℚ {rationalVector (M.col j)} = (L j).val)
    (hface : Finset.univ.image L ∈ ambient) : M.det.natAbs = 1 := by
  obtain ⟨g,idx,u,he⟩ := matrix_factorization_of_ambient M hprim L hL hface
  have ht : (templateMatrix idx).det.natAbs = 1 := by
    rcases templateMatrix_det_zero_or_unit idx with hz | hu
    · exfalso
      apply hdet
      rw [he,Matrix.det_mul,Matrix.det_mul,hz,mul_zero,zero_mul]
    · exact hu
  apply Int.isUnit_iff_natAbs_eq.mp
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
  exact ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit).mul
    (Int.isUnit_iff_natAbs_eq.mpr ht) |>.mul
      (by simpa only [Fin.prod_univ_three] using
        ((u 0).isUnit.mul (u 1).isUnit).mul (u 2).isUnit)

/-- The unimodularity theorem produces a genuine integer matrix unit with exactly the given columns. -/
theorem exists_integralGL_eq_of_ambient (M : IntegralMatrix)
    (hprim : ∀ j, Primitive (M.col j)) (hdet : M.det ≠ 0)
    (L : Fin 3 → RationalLine)
    (hL : ∀ j, Submodule.span ℚ {rationalVector (M.col j)} = (L j).val)
    (hface : Finset.univ.image L ∈ ambient) : ∃ g : IntegralGL, g.val = M := by
  exact ⟨Matrix.nonsingInvUnit M (Int.isUnit_iff_natAbs_eq.mpr
    (det_natAbs_eq_one_of_ambient M hprim hdet L hL hface)),rfl⟩

/-- Primitive integer vectors have nonzero rational images, independently of goodness. -/
theorem rationalVector_ne_zero_of_primitive {v : IntegralVector} (hv : Primitive v) :
    rationalVector v ≠ 0 := by
  intro hz
  have hvz : v = 0 := by
    ext i
    have hi : (v i : ℚ) = 0 := congrFun hz i
    exact_mod_cast hi
  obtain ⟨b,hb⟩ := primitive_bezout hv
  simp [hvz] at hb

/-- The actual rational column lines of any primitive-column integral matrix. -/
def primitiveColumnLine (M : IntegralMatrix) (hprim : ∀ j, Primitive (M.col j))
    (j : Fin 3) : RationalLine :=
  vectorLine (rationalVector (M.col j)) (rationalVector_ne_zero_of_primitive (hprim j))

/-- Matrix-only version of the complete independent-triple classification. -/
theorem det_natAbs_eq_one_of_column_face (M : IntegralMatrix)
    (hprim : ∀ j, Primitive (M.col j)) (hdet : M.det ≠ 0)
    (hface : Finset.univ.image (primitiveColumnLine M hprim) ∈ ambient) :
    M.det.natAbs = 1 :=
  det_natAbs_eq_one_of_ambient M hprim hdet (primitiveColumnLine M hprim)
    (fun _ => rfl) hface

/-- For independent primitive columns, the ambient-face condition is exactly unimodularity. -/
theorem column_face_iff_det_natAbs_eq_one (M : IntegralMatrix)
    (hprim : ∀ j, Primitive (M.col j)) (hdet : M.det ≠ 0) :
    Finset.univ.image (primitiveColumnLine M hprim) ∈ ambient ↔ M.det.natAbs = 1 := by
  classical
  constructor
  · exact det_natAbs_eq_one_of_column_face M hprim hdet
  · intro hd
    let g : IntegralGL := Matrix.nonsingInvUnit M (Int.isUnit_iff_natAbs_eq.mpr hd)
    apply subset_augmentedFrame_mem g (Finset.image_nonempty.mpr Finset.univ_nonempty)
    intro L hL
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hL
    refine Finset.mem_image.mpr ⟨j.castSucc,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    rw [augmentedLine_castSucc_val,rationalRepresentation_basis]
    rfl

/-- The span of an ordered family of column generators is exactly the span of its line face. -/
theorem column_span_eq_faceSpan (M : IntegralMatrix) (L : Fin 3 → RationalLine)
    (hL : ∀ j, Submodule.span ℚ {rationalVector (M.col j)} = (L j).val) :
    Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).col) =
      faceSpan (Finset.univ.image L) := by
  classical
  rw [Submodule.span_range_eq_iSup]
  unfold faceSpan
  rw [Finset.sup_image]
  simp only [Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]
  exact iSup_congr hL

/-- Full rational span makes an ordered ambient triple the column lines of an actual integer basis. -/
theorem exists_integralGL_of_finrank_eq_three (L : Fin 3 → RationalLine)
    (hface : Finset.univ.image L ∈ ambient)
    (hdim : Module.finrank ℚ (faceSpan (Finset.univ.image L)) = 3) :
    ∃ g : IntegralGL, ∀ j : Fin 3, augmentedLine g j.castSucc = L j := by
  classical
  choose v hp hn hs using fun j => RationalLineBasis.rationalLine_primitive_generator (L j)
  let M : IntegralMatrix := fun i j => v j i
  have hprim (j : Fin 3) : Primitive (M.col j) := hp j
  have hL (j : Fin 3) : Submodule.span ℚ {rationalVector (M.col j)} = (L j).val := hs j
  have hind : LinearIndependent ℚ (M.map (Int.castRingHom ℚ)).col := by
    apply linearIndependent_iff_card_le_finrank_span.mpr
    change 3 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (M.map (Int.castRingHom ℚ)).col))
    rw [column_span_eq_faceSpan M L hL,hdim]
  have hdet : M.det ≠ 0 := by
    have hd := Matrix.linearIndependent_cols_iff_isUnit.mp hind
    have hdq : (M.map (Int.castRingHom ℚ)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp hd).ne_zero
    have he : (M.map (Int.castRingHom ℚ)).det = (M.det : ℚ) :=
      ((Int.castRingHom ℚ).map_det M).symm
    rw [he] at hdq
    exact fun hz => hdq (by rw [hz,Int.cast_zero])
  obtain ⟨g,hg⟩ := exists_integralGL_eq_of_ambient M hprim hdet L hL hface
  refine ⟨g,fun j => ?_⟩
  apply Subtype.ext
  rw [augmentedLine_castSucc_val,rationalRepresentation_basis,hg]
  exact hL j

end TernaryPoly.AmbientIndependentTriple
