module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.BadFaces
public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles
public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

noncomputable section
namespace TernaryPoly.AmbientZeroHeightCone
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open OrientedListChains OrientedChainJoin
abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- Replace the third column by the standard last-coordinate vector. -/
def planeMatrix (g : IntegralGL) : Mat :=
  fun i j => if j = 2 then if i = 2 then 1 else 0 else g.val i j

/-- The determinant of a basis whose first two columns have height zero factors by
the last entry of its complementary column. -/
theorem planeMatrix_det_mul (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0) :
    (planeMatrix g).det * g.val 2 2 = g.val.det := by
  simp [Matrix.det_fin_three,planeMatrix,h0,h1]
  ring

theorem planeMatrix_isUnit (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0) :
    IsUnit (planeMatrix g).det := by
  apply isUnit_of_mul_isUnit_left (y := g.val 2 2)
  rw [planeMatrix_det_mul g h0 h1]
  exact (Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit

def planeBasis (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0) : IntegralGL :=
  Matrix.nonsingInvUnit (planeMatrix g) (planeMatrix_isUnit g h0 h1)

theorem planeBasis_template (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0)
    (i : Fin 4) (hi : i ≠ 2) :
    rationalRepresentation (planeBasis g h0 h1) (template i) =
      rationalRepresentation g (template i) := by
  rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,
    ← rationalVector_mulVec,← rationalVector_mulVec]
  apply congrArg rationalVector
  change (planeMatrix g).mulVec (GoodAugmentedNormalForm.integralTemplate i) = _
  fin_cases i
  · funext r; simp [planeMatrix,GoodAugmentedNormalForm.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  · funext r; simp [planeMatrix,GoodAugmentedNormalForm.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  · exact (hi rfl).elim
  · funext r; simp [planeMatrix,GoodAugmentedNormalForm.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem planeBasis_line (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0)
    (i : Fin 4) (hi : i ≠ 2) :
    augmentedLine (planeBasis g h0 h1) i = augmentedLine g i := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (planeBasis g h0 h1) (template i)} = _
  rw [planeBasis_template g h0 h1 i hi]
  rfl

theorem planeBasis_line_two (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0) :
    augmentedLine (planeBasis g h0 h1) 2 = augmentedLine 1 2 := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (planeBasis g h0 h1) (template 2)} = _
  have hv : rationalRepresentation (planeBasis g h0 h1) (template 2) = template 2 := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
    apply congrArg rationalVector
    change (planeMatrix g).mulVec (GoodAugmentedNormalForm.integralTemplate 2) = _
    funext r
    fin_cases r <;> simp [planeMatrix,GoodAugmentedNormalForm.integralTemplate,Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  rw [hv]
  simp only [augmentedLine,vectorLine,map_one,LinearEquiv.coe_one,id_eq]

/-- Adjoining the standard height-one vertex to a zero-height augmented core is
literally an actual integral augmented tetrahedron. -/
theorem core_cone_ambient (g : IntegralGL) (h0 : g.val 2 0 = 0) (h1 : g.val 2 1 = 0) :
    {augmentedLine 1 2,augmentedLine g 0,augmentedLine g 1,augmentedLine g 3} ∈ ambient := by
  apply subset_augmentedFrame_mem (planeBasis g h0 h1) (by simp)
  have hmem (i : Fin 4) : augmentedLine (planeBasis g h0 h1) i ∈
      augmentedFrame (planeBasis g h0 h1) := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · rw [← planeBasis_line_two g h0 h1]; exact hmem 2
  · rw [← planeBasis_line g h0 h1 0 (by decide)]; exact hmem 0
  · rw [← planeBasis_line g h0 h1 1 (by decide)]; exact hmem 1
  · rw [← planeBasis_line g h0 h1 3 (by decide)]; exact hmem 3

/-- The literal rational coordinate plane at height zero. -/
def lastCoordinate : Space →ₗ[ℚ] ℚ where
  toFun v := v 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lastPlane : Submodule ℚ Space := LinearMap.ker lastCoordinate

def planeCoordinates : lastPlane →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun v := fun i => v.val i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem planeCoordinates_injective : Function.Injective planeCoordinates := by
  intro v w h
  apply Subtype.ext
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1
  · have hv : v.val 2 = 0 := v.property
    have hw : w.val 2 = 0 := w.property
    exact hv.trans hw.symm

theorem lastPlane_finrank_le : Module.finrank ℚ lastPlane ≤ 2 := by
  have h := LinearMap.finrank_le_finrank_of_injective planeCoordinates_injective
  simpa using h

/-- A zero-height line is literally contained in the rational coordinate plane. -/
def PlaneLine (L : RationalLine) : Prop := L.val ≤ lastPlane

theorem faceSpan_le_plane (s : Finset RationalLine) (hs : ∀ L ∈ s, PlaneLine L) :
    faceSpan s ≤ lastPlane := by
  exact Finset.sup_le hs

theorem faceSpan_finrank_le (s : Finset RationalLine) (hs : ∀ L ∈ s, PlaneLine L) :
    Module.finrank ℚ (faceSpan s) ≤ 2 :=
  (Submodule.finrank_mono (faceSpan_le_plane s hs)).trans lastPlane_finrank_le

theorem column_last_zero (g : IntegralGL) (i : Fin 3)
    (hi : PlaneLine (augmentedLine g i.castSucc)) : g.val 2 i = 0 := by
  have hm : rationalRepresentation g (template i.castSucc) ∈
      (augmentedLine g i.castSucc).val := Submodule.mem_span_singleton_self _
  have hz := hi hm
  change rationalRepresentation g (template i.castSucc) 2 = 0 at hz
  have ht : template i.castSucc = Pi.single i 1 := by fin_cases i <;> rfl
  rw [ht,rationalRepresentation_basis] at hz
  change (g.val 2 i : ℚ) = 0 at hz
  exact_mod_cast hz

/-- The actual full zero-coordinate-plane subcomplex of ambient augmented frames. -/
def zeroPlane : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ ambient ∧ ∀ L ∈ s, PlaneLine L}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(ambient.isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨(ambient.isRelLowerSet_faces hs.1).2 hts ht,fun L hL => hs.2 L (hts hL)⟩

/-- Every nondegenerate zero-plane triangle has an actual integral cone tetrahedron. -/
theorem triangle_cone_mem (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : l.toFinset ∈ zeroPlane) :
    cons (augmentedLine 1 2) (simplex l) ∈ chains ambient 4 := by
  have hface : l.toFinset ∈ ambient := hl.1
  have hplane : ∀ L ∈ l.toFinset, PlaneLine L := hl.2
  obtain ⟨g,hg⟩ := AmbientDependentTriangles.dependent_triangle_core l hlen hn hface
    (faceSpan_finrank_le l.toFinset hplane)
  have h0 : PlaneLine (augmentedLine g 0) := by
    apply hplane
    apply List.mem_toFinset.mpr
    exact hg.mem_iff.mpr (by simp)
  have h1 : PlaneLine (augmentedLine g 1) := by
    apply hplane
    apply List.mem_toFinset.mpr
    exact hg.mem_iff.mpr (by simp)
  have hf := core_cone_ambient g (column_last_zero g 0 h0) (column_last_zero g 1 h1)
  have hf' : Allowed ambient (augmentedLine 1 2 :: l) := by
    apply Or.inr
    convert hf using 1
    ext L
    simpa only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
      Finset.mem_insert,Finset.mem_singleton] using or_congr Iff.rfl (hg.mem_iff (a := L))
  rw [cons_simplex]
  have hm := simplex_mem_chains ambient (augmentedLine 1 2 :: l) hf'
  simpa only [List.length_cons,hlen] using hm

/-- The actual coordinate-plane cone sends every zero-plane two-chain into ambient tetrahedra. -/
theorem cone_mem {c : Chain RationalLine} (hc : c ∈ chains zeroPlane 3) :
    cons (augmentedLine 1 2) c ∈ chains ambient 4 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · apply triangle_cone_mem l hlen hn
      convert hl.resolve_left (fun he => by subst l; simp at hlen) using 1
      ext L
      simp only [List.mem_toFinset]
    · rw [simplex_eq_zero_of_not_nodup l hn,map_zero]
      exact (chains ambient 4).zero_mem
  | zero => simpa only [map_zero] using (chains ambient 4).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains ambient 4).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains ambient 4).smul_mem q ih

/-- Every actual zero-height two-cycle bounds its literal finite height-one cone. -/
theorem zero_plane_filling {c : Chain RationalLine} (hc : c ∈ chains zeroPlane 3)
    (hd : boundary c = 0) :
    ∃ t : Chain RationalLine, t ∈ chains ambient 4 ∧ boundary t = c := by
  refine ⟨cons (augmentedLine 1 2) c,cone_mem hc,?_⟩
  rw [boundary_cons_chain,hd,map_zero,sub_zero]

/-- The literal integral height functional corresponding to the rational coordinate plane. -/
def integralLastCoordinate : IntegralVector →ₗ[ℤ] ℤ where
  toFun v := v 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The coordinate-plane condition is exactly zero primitive height. -/
theorem height_zero_iff (L : RationalLine) :
    PrimitiveLineHeight.height integralLastCoordinate L = 0 ↔ PlaneLine L := by
  change (PrimitiveLineHeight.primitiveGenerator L 2).natAbs = 0 ↔ _
  rw [Int.natAbs_eq_zero]
  constructor
  · intro hz v hv
    rw [← PrimitiveLineHeight.primitiveGenerator_span L] at hv
    obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hv
    change q * (PrimitiveLineHeight.primitiveGenerator L 2 : ℚ) = 0
    rw [hz,Int.cast_zero,mul_zero]
  · intro hl
    have hm : rationalVector (PrimitiveLineHeight.primitiveGenerator L) ∈ L.val := by
      rw [← PrimitiveLineHeight.primitiveGenerator_span L]
      exact Submodule.mem_span_singleton_self _
    have hz := hl hm
    change (PrimitiveLineHeight.primitiveGenerator L 2 : ℚ) = 0 at hz
    exact_mod_cast hz

end TernaryPoly.AmbientZeroHeightCone
