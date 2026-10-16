module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.FrameComplex
public import TernaryPeriodPolynomials.Building.Good.AugmentedNormalForm
public import TernaryPeriodPolynomials.Building.Primitive.LineHeight
public import TernaryPeriodPolynomials.Building.AugmentedFrame.HeightArithmetic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


noncomputable section
namespace TernaryPoly.AugmentedCarryingGeometry
open ModThreeGoodAction GoodIntegralNormalization GoodAugmentedNormalForm
open AugmentedFrameComplex PrimitiveLineHeight OrientedListChains

abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

/-- Coordinates of w,b,c,a=b+c-w,t=b-w in an actual integral basis. -/
def carryVector : Fin 5 → IntegralVector :=
  ![![1,0,0],![0,1,0],![0,0,1],![-1,1,1],![-1,1,0]]

private theorem carryVector_primitive : ∀ i, Primitive (carryVector i) := by
  unfold Primitive content
  decide +kernel

theorem carryVector_ne_zero : ∀ i, rationalVector (carryVector i) ≠ 0 := by
  decide +kernel

/-- The five primitive integral vectors in the chosen actual basis. -/
def actualVector (g : IntegralGL) (i : Fin 5) : IntegralVector := g.val.mulVec (carryVector i)

theorem actualVector_primitive (g : IntegralGL) (i : Fin 5) : Primitive (actualVector g i) :=
  primitive_mulVec g (carryVector_primitive i)

/-- Their actual rational-line vertices. -/
def carryLine (g : IntegralGL) (i : Fin 5) : RationalLine :=
  vectorLine (rationalRepresentation g (rationalVector (carryVector i)))
    (fun h => carryVector_ne_zero i ((rationalRepresentation g).injective
      (h.trans (map_zero (rationalRepresentation g)).symm)))

abbrev w (g : IntegralGL) := carryLine g 0
abbrev b (g : IntegralGL) := carryLine g 1
abbrev c (g : IntegralGL) := carryLine g 2
abbrev a (g : IntegralGL) := carryLine g 3
abbrev t (g : IntegralGL) := carryLine g 4

theorem actualVector_span (g : IntegralGL) (i : Fin 5) :
    Submodule.span ℚ {rationalVector (actualVector g i)} = (carryLine g i).val := by
  rw [actualVector,rationalVector_mulVec]
  rfl

/-- The center vector is exactly b-w, with its actual sign. -/
theorem actualVector_t (g : IntegralGL) : actualVector g 4 = actualVector g 1 - actualVector g 0 := by
  unfold actualVector
  rw [show carryVector 4 = carryVector 1 - carryVector 0 by decide +kernel,Matrix.mulVec_sub]

/-- The corrected sum vector is exactly b+c-w. -/
theorem actualVector_a (g : IntegralGL) :
    actualVector g 3 = actualVector g 1 + actualVector g 2 - actualVector g 0 := by
  unfold actualVector
  rw [show carryVector 3 = carryVector 1 + carryVector 2 - carryVector 0 by decide +kernel,
    Matrix.mulVec_sub,Matrix.mulVec_add]

/-- The five rational vertices remain pairwise distinct under every integral basis change. -/
theorem carryLine_injective (g : IntegralGL) : Function.Injective (carryLine g) := by
  intro i j h
  have hm : rationalRepresentation g (rationalVector (carryVector i)) ∈
      Submodule.span ℚ {rationalRepresentation g (rationalVector (carryVector j))} := by
    change rationalRepresentation g (rationalVector (carryVector i)) ∈ (carryLine g j).val
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have hb : r • rationalVector (carryVector j) = rationalVector (carryVector i) := by
    apply (rationalRepresentation g).injective
    rw [map_smul]
    exact hr
  have hs := PrimitiveLineUniqueness.primitive_eq_or_neg_of_mem_span
    (carryVector_primitive j) (carryVector_primitive i) (Submodule.mem_span_singleton.mpr ⟨r,hb⟩)
  have hc : ∀ i j : Fin 5, (carryVector i = carryVector j ∨ carryVector i = -carryVector j) → i = j := by
    decide +kernel
  exact hc i j hs

@[simp] theorem carryLine_inj (g : IntegralGL) (i j : Fin 5) :
    carryLine g i = carryLine g j ↔ i = j := (carryLine_injective g).eq_iff

/-- Residual primitive vectors do not lie in the fixed rational line w. -/
theorem actualVector_not_mem_w (g : IntegralGL) (i : Fin 5) (hi : i ≠ 0) :
    rationalVector (actualVector g i) ∉ (w g).val := by
  intro hm
  have hs : (carryLine g i).val ≤ (w g).val := by
    rw [← actualVector_span]
    exact Submodule.span_le.mpr (by intro x hx; rcases hx with rfl; exact hm)
  have he : (carryLine g i).val = (w g).val :=
    Submodule.eq_of_le_of_finrank_eq hs ((carryLine g i).property.trans (w g).property.symm)
  exact hi ((carryLine_injective g) (Subtype.ext he))

/-- Bases (w,t,c), (t,c,w), and (w,t,a). Their first two vectors sum to b,a,b. -/
def basisMatrix : Fin 3 → Mat :=
  ![!![1,-1,0;0,1,0;0,0,1],
    !![-1,0,1;1,0,0;0,1,0],
    !![1,-1,-1;0,1,1;0,0,1]]

def inverseMatrix : Fin 3 → Mat :=
  ![!![1,1,0;0,1,0;0,0,1],
    !![0,1,0;0,0,1;1,1,0],
    !![1,1,0;0,1,-1;0,0,1]]

theorem basisMatrix_mul_inverse : ∀ i, basisMatrix i * inverseMatrix i = 1 := by decide +kernel
theorem inverseMatrix_mul_basis : ∀ i, inverseMatrix i * basisMatrix i = 1 := by decide +kernel

/-- Explicit unimodular changes of the actual integer basis. -/
def basisChange (i : Fin 3) : IntegralGL :=
  ⟨basisMatrix i,inverseMatrix i,basisMatrix_mul_inverse i,inverseMatrix_mul_basis i⟩

theorem basisMatrix_det : ∀ i, (basisMatrix i).det = 1 := by decide +kernel

def frameIndex : Fin 3 → Fin 4 → Fin 5 := ![![0,4,2,1],![4,2,0,3],![0,4,3,1]]

private theorem basisMatrix_template : ∀ i j,
    (basisMatrix i).mulVec (integralTemplate j) = carryVector (frameIndex i j) := by decide +kernel

theorem basisChange_template (i : Fin 3) (j : Fin 4) :
    rationalRepresentation (basisChange i) (template j) = rationalVector (carryVector (frameIndex i j)) := by
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec]
  exact congrArg rationalVector (basisMatrix_template i j)

/-- The actual augmented frame template gives exactly the four required rational lines. -/
theorem augmentedLine_basisChange (g : IntegralGL) (i : Fin 3) (j : Fin 4) :
    augmentedLine (g * basisChange i) j = carryLine g (frameIndex i j) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * basisChange i) (template j)} =
    Submodule.span ℚ {rationalRepresentation g (rationalVector (carryVector (frameIndex i j)))}
  rw [map_mul]
  change Submodule.span ℚ {rationalRepresentation g (rationalRepresentation (basisChange i) (template j))} = _
  rw [basisChange_template]

/-- Ordered triangles in the carrying replacement. -/
def residualList (g : IntegralGL) : Fin 3 → List RationalLine :=
  ![[t g,b g,c g],[a g,t g,c g],[a g,b g,t g]]

private theorem fin4_univ : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide +kernel

/-- Each residual triangle, together with w, is literally an actual augmented frame. -/
theorem augmentedFrame_eq (g : IntegralGL) (i : Fin 3) :
    augmentedFrame (g * basisChange i) = (w g :: residualList g i).toFinset := by
  change Finset.univ.image (augmentedLine (g * basisChange i)) = _
  rw [show augmentedLine (g * basisChange i) = (fun j => carryLine g (frameIndex i j)) from
    funext (augmentedLine_basisChange g i),fin4_univ]
  fin_cases i <;> ext L <;>
    simp [residualList,frameIndex,w,a,b,c,t,or_comm,or_left_comm]

theorem tetrahedron_ambient (g : IntegralGL) (i : Fin 3) :
    (w g :: residualList g i).toFinset ∈ ambient := by
  rw [← augmentedFrame_eq]
  exact augmentedFrame_mem _

/-- The genuine vertex link: the residual face excludes w and adjoins to an ambient face. -/
def vertexLink (g : IntegralGL) : PreAbstractSimplicialComplex RationalLine where
  faces := {s | s.Nonempty ∧ w g ∉ s ∧ insert (w g) s ∈ ambient}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro q hqs hq
    refine ⟨hq,fun h => hs.2.1 (hqs h),?_⟩
    exact (ambient.isRelLowerSet_faces hs.2.2).2
      (Finset.insert_subset_insert (w g) hqs) (Finset.insert_nonempty _ _)

/-- No residual triangle contains the fixed vertex. -/
theorem w_not_mem_residualList (g : IntegralGL) (i : Fin 3) : w g ∉ residualList g i := by
  fin_cases i <;> simp [residualList,w,a,b,c,t]

/-- All three triangles are actual vertex-link faces, with explicit exclusion of w. -/
theorem residualList_link (g : IntegralGL) (i : Fin 3) :
    (residualList g i).toFinset ∈ vertexLink g := by
  refine ⟨?_,?_,?_⟩
  · fin_cases i <;> simp [residualList]
  · simpa only [List.mem_toFinset] using w_not_mem_residualList g i
  · simpa only [List.toFinset_cons] using tetrahedron_ambient g i

/-- Height is computed from these literal primitive integral vectors. -/
theorem height_carryLine (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (i : Fin 5) :
    height F (carryLine g i) = (F (actualVector g i)).natAbs :=
  height_eq_natAbs F _ (actualVector_primitive g i) (actualVector_span g i)

/-- Every residual vertex lies strictly below N in the carrying case. -/
theorem residual_heights_lt (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (N : ℤ)
    (hN : 0 < N) (hw : F (actualVector g 0) = N)
    (hb0 : 0 ≤ F (actualVector g 1)) (hbN : F (actualVector g 1) < N)
    (hc0 : 0 ≤ F (actualVector g 2)) (hcN : F (actualVector g 2) < N)
    (hcarry : N ≤ F (actualVector g 1) + F (actualVector g 2))
    (i : Fin 5) (hi : i ≠ 0) : (height F (carryLine g i) : ℤ) < N := by
  rw [height_carryLine,Int.natCast_natAbs]
  have ha : F (actualVector g 3) = F (actualVector g 1) + F (actualVector g 2) - N := by
    rw [actualVector_a,map_sub,map_add,hw]
  have ht : F (actualVector g 4) = F (actualVector g 1) - N := by
    rw [actualVector_t,map_sub,hw]
  apply abs_lt.mpr
  fin_cases i
  · exact (hi rfl).elim
  · change -N < F (actualVector g 1) ∧ F (actualVector g 1) < N
    omega
  · change -N < F (actualVector g 2) ∧ F (actualVector g 2) < N
    omega
  · change -N < F (actualVector g 3) ∧ F (actualVector g 3) < N
    omega
  · change -N < F (actualVector g 4) ∧ F (actualVector g 4) < N
    omega

/-- The strict center bound records the negative representative chosen in the carrying correction. -/
theorem center_value_bounds (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (N : ℤ)
    (hw : F (actualVector g 0) = N)
    (hbN : F (actualVector g 1) < N) (hcN : F (actualVector g 2) < N)
    (hcarry : N ≤ F (actualVector g 1) + F (actualVector g 2)) :
    -N < F (actualVector g 4) ∧ F (actualVector g 4) < 0 := by
  rw [actualVector_t,map_sub,hw]
  omega

/-- The literal oriented carrying replacement on actual rational lines. -/
def replacement (g : IntegralGL) : Chain RationalLine :=
  AugmentedHeightArithmetic.subdividedTriangle (a g) (b g) (c g) (t g)

/-- The three actual link triangles have the same boundary as the formal reduced triangle. -/
theorem boundary_replacement (g : IntegralGL) :
    boundary (replacement g) = boundary (simplex [a g,b g,c g]) :=
  AugmentedHeightArithmetic.boundary_subdividedTriangle (a g) (b g) (c g) (t g)

theorem residual_simplex_mem_link (g : IntegralGL) (i : Fin 3) :
    simplex (residualList g i) ∈ chains (vertexLink g) 3 := by
  have hlen : (residualList g i).length = 3 := by fin_cases i <;> rfl
  have hallowed : Allowed (vertexLink g) (residualList g i) := by
    apply Or.inr
    convert residualList_link g i using 1
    ext L
    simp only [List.mem_toFinset]
  simpa only [hlen] using simplex_mem_chains (vertexLink g) (residualList g i) hallowed

/-- The carrying replacement is supported on the genuine vertex link. -/
theorem replacement_mem_link (g : IntegralGL) : replacement g ∈ chains (vertexLink g) 3 := by
  exact (chains (vertexLink g) 3).add_mem
    ((chains (vertexLink g) 3).add_mem (residual_simplex_mem_link g 0) (residual_simplex_mem_link g 1))
    (residual_simplex_mem_link g 2)

/-- The actual full lower-height subcomplex of the genuine vertex link. -/
def lowerLink (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (N : ℤ) :
    PreAbstractSimplicialComplex RationalLine where
  faces := {s | s ∈ vertexLink g ∧ ∀ L ∈ s, (height F L : ℤ) < N}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((vertexLink g).isRelLowerSet_faces hs.1).1,?_⟩
    intro q hqs hq
    exact ⟨((vertexLink g).isRelLowerSet_faces hs.1).2 hqs hq,
      fun L hL => hs.2 L (hqs hL)⟩

/-- Every residual triangle belongs to the actual lower-height link under the carrying bounds. -/
theorem residualList_lowerLink (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (N : ℤ)
    (hN : 0 < N) (hw : F (actualVector g 0) = N)
    (hb0 : 0 ≤ F (actualVector g 1)) (hbN : F (actualVector g 1) < N)
    (hc0 : 0 ≤ F (actualVector g 2)) (hcN : F (actualVector g 2) < N)
    (hcarry : N ≤ F (actualVector g 1) + F (actualVector g 2)) (i : Fin 3) :
    (residualList g i).toFinset ∈ lowerLink F g N := by
  refine ⟨residualList_link g i,?_⟩
  intro L hL
  rw [List.mem_toFinset] at hL
  fin_cases i <;> simp [residualList] at hL <;> rcases hL with rfl | rfl | rfl <;>
    exact residual_heights_lt F g N hN hw hb0 hbN hc0 hcN hcarry _ (by decide)

/-- The complete carrying replacement is an actual finite chain entirely in the lower link. -/
theorem replacement_mem_lowerLink (F : IntegralVector →ₗ[ℤ] ℤ) (g : IntegralGL) (N : ℤ)
    (hN : 0 < N) (hw : F (actualVector g 0) = N)
    (hb0 : 0 ≤ F (actualVector g 1)) (hbN : F (actualVector g 1) < N)
    (hc0 : 0 ≤ F (actualVector g 2)) (hcN : F (actualVector g 2) < N)
    (hcarry : N ≤ F (actualVector g 1) + F (actualVector g 2)) :
    replacement g ∈ chains (lowerLink F g N) 3 := by
  have hmem (i : Fin 3) : simplex (residualList g i) ∈ chains (lowerLink F g N) 3 := by
    have hlen : (residualList g i).length = 3 := by fin_cases i <;> rfl
    have hallowed : Allowed (lowerLink F g N) (residualList g i) := by
      apply Or.inr
      convert residualList_lowerLink F g N hN hw hb0 hbN hc0 hcN hcarry i using 1
      ext L
      simp only [List.mem_toFinset]
    simpa only [hlen] using simplex_mem_chains (lowerLink F g N) (residualList g i) hallowed
  exact (chains (lowerLink F g N) 3).add_mem
    ((chains (lowerLink F g N) 3).add_mem (hmem 0) (hmem 1)) (hmem 2)

end TernaryPoly.AugmentedCarryingGeometry
