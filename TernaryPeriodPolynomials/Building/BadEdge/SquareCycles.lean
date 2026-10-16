module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.SquareCaps
public import TernaryPeriodPolynomials.Building.BadTriangle.NeighborCycles
public import TernaryPeriodPolynomials.Building.BadEdge.LinkChains

@[expose] public section


/-! Actual ambient square cycles with prescribed two-bad leading term and no
three-bad component. The square itself remains a loop in the bad-edge link. -/

noncomputable section
namespace TernaryPoly.BadEdgeSquareCycles
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces GoodAugmentedNormalForm
open OrientedListChains OrientedChainJoin OrientedChainProjection
open AugmentedSquareCaps BadEdgeLinkVertices

local instance : DecidableEq RationalLine := Classical.decEq _

abbrev A (g : IntegralGL) := AugmentedSquareCaps.A g
abbrev B (g : IntegralGL) := AugmentedSquareCaps.B g
abbrev C (g : IntegralGL) := AugmentedSquareCaps.C g
abbrev D (g : IntegralGL) := AugmentedSquareCaps.D g

abbrev u (g : IntegralGL) := augmentedLine g 0
abbrev v (g : IntegralGL) := augmentedLine g 1

def edge (g : IntegralGL) : Chain RationalLine := simplex [u g,v g]
def T (g : IntegralGL) : Chain RationalLine := simplex [A g,B g,D g] + simplex [A g,D g,C g]
def q (g : IntegralGL) : Chain RationalLine := boundary (T g)

/-- The diagonal cancels, leaving the positively oriented square boundary. -/
theorem q_eq (g : IntegralGL) : q g =
    simplex [A g,B g] + simplex [B g,D g] - simplex [C g,D g] - simplex [A g,C g] := by
  simp only [q,T,map_add,boundary_cons,boundary_nil,map_zero,map_sub,cons_simplex,sub_zero]
  rw [simplex_swap_eq_neg (D g) (C g)]
  abel

/-- The join formula closes a two-bad square loop using four one-bad cones. -/
def Z (g : IntegralGL) : Chain RationalLine :=
  join (edge g) (q g) + join (boundary (edge g)) (T g)

def termList (g : IntegralGL) : Fin 8 → List RationalLine :=
  ![[u g,v g,A g,B g],[u g,v g,B g,D g],[u g,v g,C g,D g],[u g,v g,A g,C g],
    [v g,A g,B g,D g],[v g,A g,D g,C g],[u g,A g,B g,D g],[u g,A g,D g,C g]]

theorem Z_eq (g : IntegralGL) : Z g =
    simplex (termList g 0) + simplex (termList g 1) - simplex (termList g 2) -
    simplex (termList g 3) + simplex (termList g 4) + simplex (termList g 5) -
    simplex (termList g 6) - simplex (termList g 7) := by
  simp only [Z,edge,q_eq,T,boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,
    map_sub,map_add,LinearMap.sub_apply,join_simplex,List.cons_append,List.nil_append]
  change _ = simplex [u g,v g,A g,B g] + simplex [u g,v g,B g,D g] -
    simplex [u g,v g,C g,D g] - simplex [u g,v g,A g,C g] +
    simplex [v g,A g,B g,D g] + simplex [v g,A g,D g,C g] -
    simplex [u g,A g,B g,D g] - simplex [u g,A g,D g,C g]
  abel

/-- Exact deletion cancellation proves the ambient cycle identity. -/
theorem boundary_Z (g : IntegralGL) : boundary (Z g) = 0 := by
  simp only [Z,edge,q,T,map_add,map_sub,map_zero,LinearMap.sub_apply,
    boundary_cons,boundary_nil,sub_zero,cons_simplex,join_simplex,
    List.cons_append,List.nil_append]
  abel

/-- The four affine square corners in the first two basis coordinates. -/
def squarePoint : Fin 4 → IntegerGridExactness.Vertex := ![(0,0),(1,0),(0,1),(1,1)]

theorem capLine_coordinate (g : IntegralGL) (i : Fin 4) :
    capLine g i.castSucc = coordinateLine g (squarePoint i) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (capVector i.castSucc))} =
    Submodule.span ℚ {rationalVector (g.val.mulVec (affineVector (squarePoint i)))}
  rw [rationalVector_mulVec]
  have he : capVector i.castSucc = affineVector (squarePoint i) := by
    fin_cases i <;> rfl
  rw [he]

private theorem leading_term_mem (g : IntegralGL) (i : Fin 4) :
    simplex (termList g i.castSucc.castSucc.castSucc.castSucc) ∈ chains ambient 4 := by
  let es : Fin 4 → IntegerGridExactness.Edge :=
    ![((0,0),0),((1,0),1),((0,1),0),((0,0),1)]
  have hf := BadEdgeLinkGrid.face_of_gridAdjacent g (es i).1
    (IntegerGridExactness.edgeHead (es i)) (BadEdgeLinkChains.gridAdjacent_edge (es i))
  have hallowed : Allowed ambient (termList g i.castSucc.castSucc.castSucc.castSucc) := by
    apply Or.inr
    convert hf using 1
    have hA : A g = coordinateLine g (0,0) := capLine_coordinate g 0
    have hB : B g = coordinateLine g (1,0) := capLine_coordinate g 1
    have hC : C g = coordinateLine g (0,1) := capLine_coordinate g 2
    have hD : D g = coordinateLine g (1,1) := capLine_coordinate g 3
    fin_cases i <;> ext L <;>
      simp [termList,es,u,v,hA,hB,hC,hD,IntegerGridExactness.edgeHead]
  have hlen : (termList g i.castSucc.castSucc.castSucc.castSucc).length = 4 := by
    fin_cases i <;> rfl
  simpa only [hlen] using simplex_mem_chains ambient _ hallowed

/-- Coordinates of the two bad basis vectors and four good square corners. -/
def coneVector : Fin 6 → IntegralVector :=
  ![![1,0,0],![0,1,0],capVector 0,capVector 1,capVector 2,capVector 3]

def coneLine (g : IntegralGL) : Fin 6 → RationalLine := ![u g,v g,A g,B g,C g,D g]

/-- Bases (u,A,D), (u,C,A), (v,B,A), (v,A,D); their first sums are B,D,D,C. -/
def coneMatrix : Fin 4 → AugmentedSquareCaps.Mat :=
  ![!![1,0,1;0,0,1;0,1,1],!![1,0,0;0,1,0;0,1,1],
    !![0,1,0;1,0,0;0,1,1],!![0,0,1;1,0,1;0,1,1]]

def coneIndex : Fin 4 → Fin 4 → Fin 6 :=
  ![![0,2,5,3],![0,4,2,5],![1,3,2,5],![1,2,5,4]]

theorem coneMatrix_unit (i : Fin 4) : IsUnit (coneMatrix i).det := by
  have h : ∀ j : Fin 4, (coneMatrix j).det = (![-1,1,-1,1] : Fin 4 → ℤ) j := by
    decide +kernel
  rw [h]
  fin_cases i <;> norm_num

def coneGL (i : Fin 4) : IntegralGL := Matrix.nonsingInvUnit (coneMatrix i) (coneMatrix_unit i)

private theorem coneMatrix_template (i j : Fin 4) :
    (coneMatrix i).mulVec (GoodAugmentedNormalForm.integralTemplate j) =
      coneVector (coneIndex i j) := by
  exact (by decide +kernel : ∀ i j : Fin 4,
    (coneMatrix i).mulVec (GoodAugmentedNormalForm.integralTemplate j) =
      coneVector (coneIndex i j)) i j

private theorem coneLine_val (g : IntegralGL) (i : Fin 6) :
    (coneLine g i).val = Submodule.span ℚ {rationalRepresentation g (rationalVector (coneVector i))} := by
  fin_cases i
  · change Submodule.span ℚ {rationalRepresentation g (template 0)} =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (coneVector 0))}
    rw [show rationalVector (coneVector 0) = template 0 by decide +kernel]
  · change Submodule.span ℚ {rationalRepresentation g (template 1)} =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (coneVector 1))}
    rw [show rationalVector (coneVector 1) = template 1 by decide +kernel]
  · rfl
  · rfl
  · rfl
  · rfl

theorem augmentedLine_coneGL (g : IntegralGL) (i j : Fin 4) :
    augmentedLine (g * coneGL i) j = coneLine g (coneIndex i j) := by
  apply Subtype.ext
  rw [coneLine_val]
  change Submodule.span ℚ {rationalRepresentation (g * coneGL i) (template j)} = _
  rw [map_mul,LinearEquiv.mul_apply]
  have he : rationalRepresentation (coneGL i) (template j) =
      rationalVector (coneVector (coneIndex i j)) := by
    rw [← GoodAugmentedNormalForm.rationalVector_integralTemplate,← rationalVector_mulVec]
    exact congrArg rationalVector (coneMatrix_template i j)
  rw [he]

def coneList (g : IntegralGL) : Fin 4 → List RationalLine :=
  ![[u g,A g,B g,D g],[u g,A g,D g,C g],[v g,A g,B g,D g],[v g,A g,D g,C g]]

theorem coneList_frame (g : IntegralGL) (i : Fin 4) :
    (coneList g i).toFinset = augmentedFrame (g * coneGL i) := by
  unfold augmentedFrame
  rw [show augmentedLine (g * coneGL i) = (fun j => coneLine g (coneIndex i j)) from
    funext (augmentedLine_coneGL g i),show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]
  fin_cases i <;> ext L <;> simp [coneList,coneIndex,coneLine,or_comm,or_left_comm]

theorem cone_simplex_mem (g : IntegralGL) (i : Fin 4) :
    simplex (coneList g i) ∈ chains ambient 4 := by
  have ha : Allowed ambient (coneList g i) := by
    apply Or.inr
    convert (show (coneList g i).toFinset ∈ ambient from by rw [coneList_frame]; exact augmentedFrame_mem _) using 1
  have hlen : (coneList g i).length = 4 := by fin_cases i <;> rfl
  simpa only [hlen] using simplex_mem_chains ambient _ ha

/-- All eight displayed tetrahedra are actual ambient augmented faces. -/
theorem term_simplex_mem (g : IntegralGL) (i : Fin 8) :
    simplex (termList g i) ∈ chains ambient 4 := by
  fin_cases i
  · exact leading_term_mem g 0
  · exact leading_term_mem g 1
  · exact leading_term_mem g 2
  · exact leading_term_mem g 3
  · exact cone_simplex_mem g 2
  · exact cone_simplex_mem g 3
  · exact cone_simplex_mem g 0
  · exact cone_simplex_mem g 1

theorem Z_mem_chains (g : IntegralGL) : Z g ∈ chains ambient 4 := by
  rw [Z_eq]
  repeat first | apply Submodule.add_mem | apply Submodule.sub_mem
  all_goals exact term_simplex_mem g _

private theorem u_bad (g : IntegralGL) (h0 : columnResidue g 0 = 0) : ¬Good (u g).val := by
  rw [good_augmentedLine_iff_residue]
  exact fun h => h h0

private theorem v_bad (g : IntegralGL) (h1 : columnResidue g 1 = 0) : ¬Good (v g).val := by
  rw [good_augmentedLine_iff_residue]
  exact fun h => h h1

/-- Exact bad-count values: four two-bad terms followed by four one-bad terms. -/
theorem term_badCount (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (i : Fin 8) :
    badCount (fun L : RationalLine => Good L.val) (termList g i) =
      (if i.val < 4 then 2 else 1) := by
  have huv : u g ≠ v g := fun h => (by decide : (0 : Fin 4) ≠ 1) (augmentedLine_injective g h)
  have hA := capLine_good g h0 h1 h2 0
  have hB := capLine_good g h0 h1 h2 1
  have hC := capLine_good g h0 h1 h2 2
  have hD := capLine_good g h0 h1 h2 3
  fin_cases i <;> simp [badCount,badVertices,termList,Finset.filter_insert,
    Finset.filter_singleton,u_bad g h0,v_bad g h1,huv,A,B,C,D,hA,hB,hC,hD]

/-- The entire two-bad component is exactly the joined square loop. -/
theorem leading_badCount_two (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) :
    badCountProjection (fun L : RationalLine => Good L.val) 2 (Z g) = join (edge g) (q g) := by
  rw [Z_eq]
  simp only [map_add,map_sub,badCountProjection_simplex,term_badCount g h0 h1 h2]
  norm_num [Fin.ext_iff]
  simp only [edge,q_eq,map_sub,map_add,join_simplex,List.cons_append,List.nil_append,termList]
  rfl

/-- The square cycle introduces no three-bad simplices. -/
theorem badCount_three_zero (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) :
    badCountProjection (fun L : RationalLine => Good L.val) 3 (Z g) = 0 := by
  rw [Z_eq]
  simp only [map_add,map_sub,badCountProjection_simplex,term_badCount g h0 h1 h2]
  norm_num [Fin.ext_iff]

/-- Affine completion translates all four square corners by the prescribed integer point. -/
theorem capLine_affineCompletion (g : IntegralGL) (p : IntegerGridExactness.Vertex) (i : Fin 4) :
    capLine (affineCompletion g p) i.castSucc =
      coordinateLine g (p.1 + (squarePoint i).1,p.2 + (squarePoint i).2) := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (affineCompletion g p)
    (rationalVector (capVector i.castSucc)))} = _
  rw [← rationalVector_mulVec]
  apply congrArg (fun a : IntegralVector => Submodule.span ℚ {rationalVector a})
  change (completionMatrix g (affineVector p)).mulVec (capVector i.castSucc) = _
  rw [completionMatrix,← Matrix.mulVec_mulVec]
  congr 1
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateMatrix,affineVector,capVector,squarePoint,Matrix.mulVec,dotProduct,
      Fin.sum_univ_three,add_comm]

/-- The translated square boundary has exactly the grid square-loop orientation. -/
theorem q_affineCompletion (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (p : IntegerGridExactness.Vertex) :
    q (affineCompletion g p) = (BadEdgeLinkChains.squareLoop g h0 h1 h2 p).val := by
  have hA : A (affineCompletion g p) = coordinateLine g p := by
    simpa [squarePoint] using capLine_affineCompletion g p 0
  have hB : B (affineCompletion g p) = coordinateLine g (p.1+1,p.2) := by
    simpa [squarePoint] using capLine_affineCompletion g p 1
  have hC : C (affineCompletion g p) = coordinateLine g (p.1,p.2+1) := by
    simpa [squarePoint] using capLine_affineCompletion g p 2
  have hD : D (affineCompletion g p) = coordinateLine g (p.1+1,p.2+1) := by
    simpa [squarePoint] using capLine_affineCompletion g p 3
  rw [q_eq,hA,hB,hC,hD,BadEdgeLinkChains.squareLoop_val]

/-- One affine square loop has an actual ambient correction cycle with precisely its two-bad part. -/
theorem affine_square_cycle (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (p : IntegerGridExactness.Vertex) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 2 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1])
          (BadEdgeLinkChains.squareLoop g h0 h1 h2 p).val := by
  have k0 : columnResidue (affineCompletion g p) 0 = 0 := by
    rw [BadTriangleNeighborCycles.affineCompletion_residue_zero,h0]
  have k1 : columnResidue (affineCompletion g p) 1 = 0 := by
    rw [BadTriangleNeighborCycles.affineCompletion_residue_one,h1]
  have k2 : columnResidue (affineCompletion g p) 2 ≠ 0 := by
    rw [BadTriangleNeighborCycles.affineCompletion_residue_two g p h0 h1]
    exact h2
  refine ⟨Z (affineCompletion g p),Z_mem_chains _,boundary_Z _,badCount_three_zero _ k0 k1 k2,?_⟩
  rw [leading_badCount_two _ k0 k1 k2,q_affineCompletion g h0 h1 h2 p]
  change join (simplex [augmentedLine (affineCompletion g p) 0,
    augmentedLine (affineCompletion g p) 1]) _ = _
  rw [affineCompletion_line_zero,affineCompletion_line_one]

/-- Every finite square-loop combination has an actual ambient cycle with the prescribed
entire two-bad leading component and with three-bad component zero. -/
theorem exists_cycle_with_leading (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (a : IntegerGridExactness.C₂) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 2 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1])
          ((BadEdgeLinkChains.edgeTransport g h0 h1 h2 (IntegerGridExactness.boundary₂ a)).val) := by
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp,by simp⟩
  | add a b ha hb =>
    obtain ⟨z,hz,hd,h3,h2z⟩ := ha
    obtain ⟨w,hw,he,k3,h2w⟩ := hb
    refine ⟨z+w,(chains ambient 4).add_mem hz hw,by rw [map_add,hd,he,add_zero],
      by rw [map_add,h3,k3,add_zero],?_⟩
    simpa only [map_add,Submodule.coe_add] using congrArg₂ (·+·) h2z h2w
  | single p q =>
    obtain ⟨z,hz,hd,h3,h2z⟩ := affine_square_cycle g h0 h1 h2 p
    refine ⟨q • z,(chains ambient 4).smul_mem q hz,by rw [map_smul,hd,smul_zero],
      by rw [map_smul,h3,smul_zero],?_⟩
    rw [map_smul,h2z,IntegerGridExactness.boundary₂_single,map_smul]
    change q • join (simplex [augmentedLine g 0,augmentedLine g 1])
      (BadEdgeLinkChains.squareLoop g h0 h1 h2 p).val =
      join (simplex [augmentedLine g 0,augmentedLine g 1])
        (q • (BadEdgeLinkChains.squareLoop g h0 h1 h2 p).val)
    rw [map_smul]

end TernaryPoly.BadEdgeSquareCycles
