module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.EightTermCycle
public import TernaryPeriodPolynomials.Building.BadTriangle.Link
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin

@[expose] public section

noncomputable section
namespace TernaryPoly.BadTriangleNeighborCycles
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces GoodAugmentedNormalForm
open GoodIntegralNormalization OrientedListChains OrientedChainJoin OrientedChainProjection
open BadEdgeLinkVertices BadTriangleLink
open AugmentedEightTermCycle
local instance : DecidableEq RationalLine := Classical.decEq _

/-- The three-bad part of the eight-term cycle has the standard core orientation. -/
theorem leading_eq_join (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) :
    badCountProjection (fun L : RationalLine => Good L.val) 3 (Z g) =
      join (simplex [u g,v g,s g]) (simplex [w2 g] - simplex [w g]) := by
  rw [leading_badCount_three g h0 h1 h2,map_sub,join_simplex,join_simplex]
  simp only [List.cons_append,List.nil_append]
  have e1 := simplex_swap (w g) (v g) [u g,s g]
  have e2 := congrArg (cons (v g)) (simplex_swap (w g) (u g) [s g])
  have e3 := congrArg ((cons (v g)).comp (cons (u g))) (simplex_swap (w g) (s g) [])
  have e4 := simplex_swap (v g) (u g) [s g,w g]
  have e5 := simplex_swap (v g) (u g) [w2 g,s g]
  have e6 := congrArg ((cons (u g)).comp (cons (v g))) (simplex_swap (w2 g) (s g) [])
  simp only [LinearMap.comp_apply,map_add,cons_simplex,map_zero] at e2 e3 e6
  have ha : simplex [w g,v g,u g,s g] = simplex [u g,v g,s g,w g] := by
    rw [eq_neg_of_add_eq_zero_left e1,eq_neg_of_add_eq_zero_left e2,neg_neg,
      eq_neg_of_add_eq_zero_left e3,eq_neg_of_add_eq_zero_left e4,neg_neg]
  have hb : simplex [v g,u g,w2 g,s g] = simplex [u g,v g,s g,w2 g] := by
    rw [eq_neg_of_add_eq_zero_left e5,eq_neg_of_add_eq_zero_left e6,neg_neg]
  rw [ha,hb]
  abel

/-- The first four cycle lines are the literal four augmented frame lines. -/
theorem cycleLine_cast (g : IntegralGL) (i : Fin 4) :
    cycleLine g i.castSucc.castSucc = augmentedLine g i := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation g (rationalVector (cycleVector i.castSucc.castSucc))} =
    Submodule.span ℚ {rationalRepresentation g (template i)}
  congr 3
  exact (show ∀ j : Fin 4, rationalVector (cycleVector j.castSucc.castSucc) = template j from
    by decide +kernel) i

/-- Affine completion preserves the first two residue coordinates. -/
theorem affineCompletion_residue_zero (g : IntegralGL) (p : ℤ × ℤ) :
    columnResidue (affineCompletion g p) 0 = columnResidue g 0 := by
  change (∑ i, ((completionMatrix g (affineVector p)).col 0 i : ZMod 3)) = _
  rw [completionMatrix_col_zero]
  rfl

theorem affineCompletion_residue_one (g : IntegralGL) (p : ℤ × ℤ) :
    columnResidue (affineCompletion g p) 1 = columnResidue g 1 := by
  change (∑ i, ((completionMatrix g (affineVector p)).col 1 i : ZMod 3)) = _
  rw [completionMatrix_col_one]
  rfl

/-- Over a bad first edge, all affine complements have the same nonzero last residue. -/
theorem affineCompletion_residue_two (g : IntegralGL) (p : ℤ × ℤ)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    columnResidue (affineCompletion g p) 2 = columnResidue g 2 := by
  change (∑ i, ((completionMatrix g (affineVector p)).col 2 i : ZMod 3)) = _
  rw [completionMatrix_col_two,residue_mulVec_bad_edge g h0 h1]
  simp [affineVector]

/-- The extra good vertex is the horizontal neighbor of the affine complement. -/
theorem w2_affineCompletion (g : IntegralGL) (p : ℤ × ℤ) :
    w2 (affineCompletion g p) = coordinateLine g (p.1+1,p.2) := by
  apply Subtype.ext
  change Submodule.span ℚ {(rationalRepresentation (affineCompletion g p)
      (rationalVector (cycleVector 4)))} = _
  rw [← rationalVector_mulVec]
  apply congrArg (fun a : IntegralVector => Submodule.span ℚ {rationalVector a})
  change (completionMatrix g (affineVector p)).mulVec (cycleVector 4) = _
  rw [completionMatrix,← Matrix.mulVec_mulVec]
  congr 1
  ext i
  fin_cases i <;> simp [coordinateMatrix,affineVector,cycleVector,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three]
  omega

/-- The eight-term chain realizes any horizontal neighbor difference with no other three-bad part. -/
theorem horizontal_cycle (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3])
          (simplex [coordinateLine g (p.1+1,p.2)] - simplex [coordinateLine g p]) := by
  refine ⟨Z (affineCompletion g p),Z_mem_chains _,boundary_Z _,?_⟩
  rw [leading_eq_join _ (by rw [affineCompletion_residue_zero,h0])
    (by rw [affineCompletion_residue_one,h1])
    (by rw [affineCompletion_residue_two g p h0 h1]; exact h2)]
  rw [show u (affineCompletion g p) = augmentedLine (affineCompletion g p) 0 from cycleLine_cast _ 0,
    show v (affineCompletion g p) = augmentedLine (affineCompletion g p) 1 from cycleLine_cast _ 1,
    show s (affineCompletion g p) = augmentedLine (affineCompletion g p) 3 from cycleLine_cast _ 3,
    show w (affineCompletion g p) = augmentedLine (affineCompletion g p) 2 from cycleLine_cast _ 2,
    affineCompletion_line_zero,affineCompletion_line_one,affineCompletion_line_three,
    affineCompletion_line_two,w2_affineCompletion]

/-- The literal integral exchange of the first two frame columns. -/
def swapMatrix : Matrix (Fin 3) (Fin 3) ℤ := !![0,1,0;1,0,0;0,0,1]

def swapBasis : IntegralGL :=
  ⟨swapMatrix,swapMatrix,by decide +kernel,by decide +kernel⟩

def swapIndex : Fin 4 → Fin 4 := ![1,0,2,3]

private theorem swapMatrix_template (i : Fin 4) :
    swapMatrix.mulVec (integralTemplate i) = integralTemplate (swapIndex i) := by
  exact (show ∀ j : Fin 4, swapMatrix.mulVec (integralTemplate j) =
    integralTemplate (swapIndex j) from by decide +kernel) i

theorem augmentedLine_swap (g : IntegralGL) (i : Fin 4) :
    augmentedLine (g * swapBasis) i = augmentedLine g (swapIndex i) := by
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (g * swapBasis) (template i)} = _
  rw [map_mul,LinearEquiv.mul_apply]
  have he : rationalRepresentation swapBasis (template i) = template (swapIndex i) := by
    rw [← rationalVector_integralTemplate,← rationalVector_mulVec,swapBasis,swapMatrix_template,
      rationalVector_integralTemplate]
  rw [he]
  rfl

theorem coordinateLine_swap (g : IntegralGL) (p : ℤ × ℤ) :
    coordinateLine (g * swapBasis) p = coordinateLine g (p.2,p.1) := by
  apply Subtype.ext
  apply congrArg (fun a : IntegralVector => Submodule.span ℚ {rationalVector a})
  change (g.val * swapMatrix).mulVec (affineVector p) = _
  rw [← Matrix.mulVec_mulVec]
  congr 1
  ext i
  fin_cases i <;> simp [swapMatrix,affineVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

theorem columnResidue_swap (g : IntegralGL) (i : Fin 3) :
    columnResidue (g * swapBasis) i = columnResidue g ((![1,0,2] : Fin 3 → Fin 3) i) := by
  unfold columnResidue
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change (g.val * swapMatrix) j i = _
  fin_cases i <;> simp [swapMatrix,Matrix.mul_apply,Fin.sum_univ_three]

/-- Exchanging the two bad columns realizes vertical neighbors with the corrected core orientation. -/
theorem vertical_cycle (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3])
          (simplex [coordinateLine g (p.1,p.2+1)] - simplex [coordinateLine g p]) := by
  obtain ⟨z,hz,hd,hp⟩ := horizontal_cycle (g * swapBasis)
    (by rw [columnResidue_swap]; exact h1)
    (by rw [columnResidue_swap]; exact h0)
    (by rw [columnResidue_swap]; exact h2) (p.2,p.1)
  refine ⟨-z,(chains ambient 4).neg_mem hz,by rw [map_neg,hd,neg_zero],?_⟩
  rw [map_neg,hp,augmentedLine_swap,augmentedLine_swap,augmentedLine_swap,
    coordinateLine_swap,coordinateLine_swap]
  simp only [swapIndex,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  rw [simplex_swap_eq_neg, map_neg,LinearMap.neg_apply,neg_neg]

/-- Every oriented coordinate neighbor has an actual cycle realizing precisely its leading term. -/
theorem neighbor_cycle (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (e : IntegerGridExactness.Edge) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3])
          (simplex [coordinateLine g (IntegerGridExactness.edgeHead e)] -
            simplex [coordinateLine g e.1]) := by
  obtain ⟨p,j⟩ := e
  fin_cases j
  · simpa [IntegerGridExactness.edgeHead,Fin.ext_iff] using horizontal_cycle g h0 h1 h2 p
  · simpa [IntegerGridExactness.edgeHead,Fin.ext_iff]
      using vertical_cycle g h0 h1 h2 p

/-- Every finite combination of neighbor differences has a matching ambient cycle, with no
uncontrolled three-bad summands. -/
theorem exists_cycle_with_leading (g : IntegralGL) (h0 : columnResidue g 0 = 0)
    (h1 : columnResidue g 1 = 0) (h2 : columnResidue g 2 ≠ 0) (a : IntegerGridExactness.C₁) :
    ∃ z : Chain RationalLine, z ∈ chains ambient 4 ∧ boundary z = 0 ∧
      badCountProjection (fun L : RationalLine => Good L.val) 3 z =
        join (simplex [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3])
          (Finsupp.linearCombination ℚ (fun e =>
            simplex [coordinateLine g (IntegerGridExactness.edgeHead e)] -
              simplex [coordinateLine g e.1]) a) := by
  induction a using Finsupp.induction_linear with
  | zero => exact ⟨0,(chains ambient 4).zero_mem,by simp,by simp⟩
  | add a b ha hb =>
    obtain ⟨z,hz,hd,hp⟩ := ha
    obtain ⟨w,hw,he,hq⟩ := hb
    refine ⟨z+w,(chains ambient 4).add_mem hz hw,by rw [map_add,hd,he,add_zero],?_⟩
    simp only [map_add,hp,hq]
  | single e q =>
    obtain ⟨z,hz,hd,hp⟩ := neighbor_cycle g h0 h1 h2 e
    refine ⟨q • z,(chains ambient 4).smul_mem q hz,by rw [map_smul,hd,smul_zero],?_⟩
    rw [map_smul,hp,Finsupp.linearCombination_single,map_smul]

end TernaryPoly.BadTriangleNeighborCycles
