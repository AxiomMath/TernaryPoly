module

public import TernaryPeriodPolynomials.Building.AugmentedFrame.SquareCaps
public import TernaryPeriodPolynomials.Building.Coherent.PrismReduction
public import TernaryPeriodPolynomials.Building.Integer.PathJoinCycles

@[expose] public section

noncomputable section
namespace TernaryPoly.BadVertexSquareCaps
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains
open CoherentPrismReduction

local notation "residue" => AugmentedBadFaces.columnResidue
local notation "capLine" => AugmentedSquareCaps.capLine
local notation "squareCap" => AugmentedSquareCaps.squareCap

/-- Columns b, V'-U, U in the original basis, where U=X+kb and V'=εY+rb. -/
def squareMatrix (ε k r : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1,r-k,k;0,-1,1;0,ε,0]

theorem squareMatrix_det (ε k r : ℤ) : (squareMatrix ε k r).det = -ε := by
  simp [squareMatrix,Matrix.det_fin_three]

def squareChange (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) : IntegralGL :=
  Matrix.nonsingInvUnit (squareMatrix ε k r) (by rw [squareMatrix_det]; exact hε.neg)

def squareBasis (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) : IntegralGL :=
  g * squareChange ε hε k r

theorem squareBasis_column_zero (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ)
    (i : Fin 3) : (squareBasis g ε hε k r).val i 0 = g.val i 0 := by
  change (g.val * squareMatrix ε k r) i 0 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,squareMatrix]

theorem squareBasis_column_one (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ)
    (i : Fin 3) : (squareBasis g ε hε k r).val i 1 =
      g.val i 0 * (r-k) - g.val i 1 + g.val i 2 * ε := by
  change (g.val * squareMatrix ε k r) i 1 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,squareMatrix,sub_eq_add_neg]

theorem squareBasis_column_two (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ)
    (i : Fin 3) : (squareBasis g ε hε k r).val i 2 = g.val i 0 * k + g.val i 1 := by
  change (g.val * squareMatrix ε k r) i 2 = _
  simp [Matrix.mul_apply,Fin.sum_univ_three,squareMatrix]

theorem squareBasis_residue_zero (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) :
    residue (squareBasis g ε hε k r) 0 = residue g 0 := by
  simp only [AugmentedBadFaces.columnResidue,squareBasis_column_zero]

theorem squareBasis_residue_one (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) :
    residue (squareBasis g ε hε k r) 1 =
      residue g 0 * ((r-k : ℤ) : ZMod 3) - residue g 1 + residue g 2 * (ε : ZMod 3) := by
  simp only [AugmentedBadFaces.columnResidue,squareBasis_column_one,Int.cast_add,
    Int.cast_sub,Int.cast_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_mul]

theorem squareBasis_residue_two (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) :
    residue (squareBasis g ε hε k r) 2 = residue g 0 * (k : ZMod 3) + residue g 1 := by
  simp only [AugmentedBadFaces.columnResidue,squareBasis_column_two,Int.cast_add,
    Int.cast_mul,Finset.sum_add_distrib,Finset.sum_mul]

/-- Four cap corners, before passing to their actual rational lines. -/
def cornerVector (ε k r : ℤ) : Fin 4 → IntegralVector :=
  ![![k,1,0],![k+1,1,0],![r,0,ε],![r+1,0,ε]]

theorem squareChange_capVector (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) (i : Fin 4) :
    (squareChange ε hε k r).val.mulVec (AugmentedSquareCaps.capVector i.castSucc) =
      cornerVector ε k r i := by
  change (squareMatrix ε k r).mulVec (AugmentedSquareCaps.capVector i.castSucc) = _
  fin_cases i <;> funext j <;> fin_cases j <;>
    simp [squareMatrix,AugmentedSquareCaps.capVector,cornerVector,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three] <;> ring

theorem capLine_squareBasis_val (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ)
    (i : Fin 4) : (capLine (squareBasis g ε hε k r) i.castSucc).val =
      Submodule.span ℚ {rationalRepresentation g (rationalVector (cornerVector ε k r i))} := by
  change Submodule.span ℚ {(rationalRepresentation (g * squareChange ε hε k r)
    (rationalVector (AugmentedSquareCaps.capVector i.castSucc)))} = _
  rw [map_mul,LinearEquiv.mul_apply,← rationalVector_mulVec,squareChange_capVector]

theorem capLine_squareBasis_zero (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) :
    capLine (squareBasis g ε hε k r) 0 = xFiber g k := by
  apply Subtype.ext
  exact capLine_squareBasis_val g ε hε k r 0

theorem capLine_squareBasis_one (g : IntegralGL) (ε : ℤ) (hε : IsUnit ε) (k r : ℤ) :
    capLine (squareBasis g ε hε k r) 1 = xFiber g (k+1) := by
  apply Subtype.ext
  exact capLine_squareBasis_val g ε hε k r 1

theorem capLine_positive_two (g : IntegralGL) (k l : ℤ) :
    capLine (squareBasis g 1 isUnit_one k l) 2 = yFiber g l := by
  apply Subtype.ext
  exact capLine_squareBasis_val g 1 isUnit_one k l 2

theorem capLine_positive_three (g : IntegralGL) (k l : ℤ) :
    capLine (squareBasis g 1 isUnit_one k l) 3 = yFiber g (l+1) := by
  apply Subtype.ext
  exact capLine_squareBasis_val g 1 isUnit_one k l 3

private theorem span_neg (v : Space) : Submodule.span ℚ {-v} = Submodule.span ℚ {v} := by
  rw [← neg_one_smul ℚ v]
  exact Submodule.span_singleton_smul_eq (show IsUnit (-1 : ℚ) by norm_num) v

/-- Negating V+b reverses the two Y-fiber endpoints as actual rational lines. -/
theorem capLine_negative_two (g : IntegralGL) (k l : ℤ) :
    capLine (squareBasis g (-1) isUnit_neg_one k (-l-1)) 2 = yFiber g (l+1) := by
  apply Subtype.ext
  trans Submodule.span ℚ {(rationalRepresentation g
    (rationalVector (cornerVector (-1) k (-l-1) 2)))}
  · exact capLine_squareBasis_val g (-1) isUnit_neg_one k (-l-1) 2
  have hv : rationalVector (cornerVector (-1) k (-l-1) 2) =
      -rationalVector (fiberCoefficient 1 (l+1)) := by
    funext j
    fin_cases j <;> simp [rationalVector,cornerVector,fiberCoefficient]
    ring
  rw [hv,map_neg,span_neg]
  rfl

theorem capLine_negative_three (g : IntegralGL) (k l : ℤ) :
    capLine (squareBasis g (-1) isUnit_neg_one k (-l-1)) 3 = yFiber g l := by
  apply Subtype.ext
  trans Submodule.span ℚ {(rationalRepresentation g
    (rationalVector (cornerVector (-1) k (-l-1) 3)))}
  · exact capLine_squareBasis_val g (-1) isUnit_neg_one k (-l-1) 3
  have hv : rationalVector (cornerVector (-1) k (-l-1) 3) =
      -rationalVector (fiberCoefficient 1 l) := by
    funext j
    fin_cases j <;> simp [rationalVector,cornerVector,fiberCoefficient]
  rw [hv,map_neg,span_neg]
  rfl

/-- The square-cap hypotheses after an actual integral basis change. -/
theorem squareCap_basis_mem (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (ε : ℤ) (hε : IsUnit ε)
    (he : residue g 1 = residue g 2 * (ε : ZMod 3)) (k r : ℤ) :
    squareCap (squareBasis g ε hε k r) ∈ chains good 4 := by
  apply AugmentedSquareCaps.squareCap_mem_chains
  · rwa [squareBasis_residue_zero]
  · rw [squareBasis_residue_one,hb,zero_mul,zero_sub,he,neg_add_cancel]
  · simpa only [squareBasis_residue_two,hb,zero_mul,zero_add] using hX

private theorem simplex_swap_last {V : Type*} (a b c d : V) :
    simplex [a,b,d,c] = -simplex [a,b,c,d] := by
  have h := congrArg (fun t => cons a (cons b t)) (simplex_swap_eq_neg d c [])
  simpa only [cons_simplex,map_neg] using h

theorem square_cap_equal_residue (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (he : residue g 1 = residue g 2) (k l : ℤ) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧
      boundary t = boundary (simplex [xFiber g k,xFiber g (k+1),yFiber g l,yFiber g (l+1)]) := by
  refine ⟨squareCap (squareBasis g 1 isUnit_one k l),
    squareCap_basis_mem g hb hX 1 isUnit_one (by simpa using he) k l,?_⟩
  rw [AugmentedSquareCaps.squareCap_boundary]
  change boundary (simplex [capLine _ 0,capLine _ 1,capLine _ 2,capLine _ 3]) = _
  rw [capLine_squareBasis_zero,capLine_squareBasis_one,capLine_positive_two,capLine_positive_three]

/-- Opposite residues require both reversing the Y pair and negating the actual Good cap. -/
theorem square_cap_opposite_residue (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (he : residue g 1 = -residue g 2) (k l : ℤ) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧
      boundary t = boundary (simplex [xFiber g k,xFiber g (k+1),yFiber g l,yFiber g (l+1)]) := by
  refine ⟨-squareCap (squareBasis g (-1) isUnit_neg_one k (-l-1)),
    (chains good 4).neg_mem (squareCap_basis_mem g hb hX (-1) isUnit_neg_one
      (by simpa using he) k (-l-1)),?_⟩
  rw [map_neg,AugmentedSquareCaps.squareCap_boundary]
  change -boundary (simplex [capLine _ 0,capLine _ 1,capLine _ 2,capLine _ 3]) = _
  rw [capLine_squareBasis_zero,capLine_squareBasis_one,capLine_negative_two,capLine_negative_three,
    simplex_swap_last,map_neg,neg_neg]

theorem nonzero_residues_equal_or_opposite (a b : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ∨ a = -b := by
  fin_cases a <;> fin_cases b <;>
    first | exact (ha rfl).elim | exact (hb rfl).elim | exact Or.inl rfl | exact Or.inr rfl

/-- Every literal square sphere between the two Good integer fibers has an actual Good cap. -/
theorem square_cap (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0) (k l : ℤ) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧
      boundary t = boundary (simplex [xFiber g k,xFiber g (k+1),yFiber g l,yFiber g (l+1)]) := by
  rcases nonzero_residues_equal_or_opposite _ _ hX hY with he | he
  · exact square_cap_equal_residue g hb hX he k l
  · exact square_cap_opposite_residue g hb hX he k l

/-- The literal vertex map from the disjoint union of the two parameter paths. -/
def fiberMap (g : IntegralGL) : IntegerPathJoinCycles.Vertex → RationalLine :=
  Sum.elim (xFiber g) (yFiber g)

def mixed (g : IntegralGL) : IntegerGridExactness.C₁ →ₗ[ℚ] Chain RationalLine :=
  (OrientedChainMap.map (fiberMap g)).comp IntegerPathJoinCycles.mixed

theorem mapped_tetrahedron_cap (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0) (p : IntegerGridExactness.Vertex) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t =
      OrientedChainMap.map (fiberMap g) (boundary (IntegerPathJoinCycles.tetrahedron p)) := by
  obtain ⟨t,ht,hdt⟩ := square_cap g hb hX hY p.1 p.2
  refine ⟨-t,(chains good 4).neg_mem ht,?_⟩
  rw [map_neg,hdt,← OrientedChainMap.boundary_map]
  simp only [IntegerPathJoinCycles.tetrahedron,map_neg,OrientedChainMap.map_simplex,
    List.map_cons,List.map_nil,fiberMap,IntegerPathJoinCycles.left,IntegerPathJoinCycles.right,
    Sum.elim_inl,Sum.elim_inr]

/-- Every finite local mixed combination with zero cross divergence bounds in the actual
Good complex; the filling is assembled from the explicitly normalized square caps. -/
theorem mixed_cross_zero_bounds (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0) (z : IntegerGridExactness.C₁)
    (hz : IntegerPathJoinCycles.cross (boundary (IntegerPathJoinCycles.mixed z)) = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = mixed g z := by
  exact IntegerPathJoinCycles.mapped_mixed_filling (fiberMap g) (chains good 4)
    (mapped_tetrahedron_cap g hb hX hY) hz

theorem mixed_divergence_zero_bounds (g : IntegralGL) (hb : residue g 0 = 0)
    (hX : residue g 1 ≠ 0) (hY : residue g 2 ≠ 0) (z : IntegerGridExactness.C₁)
    (hz : IntegerGridExactness.boundary₁ z = 0) :
    ∃ t : Chain RationalLine, t ∈ chains good 4 ∧ boundary t = mixed g z := by
  apply mixed_cross_zero_bounds g hb hX hY z
  rwa [IntegerPathJoinCycles.cross_boundary_mixed]

end TernaryPoly.BadVertexSquareCaps
