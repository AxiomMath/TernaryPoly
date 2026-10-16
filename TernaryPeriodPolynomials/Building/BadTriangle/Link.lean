module

public import TernaryPeriodPolynomials.Building.BadEdge.LinkVertices
public import TernaryPeriodPolynomials.Building.Integer.Exactness

@[expose] public section


noncomputable section
namespace TernaryPoly.BadTriangleLink
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces GoodAugmentedNormalForm
open BadEdgeLinkVertices

/-- Actual good vertices in the ambient link of the full bad augmented core. -/
abbrev GoodTriangleLinkVertex (g : IntegralGL) :=
  {L : RationalLine // Good L.val ∧
    {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,L} ∈ ambient}

/-- An affine completion fixes the augmented sum line as well as the first two columns. -/
theorem affineCompletion_line_three (g : IntegralGL) (p : ℤ × ℤ) :
    augmentedLine (affineCompletion g p) 3 = augmentedLine g 3 := by
  have h0 : rationalRepresentation (affineCompletion g p) (Pi.single 0 1) =
      rationalRepresentation g (Pi.single 0 1) := by
    rw [rationalRepresentation_basis,rationalRepresentation_basis]
    exact congrArg rationalVector (completionMatrix_col_zero g (affineVector p))
  have h1 : rationalRepresentation (affineCompletion g p) (Pi.single 1 1) =
      rationalRepresentation g (Pi.single 1 1) := by
    rw [rationalRepresentation_basis,rationalRepresentation_basis]
    exact congrArg rationalVector (completionMatrix_col_one g (affineVector p))
  apply Subtype.ext
  change Submodule.span ℚ {rationalRepresentation (affineCompletion g p) (Pi.single 0 1 + Pi.single 1 1)} =
    Submodule.span ℚ {rationalRepresentation g (Pi.single 0 1 + Pi.single 1 1)}
  rw [map_add,map_add,h0,h1]

/-- Every affine complement completes the entire bad core to an actual augmented frame. -/
theorem coordinateLine_triangle_face (g : IntegralGL) (p : ℤ × ℤ) :
    {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,coordinateLine g p} ∈ ambient := by
  classical
  apply subset_augmentedFrame_mem (affineCompletion g p) (by simp)
  intro L hL
  simp only [Finset.mem_insert,Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,affineCompletion_line_zero g p⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,affineCompletion_line_one g p⟩
  · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,affineCompletion_line_three g p⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,affineCompletion_line_two g p⟩

/-- Downward closure takes any triangle-link vertex to a bad-edge-link vertex. -/
theorem triangle_face_implies_edge_face (g : IntegralGL) (L : RationalLine)
    (h : {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,L} ∈ ambient) :
    {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient := by
  classical
  apply (ambient.isRelLowerSet_faces h).2
  · intro M hM
    simp only [Finset.mem_insert,Finset.mem_singleton] at hM ⊢
    rcases hM with hM | hM | hM
    · exact Or.inl hM
    · exact Or.inr (Or.inl hM)
    · exact Or.inr (Or.inr (Or.inr hM))
  · simp

/-- The good link vertex predicates for the bad edge and its augmented triangle coincide. -/
theorem triangle_vertex_iff_edge_vertex (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) (L : RationalLine) :
    (Good L.val ∧ {augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,L} ∈ ambient) ↔
      (Good L.val ∧ {augmentedLine g 0,augmentedLine g 1,L} ∈ ambient) := by
  constructor
  · rintro ⟨hg,hf⟩
    exact ⟨hg,triangle_face_implies_edge_face g L hf⟩
  · rintro ⟨hg,hf⟩
    obtain ⟨p,rfl⟩ := exists_coordinates g h0 h1 L hg hf
    exact ⟨hg,coordinateLine_triangle_face g p⟩

/-- The identity on actual rational lines identifies the two good link vertex types. -/
def triangleEdgeEquiv (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    GoodTriangleLinkVertex g ≃ GoodLinkVertex g where
  toFun L := ⟨L.val,(triangle_vertex_iff_edge_vertex g h0 h1 L.val).mp L.property⟩
  invFun L := ⟨L.val,(triangle_vertex_iff_edge_vertex g h0 h1 L.val).mpr L.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete integral affine coordinates for every actual good complement of the bad triangle. -/
def coordinateEquiv (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) : (ℤ × ℤ) ≃ GoodTriangleLinkVertex g :=
  (goodLinkVertexEquiv g h0 h1 h2).trans (triangleEdgeEquiv g h0 h1).symm

@[simp] theorem coordinateEquiv_val (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    (coordinateEquiv g h0 h1 h2 p).val = coordinateLine g p := rfl

private theorem core_bad (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0) :
    ¬Good (augmentedLine g 0).val ∧ ¬Good (augmentedLine g 1).val ∧
      ¬Good (augmentedLine g 3).val := by
  simp only [good_augmentedLine_iff_residue]
  change ¬columnResidue g 0 ≠ 0 ∧ ¬columnResidue g 1 ≠ 0 ∧
    ¬(columnResidue g 0 + columnResidue g 1) ≠ 0
  simp [h0,h1]

/-- Two distinct good complements cannot form an edge in the actual bad-triangle link. -/
theorem no_link_edge (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L M : GoodTriangleLinkVertex g) (hLM : L ≠ M) :
    ¬({augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,L.val,M.val} ∈ ambient) := by
  intro hf
  obtain ⟨hb0,hb1,hb3⟩ := core_bad g h0 h1
  have hL0 : L.val ≠ augmentedLine g 0 := fun h => hb0 (h ▸ L.property.1)
  have hL1 : L.val ≠ augmentedLine g 1 := fun h => hb1 (h ▸ L.property.1)
  have hL3 : L.val ≠ augmentedLine g 3 := fun h => hb3 (h ▸ L.property.1)
  have hM0 : M.val ≠ augmentedLine g 0 := fun h => hb0 (h ▸ M.property.1)
  have hM1 : M.val ≠ augmentedLine g 1 := fun h => hb1 (h ▸ M.property.1)
  have hM3 : M.val ≠ augmentedLine g 3 := fun h => hb3 (h ▸ M.property.1)
  have hval : L.val ≠ M.val := fun h => hLM (Subtype.ext h)
  have h01 : augmentedLine g 0 ≠ augmentedLine g 1 :=
    (augmentedLine_injective g).ne (by decide)
  have h03 : augmentedLine g 0 ≠ augmentedLine g 3 :=
    (augmentedLine_injective g).ne (by decide)
  have h13 : augmentedLine g 1 ≠ augmentedLine g 3 :=
    (augmentedLine_injective g).ne (by decide)
  have hc : ({augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,L.val,M.val} :
      Finset RationalLine).card = 5 := by
    simp [h01,h03,h13,hL0,hL1,hL3,hM0,hM1,hM3,hval,ne_comm]
  have hcard := ambient_card_le_four hf
  rw [hc] at hcard
  omega

/-- Actual finite rational zero-chains of good complement vertices. -/
abbrev ComplementChains (g : IntegralGL) := GoodTriangleLinkVertex g →₀ ℚ

/-- The literal sum of all coefficients of a finite complement chain. -/
def augmentation (g : IntegralGL) : ComplementChains g →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (fun _ => (1 : ℚ))

@[simp] theorem augmentation_single (g : IntegralGL) (L : GoodTriangleLinkVertex g) (q : ℚ) :
    augmentation g (Finsupp.single L q) = q := by simp [augmentation]

theorem augmentation_eq_sum (g : IntegralGL) (c : ComplementChains g) :
    augmentation g c = c.sum (fun _ q => q) := by
  simp only [augmentation,Finsupp.linearCombination_apply,smul_eq_mul,mul_one]

/-- Coordinate transport is an actual linear equivalence on finitely supported chains. -/
def coordinateChainEquiv (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) : IntegerGridExactness.C₀ ≃ₗ[ℚ] ComplementChains g :=
  Finsupp.domLCongr (coordinateEquiv g h0 h1 h2)

@[simp] theorem coordinateChainEquiv_single (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) (q : ℚ) :
    coordinateChainEquiv g h0 h1 h2 (Finsupp.single p q) =
      Finsupp.single (coordinateEquiv g h0 h1 h2 p) q := Finsupp.domLCongr_single _ _ _

@[simp] theorem coordinateChainEquiv_symm_single (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (L : GoodTriangleLinkVertex g) (q : ℚ) :
    (coordinateChainEquiv g h0 h1 h2).symm (Finsupp.single L q) =
      Finsupp.single ((coordinateEquiv g h0 h1 h2).symm L) q := by
  apply (coordinateChainEquiv g h0 h1 h2).injective
  rw [LinearEquiv.apply_symm_apply,coordinateChainEquiv_single,Equiv.apply_symm_apply]

/-- The coordinate chain equivalence preserves the actual coefficient sum. -/
theorem augmentation_coordinateChainEquiv (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (c : IntegerGridExactness.C₀) :
    augmentation g (coordinateChainEquiv g h0 h1 h2 c) = IntegerGridExactness.augmentation c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single p q =>
    rw [coordinateChainEquiv_single,augmentation_single,IntegerGridExactness.augmentation_single]

/-- Coordinate-neighbor differences, regarded as actual complement zero-chains. -/
def neighborDifference (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (e : IntegerGridExactness.Edge) : ComplementChains g :=
  Finsupp.single (coordinateEquiv g h0 h1 h2 (IntegerGridExactness.edgeHead e)) 1 -
    Finsupp.single (coordinateEquiv g h0 h1 h2 e.1) 1

/-- The horizontal neighbor has coordinate difference (1,0). -/
theorem neighborDifference_horizontal (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    neighborDifference g h0 h1 h2 (p,0) =
      Finsupp.single (coordinateEquiv g h0 h1 h2 (p.1+1,p.2)) 1 -
      Finsupp.single (coordinateEquiv g h0 h1 h2 p) 1 := rfl

/-- The vertical neighbor has coordinate difference (0,1). -/
theorem neighborDifference_vertical (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) :
    neighborDifference g h0 h1 h2 (p,1) =
      Finsupp.single (coordinateEquiv g h0 h1 h2 (p.1,p.2+1)) 1 -
      Finsupp.single (coordinateEquiv g h0 h1 h2 p) 1 := rfl

/-- Finite linear combinations of the two types of coordinate-neighbor differences. -/
def neighborCombination (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) : IntegerGridExactness.C₁ →ₗ[ℚ] ComplementChains g :=
  Finsupp.linearCombination ℚ (neighborDifference g h0 h1 h2)

@[simp] theorem neighborCombination_single (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (e : IntegerGridExactness.Edge) (q : ℚ) :
    neighborCombination g h0 h1 h2 (Finsupp.single e q) =
      q • neighborDifference g h0 h1 h2 e := Finsupp.linearCombination_single ℚ q e

/-- The grid boundary transports exactly to the displayed neighbor differences. -/
theorem neighborCombination_apply (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (c : IntegerGridExactness.C₁) :
    neighborCombination g h0 h1 h2 c =
      coordinateChainEquiv g h0 h1 h2 (IntegerGridExactness.boundary₁ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single e q =>
    simp only [neighborCombination_single,neighborDifference,IntegerGridExactness.boundary₁_single,
      map_smul,map_sub,IntegerGridExactness.vertex,coordinateChainEquiv_single]

/-- Every augmentation-zero complement chain is a finite combination of coordinate-neighbor differences. -/
theorem ker_augmentation_eq_range_neighbors (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) :
    LinearMap.ker (augmentation g) = LinearMap.range (neighborCombination g h0 h1 h2) := by
  ext c
  constructor
  · intro hc
    let z := (coordinateChainEquiv g h0 h1 h2).symm c
    have hz : IntegerGridExactness.augmentation z = 0 := by
      rw [← augmentation_coordinateChainEquiv g h0 h1 h2]
      change augmentation g ((coordinateChainEquiv g h0 h1 h2)
        ((coordinateChainEquiv g h0 h1 h2).symm c)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact LinearMap.mem_ker.mp hc
    refine ⟨IntegerGridExactness.pathLinear z,?_⟩
    rw [neighborCombination_apply,IntegerGridExactness.boundary₁_pathLinear,hz,zero_smul,sub_zero]
    exact (coordinateChainEquiv g h0 h1 h2).apply_symm_apply c
  · rintro ⟨c,rfl⟩
    change augmentation g (neighborCombination g h0 h1 h2 c) = 0
    rw [neighborCombination_apply,augmentation_coordinateChainEquiv]
    exact IntegerGridExactness.augmentation_boundary₁ c

/-- The complete reduced H0 generating statement for the discrete bad-triangle complement lattice. -/
theorem ker_augmentation_eq_span_neighbors (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) :
    LinearMap.ker (augmentation g) =
      Submodule.span ℚ (Set.range (neighborDifference g h0 h1 h2)) := by
  exact (ker_augmentation_eq_range_neighbors g h0 h1 h2).trans
    (Finsupp.range_linearCombination ℚ (v := neighborDifference g h0 h1 h2))

/-- Forgetting the link proof gives an actual finite chain of rational line vertices. -/
def lineChains (g : IntegralGL) : ComplementChains g →ₗ[ℚ] (RationalLine →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun L : GoodTriangleLinkVertex g => L.val)

/-- Coordinate basis chains map to the literal affine rational lines. -/
theorem lineChains_coordinate_single (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) (p : ℤ × ℤ) (q : ℚ) :
    lineChains g (Finsupp.single (coordinateEquiv g h0 h1 h2 p) q) =
      Finsupp.single (coordinateLine g p) q := by
  simp [lineChains,Finsupp.lmapDomain_apply]

end TernaryPoly.BadTriangleLink
