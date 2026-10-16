module

public import TernaryPeriodPolynomials.Building.BadEdge.LinkVertices
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

open scoped BigOperators
noncomputable section
namespace TernaryPoly.BadEdgeLinkGrid
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces
open AmbientIndependentTriple BadEdgeLinkVertices

/-- Matrix with the indicated ordered integral vector columns. -/
def columns (v : Fin 3 → IntegralVector) : IntegralMatrix := fun i j => v j i

/-- Determinant of an ordered triple selected from four actual vectors. -/
def tripleDet (v : Fin 4 → IntegralVector) (i j k : Fin 4) : ℤ :=
  (columns ![v i,v j,v k]).det

/-- Every four choices from the literal augmented template contain a singular triple. -/
theorem template_four_singular (idx : Fin 4 → Fin 4) :
    (templateMatrix ![idx 0,idx 1,idx 2]).det = 0 ∨
    (templateMatrix ![idx 0,idx 1,idx 3]).det = 0 ∨
    (templateMatrix ![idx 0,idx 2,idx 3]).det = 0 ∨
    (templateMatrix ![idx 1,idx 2,idx 3]).det = 0 := by
  exact (by decide +kernel : ∀ a b c d : Fin 4,
    (templateMatrix ![a,b,c]).det = 0 ∨ (templateMatrix ![a,b,d]).det = 0 ∨
    (templateMatrix ![a,c,d]).det = 0 ∨ (templateMatrix ![b,c,d]).det = 0)
      (idx 0) (idx 1) (idx 2) (idx 3)

/-- Four primitive generators on an actual ambient face have a singular triple. -/
theorem four_singular_of_ambient (v : Fin 4 → IntegralVector)
    (hp : ∀ i, Primitive (v i)) (L : Fin 4 → RationalLine)
    (hL : ∀ i, Submodule.span ℚ {rationalVector (v i)} = (L i).val)
    (hface : Finset.univ.image L ∈ ambient) :
    tripleDet v 0 1 2 = 0 ∨ tripleDet v 0 1 3 = 0 ∨
      tripleDet v 0 2 3 = 0 ∨ tripleDet v 1 2 3 = 0 := by
  classical
  obtain ⟨_,g,hg⟩ := hface
  have hi (j : Fin 4) : ∃ i : Fin 4, augmentedLine g i = L j := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hg (Finset.mem_image.mpr
      ⟨j,Finset.mem_univ _,rfl⟩))
    exact ⟨i,hi⟩
  choose idx hidx using hi
  have hu (j : Fin 4) : ∃ u : ℤˣ,
      v j = (u : ℤ) • g.val.mulVec (integralTemplate (idx j)) := by
    apply primitive_eq_unit_template g (idx j) (hp j)
    rw [hL,hidx]
  choose u hu using hu
  have hz (i j k : Fin 4) (ht : (templateMatrix ![idx i,idx j,idx k]).det = 0) :
      tripleDet v i j k = 0 := by
    let sel : Fin 3 → Fin 4 := ![i,j,k]
    have he : columns ![v i,v j,v k] =
        g.val * templateMatrix ![idx i,idx j,idx k] *
          Matrix.diagonal (fun t => (u (sel t) : ℤ)) := by
      ext r t
      have hv : (![v i,v j,v k] : Fin 3 → IntegralVector) t = v (sel t) := by
        fin_cases t <;> rfl
      have ht : (![idx i,idx j,idx k] : Fin 3 → Fin 4) t = idx (sel t) := by
        fin_cases t <;> rfl
      change (![v i,v j,v k] : Fin 3 → IntegralVector) t r = _
      rw [hv,hu,Matrix.mul_diagonal]
      change (u (sel t) : ℤ) * (g.val.mulVec (integralTemplate (idx (sel t)))) r =
        (g.val * templateMatrix ![idx i,idx j,idx k]) r t * (u (sel t) : ℤ)
      rw [mul_comm]
      congr 1
      simp only [Matrix.mul_apply,templateMatrix,ht,Matrix.mulVec,dotProduct]
    rw [tripleDet,he,Matrix.det_mul,Matrix.det_mul,ht,mul_zero,zero_mul]
  rcases template_four_singular idx with h | h | h | h
  · exact Or.inl (hz 0 1 2 h)
  · exact Or.inr (Or.inl (hz 0 1 3 h))
  · exact Or.inr (Or.inr (Or.inl (hz 0 2 3 h)))
  · exact Or.inr (Or.inr (Or.inr (hz 1 2 3 h)))

/-- Four integral generators of the two fixed basis lines and two affine vertices. -/
def edgeVectors (g : IntegralGL) (p q : ℤ × ℤ) : Fin 4 → IntegralVector :=
  ![g.val.col 0,g.val.col 1,g.val.mulVec (affineVector p),g.val.mulVec (affineVector q)]

def edgeLines (g : IntegralGL) (p q : ℤ × ℤ) : Fin 4 → RationalLine :=
  ![augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q]

theorem edgeVectors_primitive (g : IntegralGL) (p q : ℤ × ℤ) (i : Fin 4) :
    Primitive (edgeVectors g p q i) := by
  fin_cases i
  · exact basis_column_primitive g 0
  · exact basis_column_primitive g 1
  · exact primitive_mulVec g (affineVector_primitive p)
  · exact primitive_mulVec g (affineVector_primitive q)

theorem edgeVectors_span (g : IntegralGL) (p q : ℤ × ℤ) (i : Fin 4) :
    Submodule.span ℚ {rationalVector (edgeVectors g p q i)} = (edgeLines g p q i).val := by
  fin_cases i
  · change _ = Submodule.span ℚ {rationalRepresentation g (Pi.single 0 1)}
    rw [rationalRepresentation_basis]
    rfl
  · change _ = Submodule.span ℚ {rationalRepresentation g (Pi.single 1 1)}
    rw [rationalRepresentation_basis]
    rfl
  · rfl
  · rfl

theorem edgeLines_image (g : IntegralGL) (p q : ℤ × ℤ) :
    Finset.univ.image (edgeLines g p q) =
      {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} := by
  classical
  rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]
  simp [edgeLines]

/-- Actual vector-column matrices commute with multiplication by the actual basis matrix. -/
theorem columns_mulVec (g : IntegralGL) (v : Fin 3 → IntegralVector) :
    columns (fun j => g.val.mulVec (v j)) = g.val * columns v := rfl

private theorem edgeVectors_eq (g : IntegralGL) (p q : ℤ × ℤ) :
    edgeVectors g p q = fun j =>
      g.val.mulVec ((![Pi.single 0 1,Pi.single 1 1,affineVector p,affineVector q] :
        Fin 4 → IntegralVector) j) := by
  funext j
  fin_cases j <;> simp [edgeVectors]

/-- The first two triples are bases; the other two detect the two coordinate differences. -/
theorem edge_triple_dets (g : IntegralGL) (p q : ℤ × ℤ) :
    tripleDet (edgeVectors g p q) 0 1 2 = g.val.det ∧
    tripleDet (edgeVectors g p q) 0 1 3 = g.val.det ∧
    tripleDet (edgeVectors g p q) 0 2 3 = g.val.det * (p.2-q.2) ∧
    tripleDet (edgeVectors g p q) 1 2 3 = g.val.det * (q.1-p.1) := by
  have h (i j k : Fin 4) : tripleDet (edgeVectors g p q) i j k =
      g.val.det * (columns ![
        (![Pi.single 0 1,Pi.single 1 1,affineVector p,affineVector q] : Fin 4 → IntegralVector) i,
        (![Pi.single 0 1,Pi.single 1 1,affineVector p,affineVector q] : Fin 4 → IntegralVector) j,
        (![Pi.single 0 1,Pi.single 1 1,affineVector p,affineVector q] : Fin 4 → IntegralVector) k]).det := by
    rw [tripleDet,edgeVectors_eq]
    have he (a b c : IntegralVector) :
        (![g.val.mulVec a,g.val.mulVec b,g.val.mulVec c] : Fin 3 → IntegralVector) =
          fun t => g.val.mulVec ((![a,b,c] : Fin 3 → IntegralVector) t) := by
      funext t
      fin_cases t <;> rfl
    rw [he,columns_mulVec,Matrix.det_mul]
  simp only [h]
  simp [columns,affineVector,Matrix.det_fin_three,sub_eq_add_neg,add_comm]

/-- A four-line ambient face forces one affine coordinate to agree. -/
theorem face_forces_coordinate_equal (g : IntegralGL) (p q : ℤ × ℤ)
    (hf : {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient) :
    p.1 = q.1 ∨ p.2 = q.2 := by
  have h := four_singular_of_ambient (edgeVectors g p q) (edgeVectors_primitive g p q)
    (edgeLines g p q) (edgeVectors_span g p q) (by rwa [edgeLines_image])
  obtain ⟨h0,h1,h2,h3⟩ := edge_triple_dets g p q
  rw [h0,h1,h2,h3] at h
  rcases h with h | h | h | h
  · exact (g.det_ne_zero h).elim
  · exact (g.det_ne_zero h).elim
  · exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left g.det_ne_zero))
  · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left g.det_ne_zero)).symm

/-- Any nonsingular triple selected from a primitive ambient face is unimodular. -/
theorem triple_unimodular_of_ambient (v : Fin 4 → IntegralVector)
    (hp : ∀ i, Primitive (v i)) (L : Fin 4 → RationalLine)
    (hL : ∀ i, Submodule.span ℚ {rationalVector (v i)} = (L i).val)
    (hface : Finset.univ.image L ∈ ambient) (i j k : Fin 4)
    (hd : tripleDet v i j k ≠ 0) : (tripleDet v i j k).natAbs = 1 := by
  classical
  have hprim (t : Fin 3) : Primitive ((columns ![v i,v j,v k]).col t) := by
    fin_cases t
    · exact hp i
    · exact hp j
    · exact hp k
  have hlines (t : Fin 3) : Submodule.span ℚ
      {rationalVector ((columns ![v i,v j,v k]).col t)} =
      ((![L i,L j,L k] : Fin 3 → RationalLine) t).val := by
    fin_cases t
    · exact hL i
    · exact hL j
    · exact hL k
  apply det_natAbs_eq_one_of_ambient (columns ![v i,v j,v k]) hprim hd
    ![L i,L j,L k] hlines
  obtain ⟨_,g,hg⟩ := hface
  apply subset_augmentedFrame_mem g (Finset.image_nonempty.mpr Finset.univ_nonempty)
  intro A hA
  rw [image_three] at hA
  simp only [Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl
  · exact hg (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  · exact hg (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · exact hg (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

/-- Literal nearest-neighbor adjacency on the integer coordinate plane. -/
def GridAdjacent (p q : ℤ × ℤ) : Prop :=
  (p.2 = q.2 ∧ (p.1-q.1).natAbs = 1) ∨
  (p.1 = q.1 ∧ (p.2-q.2).natAbs = 1)

/-- The complete ambient-face condition forces unit distance along the one changing coordinate. -/
theorem gridAdjacent_of_face (g : IntegralGL) (p q : ℤ × ℤ) (hpq : p ≠ q)
    (hf : {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient) :
    GridAdjacent p q := by
  have hun (i j k : Fin 4) (hd : tripleDet (edgeVectors g p q) i j k ≠ 0) :
      (tripleDet (edgeVectors g p q) i j k).natAbs = 1 :=
    triple_unimodular_of_ambient (edgeVectors g p q) (edgeVectors_primitive g p q)
      (edgeLines g p q) (edgeVectors_span g p q) (by rwa [edgeLines_image]) i j k hd
  have hgdet : g.val.det.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp
    ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit)
  obtain ⟨_,_,h2,h3⟩ := edge_triple_dets g p q
  rcases face_forces_coordinate_equal g p q hf with he | he
  · have hne : p.2-q.2 ≠ 0 := by
      intro hz
      exact hpq (Prod.ext he (sub_eq_zero.mp hz))
    have hd := hun 0 2 3 (by rw [h2]; exact mul_ne_zero g.det_ne_zero hne)
    rw [h2,Int.natAbs_mul,hgdet,one_mul] at hd
    exact Or.inr ⟨he,hd⟩
  · have hne : q.1-p.1 ≠ 0 := by
      intro hz
      exact hpq (Prod.ext (sub_eq_zero.mp hz).symm he)
    have hd := hun 1 2 3 (by rw [h3]; exact mul_ne_zero g.det_ne_zero hne)
    rw [h3,Int.natAbs_mul,hgdet,one_mul] at hd
    refine Or.inl ⟨he,?_⟩
    rw [show p.1-q.1 = -(q.1-p.1) by ring,Int.natAbs_neg,hd]

/-- A unit column matrix realizes its three generator lines and their first sum as an actual frame. -/
theorem face_of_unit_columns (v : Fin 3 → IntegralVector)
    (hu : IsUnit (columns v).det) (L : Fin 4 → RationalLine)
    (h0 : Submodule.span ℚ {rationalVector (v 0)} = (L 0).val)
    (h1 : Submodule.span ℚ {rationalVector (v 1)} = (L 1).val)
    (h2 : Submodule.span ℚ {rationalVector (v 2)} = (L 2).val)
    (h3 : Submodule.span ℚ {rationalVector (v 0 + v 1)} = (L 3).val) :
    {L 0,L 1,L 2,L 3} ∈ ambient := by
  classical
  let h : IntegralGL := Matrix.nonsingInvUnit (columns v) hu
  have he (i : Fin 4) : augmentedLine h i = L i := by
    apply Subtype.ext
    change Submodule.span ℚ {rationalRepresentation h (template i)} = (L i).val
    rw [← rationalVector_integralTemplate i,← rationalVector_mulVec]
    fin_cases i
    · change Submodule.span ℚ {rationalVector ((columns v).mulVec (Pi.single 0 1))} = _
      rw [Matrix.mulVec_single_one]
      exact h0
    · change Submodule.span ℚ {rationalVector ((columns v).mulVec (Pi.single 1 1))} = _
      rw [Matrix.mulVec_single_one]
      exact h1
    · change Submodule.span ℚ {rationalVector ((columns v).mulVec (Pi.single 2 1))} = _
      rw [Matrix.mulVec_single_one]
      exact h2
    · change Submodule.span ℚ
        {rationalVector ((columns v).mulVec (Pi.single 0 1 + Pi.single 1 1))} = _
      rw [Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
      exact h3
  apply subset_augmentedFrame_mem h (by simp)
  intro A hA
  simp only [Finset.mem_insert,Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,he 0⟩
  · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,he 1⟩
  · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,he 2⟩
  · exact Finset.mem_image.mpr ⟨3,Finset.mem_univ _,he 3⟩

/-- An integral unit rescaling preserves an actual rational basis-column line. -/
theorem scaled_basis_span (g : IntegralGL) (j : Fin 3) (s : ℤ) (hs : IsUnit s) :
    Submodule.span ℚ {rationalVector (g.val.mulVec (s • Pi.single j 1))} =
      (augmentedLine g j.castSucc).val := by
  rw [Matrix.mulVec_smul]
  have he (v : IntegralVector) : rationalVector (s • v) = (s : ℚ) • rationalVector v := by
    ext i
    simp [rationalVector]
  rw [he,Submodule.span_singleton_smul_eq
    (show IsUnit (s : ℚ) from hs.map (Int.castRingHom ℚ)),
    Matrix.mulVec_single_one,augmentedLine_castSucc_val,rationalRepresentation_basis]
  rfl

/-- Any signed unit step along either fixed basis vector is realized by an actual augmented frame. -/
theorem face_of_signed_step (g : IntegralGL) (p q : ℤ × ℤ) (j : Fin 2) (s : ℤ)
    (hs : IsUnit s)
    (hq : affineVector q = s • Pi.single j.castSucc 1 + affineVector p) :
    {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient := by
  let w : Fin 3 → IntegralVector :=
    ![s • Pi.single j.castSucc 1,affineVector p,Pi.single j.rev.castSucc 1]
  have hw : IsUnit (columns w).det := by
    fin_cases j
    · simpa [w,columns,affineVector,Matrix.det_fin_three] using hs.neg
    · simpa [w,columns,affineVector,Matrix.det_fin_three] using hs
  let v : Fin 3 → IntegralVector := fun t => g.val.mulVec (w t)
  have hv : IsUnit (columns v).det := by
    change IsUnit (columns (fun t => g.val.mulVec (w t))).det
    rw [columns_mulVec,Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit).mul hw
  let L : Fin 4 → RationalLine :=
    ![augmentedLine g j.castSucc.castSucc,coordinateLine g p,
      augmentedLine g j.rev.castSucc.castSucc,coordinateLine g q]
  have hf : {L 0,L 1,L 2,L 3} ∈ ambient := by
    apply face_of_unit_columns v hv L
    · exact scaled_basis_span g j.castSucc s hs
    · rfl
    · simpa only [v,w,L,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,one_smul] using
        scaled_basis_span g j.rev.castSucc 1 isUnit_one
    · change Submodule.span ℚ {(rationalVector
        (g.val.mulVec (s • Pi.single j.castSucc 1) + g.val.mulVec (affineVector p)))} = _
      rw [← Matrix.mulVec_add,← hq]
      rfl
  have hset : ({L 0,L 1,L 2,L 3} : Finset RationalLine) =
      {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} := by
    fin_cases j <;> ext A <;> simp [L] <;> aesop
  rwa [hset] at hf

/-- Every literal integer nearest-neighbor pair yields the required actual four-line face. -/
theorem face_of_gridAdjacent (g : IntegralGL) (p q : ℤ × ℤ) (h : GridAdjacent p q) :
    {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient := by
  rcases h with ⟨he,hd⟩ | ⟨he,hd⟩
  · have hs : IsUnit (q.1-p.1) := by
      apply Int.isUnit_iff_natAbs_eq.mpr
      rw [show q.1-p.1 = -(p.1-q.1) by ring,Int.natAbs_neg,hd]
    apply face_of_signed_step g p q 0 (q.1-p.1) hs
    ext i
    fin_cases i <;> simp [affineVector,he]
  · have hs : IsUnit (q.2-p.2) := by
      apply Int.isUnit_iff_natAbs_eq.mpr
      rw [show q.2-p.2 = -(p.2-q.2) by ring,Int.natAbs_neg,hd]
    apply face_of_signed_step g p q 1 (q.2-p.2) hs
    ext i
    fin_cases i <;> simp [affineVector,he]

theorem GridAdjacent.ne {p q : ℤ × ℤ} (h : GridAdjacent p q) : p ≠ q := by
  rintro rfl
  simp [GridAdjacent] at h

/-- The actual four-line face relation is exactly integer nearest-neighbor adjacency. -/
theorem face_iff_gridAdjacent (g : IntegralGL) (p q : ℤ × ℤ) :
    (p ≠ q ∧ {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient) ↔
      GridAdjacent p q :=
  ⟨fun h => gridAdjacent_of_face g p q h.1 h.2,
    fun h => ⟨h.ne,face_of_gridAdjacent g p q h⟩⟩

theorem GridAdjacent.symm {p q : ℤ × ℤ} (h : GridAdjacent p q) : GridAdjacent q p := by
  rcases h with ⟨he,hd⟩ | ⟨he,hd⟩
  · refine Or.inl ⟨he.symm,?_⟩
    rw [show q.1-p.1 = -(p.1-q.1) by ring,Int.natAbs_neg,hd]
  · refine Or.inr ⟨he.symm,?_⟩
    rw [show q.2-p.2 = -(p.2-q.2) by ring,Int.natAbs_neg,hd]

/-- The ordinary nearest-neighbor simple graph on the full infinite integer plane. -/
def gridGraph : SimpleGraph (ℤ × ℤ) where
  Adj := GridAdjacent
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.ne rfl⟩

/-- The genuine graph of Good vertices and actual ambient edges in the fixed-edge link. -/
def goodLinkGraph (g : IntegralGL) : SimpleGraph (GoodLinkVertex g) where
  Adj L M := L ≠ M ∧ {augmentedLine g 0,augmentedLine g 1,L.val,M.val} ∈ ambient
  symm := ⟨fun L M h => by
    refine ⟨h.1.symm,?_⟩
    have he : ({augmentedLine g 0,augmentedLine g 1,M.val,L.val} : Finset RationalLine) =
        {augmentedLine g 0,augmentedLine g 1,L.val,M.val} := by
      ext A
      simp [or_comm,or_left_comm]
    rw [he]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The exhaustive vertex coordinates identify actual link edges with the integer grid edges. -/
def goodLinkGraphIso (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (h2 : columnResidue g 2 ≠ 0) : gridGraph ≃g goodLinkGraph g where
  toEquiv := goodLinkVertexEquiv g h0 h1 h2
  map_rel_iff' := by
    intro p q
    change ((goodLinkVertexEquiv g h0 h1 h2 p ≠ goodLinkVertexEquiv g h0 h1 h2 q) ∧
      {augmentedLine g 0,augmentedLine g 1,coordinateLine g p,coordinateLine g q} ∈ ambient) ↔
        GridAdjacent p q
    constructor
    · intro h
      exact gridAdjacent_of_face g p q (fun he => h.1 (congrArg _ he)) h.2
    · intro h
      exact ⟨fun he => h.ne ((goodLinkVertexEquiv g h0 h1 h2).injective he),
        face_of_gridAdjacent g p q h⟩

/-- A Good link vertex is distinct from either of the two fixed bad basis lines. -/
theorem goodLinkVertex_ne_bad (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L : GoodLinkVertex g) : augmentedLine g 0 ≠ L.val ∧ augmentedLine g 1 ≠ L.val := by
  have hb0 : ¬ Good (augmentedLine g 0).val := by
    rw [good_augmentedLine_iff_residue]
    exact fun h => h h0
  have hb1 : ¬ Good (augmentedLine g 1).val := by
    rw [good_augmentedLine_iff_residue]
    exact fun h => h h1
  exact ⟨fun he => hb0 (he.symm ▸ L.property.1),fun he => hb1 (he.symm ▸ L.property.1)⟩

/-- There are no actual link 2-simplices: three distinct Good vertices would give five ambient vertices. -/
theorem no_good_link_triangle (g : IntegralGL)
    (h0 : columnResidue g 0 = 0) (h1 : columnResidue g 1 = 0)
    (L M N : GoodLinkVertex g) (hLM : L ≠ M) (hLN : L ≠ N) (hMN : M ≠ N) :
    {augmentedLine g 0,augmentedLine g 1,L.val,M.val,N.val} ∉ ambient := by
  classical
  intro hf
  have hbc : augmentedLine g 0 ≠ augmentedLine g 1 :=
    fun he => (by decide : (0 : Fin 4) ≠ 1) (augmentedLine_injective g he)
  obtain ⟨hbL,hcL⟩ := goodLinkVertex_ne_bad g h0 h1 L
  obtain ⟨hbM,hcM⟩ := goodLinkVertex_ne_bad g h0 h1 M
  obtain ⟨hbN,hcN⟩ := goodLinkVertex_ne_bad g h0 h1 N
  have hLM' : L.val ≠ M.val := fun he => hLM (Subtype.ext he)
  have hLN' : L.val ≠ N.val := fun he => hLN (Subtype.ext he)
  have hMN' : M.val ≠ N.val := fun he => hMN (Subtype.ext he)
  have hc : ({augmentedLine g 0,augmentedLine g 1,L.val,M.val,N.val} : Finset RationalLine).card = 5 := by
    simp [hbc,hbL,hbM,hbN,hcL,hcM,hcN,hLM',hLN',hMN']
  have hl := ambient_card_le_four hf
  rw [hc] at hl
  omega

end TernaryPoly.BadEdgeLinkGrid
