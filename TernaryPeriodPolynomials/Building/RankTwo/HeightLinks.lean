module

public import TernaryPeriodPolynomials.Building.RankTwo.VertexLinks
public import Mathlib.Data.Int.DivMod

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoHeightLinks
open RankTwoAugmentedFrames RankTwoVertexLinks OrientedListChains OrientedChainJoin

local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- A chosen primitive vector for every actual rational rank-two line. -/
def primitiveGenerator (L : RationalLine2) : IntegralVector :=
  (rationalLine_primitive_generator L).choose

theorem primitiveGenerator_primitive (L : RationalLine2) : Primitive (primitiveGenerator L) :=
  (rationalLine_primitive_generator L).choose_spec.1

theorem primitiveGenerator_span (L : RationalLine2) :
    Submodule.span ℚ {rationalVector (primitiveGenerator L)} = L.val :=
  (rationalLine_primitive_generator L).choose_spec.2.2

/-- Primitive last-coordinate height, independent of the choice of generator. -/
def height (L : RationalLine2) : ℕ := (primitiveGenerator L 1).natAbs

theorem height_eq_natAbs (L : RationalLine2) {v : IntegralVector} (hv : Primitive v)
    (hs : Submodule.span ℚ {rationalVector v} = L.val) : height L = (v 1).natAbs := by
  rcases primitive_eq_or_neg_of_span_eq (primitiveGenerator_primitive L) hv
    ((primitiveGenerator_span L).trans hs.symm) with he | he
  · simp only [height,he]
  · simp only [height,he,Pi.neg_apply,Int.natAbs_neg]

theorem primitive_of_bezout {v : IntegralVector} {a b : ℤ}
    (hb : v 0 * a + v 1 * b = 1) : Primitive v := by
  have hd : (content v : ℤ) ∣ 1 := by
    rw [← hb]
    exact dvd_add (dvd_mul_of_dvd_left (content_dvd v 0) a)
      (dvd_mul_of_dvd_left (content_dvd v 1) b)
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hd)

/-- Every actual unimodular column is primitive. -/
theorem column_primitive (g : IntegralGL) (j : Fin 2) : Primitive (g.val.col j) := by
  apply primitive_of_bezout (a := g⁻¹.val j 0) (b := g⁻¹.val j 1)
  have he : g⁻¹.val * g.val = 1 := by
    rw [← Units.val_mul,inv_mul_cancel,Units.val_one]
  have hc := congrFun (congrFun he j) j
  simpa [Matrix.mul_apply,Fin.sum_univ_two,mul_comm] using hc

/-- Literal last-coordinate height of the first basis line. -/
theorem height_first (g : IntegralGL) : height (augmentedLine g 0) = (g.val 1 0).natAbs := by
  apply height_eq_natAbs _ (column_primitive g 0)
  change _ = Submodule.span ℚ {rationalRepresentation g (template 0)}
  have he := representation_column g (0 : Fin 2)
  change rationalRepresentation g (template 0) = rationalVector (g.val.col 0) at he
  rw [he]

theorem coordinateVector_primitive (g : IntegralGL) (k : ℤ) :
    Primitive (g.val.mulVec (coordinateVector k)) := by
  have he : g.val.mulVec (coordinateVector k) = (g * neighborBasis k).val.col 0 := by
    funext i
    change g.val.mulVec (coordinateVector k) i = (g.val * neighborMatrix k) i 0
    simp [coordinateVector,neighborMatrix,Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_two]
  rw [he]
  exact column_primitive _ _

/-- Actual affine fiber height, with no choice or sign ambiguity. -/
theorem height_coordinateLine (g : IntegralGL) (k : ℤ) :
    height (coordinateLine g k) = (g.val 1 1 + k * g.val 1 0).natAbs := by
  have he := height_eq_natAbs (coordinateLine g k) (coordinateVector_primitive g k)
    (by rw [rationalVector_mulVec]; rfl)
  rw [he]
  congr 1
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,coordinateVector,mul_comm,add_comm]

/-- Euclidean division gives a strictly lower affine coordinate for every nonzero direction. -/
theorem exists_low_index (a b : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, (b+k*a).natAbs < a.natAbs := by
  refine ⟨-(b/a),?_⟩
  have he : b + -(b/a)*a = b % a := by
    have hd := Int.emod_add_ediv_mul b a
    nlinarith only [hd]
  rw [he]
  have hh : ((b%a).natAbs : ℤ) < (a.natAbs : ℤ) := by
    rw [Int.natCast_natAbs,Int.natCast_natAbs,abs_of_nonneg (Int.emod_nonneg b ha)]
    exact Int.emod_lt_abs b ha
  exact_mod_cast hh

/-- Two strict lower coordinates are equal or adjacent in the actual integer path. -/
theorem low_indices_adjacent (a b k l : ℤ)
    (hk : (b+k*a).natAbs < a.natAbs) (hl : (b+l*a).natAbs < a.natAbs) :
    k = l ∨ (k-l).natAbs = 1 := by
  have hd : ((b+k*a)-(b+l*a)).natAbs < 2*a.natAbs :=
    (Int.natAbs_sub_le _ _).trans_lt (by omega)
  have he : (b+k*a)-(b+l*a) = (k-l)*a := by ring
  rw [he,Int.natAbs_mul] at hd
  have hs : (k-l).natAbs < 2 := Nat.lt_of_mul_lt_mul_right hd
  by_cases hkl : k = l
  · exact Or.inl hkl
  · right
    have hn : (k-l).natAbs ≠ 0 := by
      intro hz
      exact hkl (sub_eq_zero.mp (Int.natAbs_eq_zero.mp hz))
    omega

/-- The full strictly lower subcomplex of the actual vertex link. -/
def lowLink (g : IntegralGL) : PreAbstractSimplicialComplex RationalLine2 where
  faces := {s | s ∈ vertexLink g ∧ ∀ L ∈ s, height L < height (augmentedLine g 0)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨((vertexLink g).isRelLowerSet_faces hs.1).1,?_⟩
    intro t hts ht
    exact ⟨((vertexLink g).isRelLowerSet_faces hs.1).2 hts ht,
      fun L hL => hs.2 L (hts hL)⟩

@[simp] theorem mem_lowLink (g : IntegralGL) (s : Finset RationalLine2) :
    s ∈ lowLink g ↔ s ∈ vertexLink g ∧ ∀ L ∈ s, height L < height (augmentedLine g 0) := Iff.rfl

theorem coordinate_low_iff (g : IntegralGL) (k : ℤ) :
    {coordinateLine g k} ∈ lowLink g ↔
      (g.val 1 1 + k*g.val 1 0).natAbs < (g.val 1 0).natAbs := by
  rw [mem_lowLink]
  simp only [coordinate_mem_link,true_and,Finset.mem_singleton,forall_eq,
    height_coordinateLine,height_first]

/-- The lower actual vertex link is nonempty whenever the base has positive height. -/
theorem lowLink_nonempty (g : IntegralGL) (hg : 0 < height (augmentedLine g 0)) :
    ∃ L : RationalLine2, {L} ∈ lowLink g := by
  have ha : g.val 1 0 ≠ 0 := by
    intro he
    rw [height_first,he] at hg
    simp at hg
  obtain ⟨k,hk⟩ := exists_low_index (g.val 1 0) (g.val 1 1) ha
  exact ⟨coordinateLine g k,(coordinate_low_iff g k).mpr hk⟩

/-- Every low-link vertex retains its unique actual integer affine coordinate. -/
theorem low_exists_coordinate (g : IntegralGL) (L : RationalLine2) (hL : {L} ∈ lowLink g) :
    ∃ k : ℤ, coordinateLine g k = L ∧
      (g.val 1 1+k*g.val 1 0).natAbs < (g.val 1 0).natAbs := by
  obtain ⟨k,hk⟩ := exists_coordinate g L hL.1
  exact ⟨k,hk,(coordinate_low_iff g k).mp (hk ▸ hL)⟩

/-- Any two distinct low vertices are connected by an actual low-link edge. -/
theorem low_pair_mem (g : IntegralGL) (L M : RationalLine2)
    (hL : {L} ∈ lowLink g) (hM : {M} ∈ lowLink g) : {L,M} ∈ lowLink g := by
  obtain ⟨k,rfl,hk⟩ := low_exists_coordinate g L hL
  obtain ⟨l,rfl,hl⟩ := low_exists_coordinate g M hM
  refine ⟨?_,?_⟩
  · rcases low_indices_adjacent (g.val 1 0) (g.val 1 1) k l hk hl with he | he
    · subst l
      simpa using coordinate_mem_link g k
    · apply (pair_mem_link_iff_natAbs g k l (by intro hh; simp [hh] at he)).mpr he
  · intro A hA
    simp only [Finset.mem_insert,Finset.mem_singleton] at hA
    rcases hA with rfl | rfl
    · exact hL.2 _ (Finset.mem_singleton_self _)
    · exact hM.2 _ (Finset.mem_singleton_self _)

/-- Coning to any chosen low vertex preserves actual low-link zero-chain support. -/
theorem low_cons_mem (g : IntegralGL) (L : RationalLine2) (hL : {L} ∈ lowLink g)
    {c : Chain RationalLine2} (hc : c ∈ chains (lowLink g) 1) :
    cons L c ∈ chains (lowLink g) 2 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨M,rfl⟩ := List.length_eq_one_iff.mp hlen
    have hM : {M} ∈ lowLink g := by
      simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using
        hl.resolve_left (by simp)
    rw [cons_simplex]
    apply simplex_mem_chains (lowLink g) [L,M]
    apply Or.inr
    simpa only [List.toFinset_cons,List.toFinset_nil,Finset.insert_empty] using low_pair_mem g L M hL hM
  | zero => simpa only [map_zero] using (chains (lowLink g) 2).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains (lowLink g) 2).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains (lowLink g) 2).smul_mem q ih

/-- Every finite reduced-zero chain in a positive-height lower vertex link has an actual
edge-chain filling wholly inside that lower link. -/
theorem lowLink_reduced_filling (g : IntegralGL) (hg : 0 < height (augmentedLine g 0))
    {c : Chain RationalLine2} (hc : c ∈ chains (lowLink g) 1) (hd : boundary c = 0) :
    ∃ b : Chain RationalLine2, b ∈ chains (lowLink g) 2 ∧ boundary b = c := by
  obtain ⟨L,hL⟩ := lowLink_nonempty g hg
  refine ⟨cons L c,low_cons_mem g L hL hc,?_⟩
  rw [boundary_cons_chain,hd,map_zero,sub_zero]

/-- Explicit integer alternatives for the low path coordinates. -/
theorem low_indices_cases (a b k l : ℤ)
    (hk : (b+k*a).natAbs < a.natAbs) (hl : (b+l*a).natAbs < a.natAbs) :
    k = l ∨ k = l+1 ∨ l = k+1 := by
  rcases low_indices_adjacent a b k l hk hl with he | he
  · exact Or.inl he
  · have hu := Int.isUnit_iff.mp (Int.isUnit_iff_natAbs_eq.mpr he)
    omega

/-- The set of allowable coordinates is nonempty and contained in one consecutive pair. -/
theorem low_indices_pair (a b : ℤ) (ha : a ≠ 0) :
    ∃ k : ℤ, (∃ l, (b+l*a).natAbs < a.natAbs) ∧
      ∀ l, (b+l*a).natAbs < a.natAbs → l = k ∨ l = k+1 := by
  obtain ⟨k,hk⟩ := exists_low_index a b ha
  by_cases hh : ∃ j, (b+j*a).natAbs < a.natAbs ∧ j < k
  · obtain ⟨j,hj,hjk⟩ := hh
    refine ⟨j,⟨k,hk⟩,?_⟩
    intro l hl
    have h1 := low_indices_cases a b k j hk hj
    have h2 := low_indices_cases a b l j hl hj
    have h3 := low_indices_cases a b l k hl hk
    omega
  · refine ⟨k,⟨k,hk⟩,?_⟩
    intro l hl
    have h1 := low_indices_cases a b l k hl hk
    have h2 : ¬l < k := fun hlt => hh ⟨l,hl,hlt⟩
    omega

/-- A positive-height lower link has one or two vertices, both in one literal path edge. -/
theorem lowLink_vertex_cover (g : IntegralGL) (hg : 0 < height (augmentedLine g 0)) :
    ∃ k : ℤ, ∀ L : RationalLine2, {L} ∈ lowLink g →
      L = coordinateLine g k ∨ L = coordinateLine g (k+1) := by
  have ha : g.val 1 0 ≠ 0 := by
    intro he
    rw [height_first,he] at hg
    simp at hg
  obtain ⟨k,_,hk⟩ := low_indices_pair (g.val 1 0) (g.val 1 1) ha
  refine ⟨k,?_⟩
  intro L hL
  obtain ⟨l,rfl,hl⟩ := low_exists_coordinate g L hL
  exact (hk l hl).imp (congrArg (coordinateLine g)) (congrArg (coordinateLine g))

/-- The whole lower-link face model is exactly the integer path restricted by the height inequality. -/
theorem low_coordinate_face_iff (g : IntegralGL) (s : Finset ℤ) :
    s.image (coordinateLine g) ∈ lowLink g ↔
      s ∈ IntegerPathChains.pathComplex ∧
        ∀ k ∈ s, (g.val 1 1+k*g.val 1 0).natAbs < (g.val 1 0).natAbs := by
  rw [mem_lowLink,coordinate_face_iff]
  constructor
  · rintro ⟨hs,hlo⟩
    refine ⟨hs,?_⟩
    intro k hk
    have he := hlo (coordinateLine g k) (Finset.mem_image.mpr ⟨k,hk,rfl⟩)
    simpa only [height_coordinateLine,height_first] using he
  · rintro ⟨hs,hlo⟩
    refine ⟨hs,?_⟩
    intro L hL
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hL
    simpa only [height_coordinateLine,height_first] using hlo k hk

end TernaryPoly.RankTwoHeightLinks
