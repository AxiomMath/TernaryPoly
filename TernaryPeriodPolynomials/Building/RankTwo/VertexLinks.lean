module

public import TernaryPeriodPolynomials.Building.RankTwo.AugmentedFrames
public import TernaryPeriodPolynomials.Building.Integer.PathChains
public import TernaryPeriodPolynomials.Analysis.PositiveChainSeparation
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainMap

@[expose] public section


noncomputable section
namespace TernaryPoly.RankTwoVertexLinks
open RankTwoAugmentedFrames OrientedListChains OrientedChainJoin GoodLinkExtraction
local instance : DecidableEq RationalLine2 := Classical.decEq _

/-- Integral affine coordinates on the complements of the first basis line. -/
def coordinateVector (k : ℤ) : IntegralVector := ![k,1]

def coordinateLine (g : IntegralGL) (k : ℤ) : RationalLine2 :=
  vectorLine (rationalRepresentation g (rationalVector (coordinateVector k))) (by
    intro h
    have he := (rationalRepresentation g).injective (h.trans (map_zero _).symm)
    have h1 := congrFun he 1
    simp [rationalVector,coordinateVector] at h1)

def vertexLink (g : IntegralGL) : PreAbstractSimplicialComplex RationalLine2 :=
  goodLink ambient (fun L => L ≠ augmentedLine g 0) {augmentedLine g 0}

/-- The matrix action on the first two templates is the actual column vector. -/
theorem representation_column (g : IntegralGL) (j : Fin 2) :
    rationalRepresentation g (template j.castSucc) = rationalVector (fun i => g.val i j) := by
  rw [rationalRepresentation_apply]
  have ht : template j.castSucc = Pi.single j 1 := by
    funext i
    fin_cases j <;> fin_cases i <;> simp [template]
  rw [ht,Matrix.mulVec_single_one]
  rfl

/-- Change to relative integral-basis coordinates inside the actual rational action. -/
theorem representation_relative (g h : IntegralGL) (v : Space) :
    rationalRepresentation h v =
      rationalRepresentation g (rationalRepresentation (g⁻¹*h) v) := by
  rw [← LinearEquiv.mul_apply,← map_mul,mul_inv_cancel_left]

/-- Membership in a transported line pulls back through the genuine inverse basis action. -/
theorem relative_mem_span (g h : IntegralGL) (v w : Space)
    (hm : rationalRepresentation h v ∈ Submodule.span ℚ {rationalRepresentation g w}) :
    rationalRepresentation (g⁻¹*h) v ∈ Submodule.span ℚ {w} := by
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  apply Submodule.mem_span_singleton.mpr
  refine ⟨q,?_⟩
  apply (rationalRepresentation g).injective
  rw [map_smul,← representation_relative]
  exact hq

/-- Equality of the first-column lines makes the relative matrix upper triangular. -/
theorem relative_lower_left_zero (g h : IntegralGL)
    (he : augmentedLine h 0 = augmentedLine g 0) : (g⁻¹*h).val 1 0 = 0 := by
  have hm : rationalRepresentation h (template 0) ∈
      Submodule.span ℚ {rationalRepresentation g (template 0)} := by
    change rationalRepresentation h (template 0) ∈ (augmentedLine g 0).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp (relative_mem_span g h _ _ hm)
  rw [show rationalRepresentation (g⁻¹*h) (template 0) =
    rationalVector (fun i => (g⁻¹*h).val i 0) from representation_column _ 0] at hq
  have h1 := congrFun hq 1
  have hz : ((g⁻¹*h).val 1 0 : ℚ) = 0 := by
    simpa [template,rationalVector,Pi.smul_apply] using h1.symm
  exact_mod_cast hz

/-- In an invertible upper-triangular integer matrix, the last diagonal entry is a unit. -/
theorem last_diagonal_unit (M : IntegralGL) (h10 : M.val 1 0 = 0) : IsUnit (M.val 1 1) := by
  have hd : IsUnit M.val.det := (Matrix.isUnit_iff_isUnit_det M.val).mp M.isUnit
  rw [Matrix.det_fin_two,h10,mul_zero,sub_zero] at hd
  exact isUnit_of_mul_isUnit_right hd

/-- Affine coordinate lines are distinct from the fixed first-column line. -/
theorem coordinateLine_ne_first (g : IntegralGL) (k : ℤ) :
    coordinateLine g k ≠ augmentedLine g 0 := by
  intro he
  have hm : rationalRepresentation g (rationalVector (coordinateVector k)) ∈
      Submodule.span ℚ {rationalRepresentation g (template 0)} := by
    change rationalRepresentation g (rationalVector (coordinateVector k)) ∈ (augmentedLine g 0).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  have hp : q • template 0 = rationalVector (coordinateVector k) :=
    (rationalRepresentation g).injective ((map_smul _ _ _).trans hq)
  have h1 := congrFun hp 1
  norm_num [template,rationalVector,coordinateVector,Pi.smul_apply] at h1

/-- The normalized last coordinate makes the integer affine coordinate unique. -/
theorem coordinateLine_injective (g : IntegralGL) : Function.Injective (coordinateLine g) := by
  intro k l he
  have hm : rationalRepresentation g (rationalVector (coordinateVector k)) ∈
      Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector l))} := by
    change rationalRepresentation g (rationalVector (coordinateVector k)) ∈ (coordinateLine g l).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  have hp : q • rationalVector (coordinateVector l) = rationalVector (coordinateVector k) :=
    (rationalRepresentation g).injective ((map_smul _ _ _).trans hq)
  have h0 := congrFun hp 0
  have h1 := congrFun hp 1
  have hq1 : q = 1 := by simpa [rationalVector,coordinateVector,Pi.smul_apply] using h1
  have hk : (l : ℚ) = (k : ℚ) := by simpa [hq1,rationalVector,coordinateVector,Pi.smul_apply] using h0
  exact_mod_cast hk.symm

/-- A singleton belongs to the actual vertex link precisely when it is a distinct ambient neighbor. -/
theorem singleton_mem_link_iff (g : IntegralGL) (L : RationalLine2) :
    {L} ∈ vertexLink g ↔ L ≠ augmentedLine g 0 ∧ {augmentedLine g 0,L} ∈ ambient := by
  have hu : ({augmentedLine g 0} : Finset RationalLine2) ∪ {L} = {augmentedLine g 0,L} := by
    ext M
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  rw [vertexLink,mem_goodLink,hu]
  simp [and_comm]

/-- Every actual link vertex has an integer affine coordinate in the fixed basis. -/
theorem exists_coordinate (g : IntegralGL) (L : RationalLine2) (hL : {L} ∈ vertexLink g) :
    ∃ k : ℤ, coordinateLine g k = L := by
  obtain ⟨hne,hface⟩ := (singleton_mem_link_iff g L).mp hL
  obtain ⟨h,hh0,hh1⟩ := edge_basis (augmentedLine g 0) L (Ne.symm hne) (by
    apply (ambient.isRelLowerSet_faces hface).2
    · intro M hM
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hM
    · simp)
  have h10 := relative_lower_left_zero g h hh0
  have h11 := last_diagonal_unit (g⁻¹*h) h10
  rcases Int.isUnit_iff.mp h11 with hp | hn
  · refine ⟨(g⁻¹*h).val 0 1,?_⟩
    rw [← hh1]
    apply Subtype.ext
    change Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector _))} =
      Submodule.span ℚ {rationalRepresentation h (template 1)}
    rw [representation_relative g h,show rationalRepresentation (g⁻¹*h) (template 1) =
      rationalVector (fun i => (g⁻¹*h).val i 1) from representation_column _ 1]
    apply congrArg (fun v : Space => Submodule.span ℚ {rationalRepresentation g v})
    funext i
    fin_cases i <;> simp [rationalVector,coordinateVector,hp]
  · refine ⟨-(g⁻¹*h).val 0 1,?_⟩
    rw [← hh1]
    apply Subtype.ext
    change Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector _))} =
      Submodule.span ℚ {rationalRepresentation h (template 1)}
    rw [representation_relative g h,show rationalRepresentation (g⁻¹*h) (template 1) =
      rationalVector (fun i => (g⁻¹*h).val i 1) from representation_column _ 1]
    have hv : rationalVector (fun i => (g⁻¹*h).val i 1) =
        (-1 : ℚ) • rationalVector (coordinateVector (-(g⁻¹*h).val 0 1)) := by
      funext i
      fin_cases i <;> simp [rationalVector,coordinateVector,hn]
    rw [hv,map_smul,Submodule.span_singleton_smul_eq (by norm_num : IsUnit (-1 : ℚ))]

/-- A relative integral column spanning the normalized affine line has the corresponding slope. -/
theorem relative_column_coordinate (g h : IntegralGL) (j : Fin 2) (k : ℤ)
    (he : augmentedLine h j.castSucc = coordinateLine g k) :
    (g⁻¹*h).val 0 j = k * (g⁻¹*h).val 1 j := by
  have hm : rationalRepresentation h (template j.castSucc) ∈
      Submodule.span ℚ {rationalRepresentation g (rationalVector (coordinateVector k))} := by
    change rationalRepresentation h (template j.castSucc) ∈ (coordinateLine g k).val
    rw [← he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp (relative_mem_span g h _ _ hm)
  rw [representation_column] at hq
  have h0 := congrFun hq 0
  have h1 := congrFun hq 1
  change q * (k : ℚ) = ((g⁻¹*h).val 0 j : ℚ) at h0
  change q * 1 = ((g⁻¹*h).val 1 j : ℚ) at h1
  rw [mul_one] at h1
  rw [h1,mul_comm] at h0
  exact_mod_cast h0.symm

/-- Distinct affine neighbors in an actual ambient edge differ by an integer unit. -/
theorem difference_unit_of_ambient (g : IntegralGL) (k l : ℤ) (hne : k ≠ l)
    (hface : {coordinateLine g k,coordinateLine g l} ∈ ambient) : IsUnit (k-l) := by
  have hneLine : coordinateLine g k ≠ coordinateLine g l := (coordinateLine_injective g).ne hne
  obtain ⟨h,hk,hl⟩ := edge_basis (coordinateLine g k) (coordinateLine g l) hneLine (by
    apply (ambient.isRelLowerSet_faces hface).2
    · intro M hM
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hM
    · simp)
  have h0 := relative_column_coordinate g h 0 k hk
  have h1 := relative_column_coordinate g h 1 l hl
  have hd : IsUnit (g⁻¹*h).val.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (g⁻¹*h).isUnit
  have he : (g⁻¹*h).val.det = ((g⁻¹*h).val 1 0 * (g⁻¹*h).val 1 1) * (k-l) := by
    rw [Matrix.det_fin_two,h0,h1]
    ring
  rw [he] at hd
  exact isUnit_of_mul_isUnit_right hd

/-- The explicit basis whose first column is (k,1) and whose second column is the fixed vector. -/
def neighborMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![k,1;1,0]
def neighborInverse (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0,1;1,-k]

def neighborBasis (k : ℤ) : IntegralGL :=
  ⟨neighborMatrix k,neighborInverse k,by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [neighborMatrix,neighborInverse,Matrix.mul_apply,Fin.sum_univ_two],by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [neighborMatrix,neighborInverse,Matrix.mul_apply,Fin.sum_univ_two]⟩

/-- The three template images in the explicit neighboring basis. -/
theorem neighborBasis_template (k : ℤ) (i : Fin 3) :
    rationalRepresentation (neighborBasis k) (template i) =
      (![rationalVector (coordinateVector k),template 0,
        rationalVector (coordinateVector (k+1))] : Fin 3 → Space) i := by
  rw [← rationalVector_integralTemplate,← rationalVector_mulVec]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [neighborBasis,neighborMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
      rationalVector,coordinateVector,integralTemplate,template]

/-- The neighboring augmented frame has the two consecutive affine lines and the fixed line. -/
theorem neighborBasis_lines (g : IntegralGL) (k : ℤ) :
    augmentedLine (g * neighborBasis k) 0 = coordinateLine g k ∧
    augmentedLine (g * neighborBasis k) 1 = augmentedLine g 0 ∧
    augmentedLine (g * neighborBasis k) 2 = coordinateLine g (k+1) := by
  have he (i : Fin 3) :
      rationalRepresentation (g * neighborBasis k) (template i) =
        rationalRepresentation g ((![rationalVector (coordinateVector k),template 0,
          rationalVector (coordinateVector (k+1))] : Fin 3 → Space) i) := by
    rw [map_mul,LinearEquiv.mul_apply,neighborBasis_template]
  exact ⟨Subtype.ext (congrArg (fun v : Space => Submodule.span ℚ {v}) (he 0)),
    Subtype.ext (congrArg (fun v : Space => Submodule.span ℚ {v}) (he 1)),
    Subtype.ext (congrArg (fun v : Space => Submodule.span ℚ {v}) (he 2))⟩

/-- Every displayed model line belongs to its actual augmented frame. -/
theorem augmentedLine_mem_frame (g : IntegralGL) (i : Fin 3) :
    augmentedLine g i ∈ augmentedFrame g := by
  let : DecidableEq RationalLine2 := fun a b => Subtype.instDecidableEq a b
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

/-- Every consecutive affine pair is an actual edge in the actual vertex link. -/
theorem consecutive_mem_link (g : IntegralGL) (k : ℤ) :
    {coordinateLine g k,coordinateLine g (k+1)} ∈ vertexLink g := by
  obtain ⟨h0,h1,h2⟩ := neighborBasis_lines g k
  rw [vertexLink,mem_goodLink]
  refine ⟨by simp,?_,?_⟩
  · apply subset_augmentedFrame_mem (g * neighborBasis k) (by simp)
    intro L hL
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with hL | hL | hL
    · exact (h1.trans hL.symm) ▸ augmentedLine_mem_frame (g * neighborBasis k) 1
    · exact (h0.trans hL.symm) ▸ augmentedLine_mem_frame (g * neighborBasis k) 0
    · exact (h2.trans hL.symm) ▸ augmentedLine_mem_frame (g * neighborBasis k) 2
  · intro L hL
    simp only [Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl
    · exact coordinateLine_ne_first g k
    · exact coordinateLine_ne_first g (k+1)

/-- All affine coordinate lines are actual link vertices. -/
theorem coordinate_mem_link (g : IntegralGL) (k : ℤ) : {coordinateLine g k} ∈ vertexLink g := by
  apply ((vertexLink g).isRelLowerSet_faces (consecutive_mem_link g k)).2
  · intro L hL
    exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hL))
  · simp

/-- Link faces themselves are ambient faces, by actual downward closure. -/
theorem link_face_ambient (g : IntegralGL) {s : Finset RationalLine2} (hs : s ∈ vertexLink g) :
    s ∈ ambient :=
  (ambient.isRelLowerSet_faces hs.1.2).2 Finset.subset_union_right hs.1.1

/-- Two distinct coordinates form a link edge exactly when their difference is an integer unit. -/
theorem pair_mem_link_iff (g : IntegralGL) (k l : ℤ) (hne : k ≠ l) :
    {coordinateLine g k,coordinateLine g l} ∈ vertexLink g ↔ IsUnit (k-l) := by
  constructor
  · intro h
    exact difference_unit_of_ambient g k l hne (link_face_ambient g h)
  · intro h
    rcases Int.isUnit_iff.mp h with hp | hn
    · have hk : k = l+1 := by omega
      rw [hk,Finset.pair_comm]
      exact consecutive_mem_link g l
    · have hl : l = k+1 := by omega
      rw [hl]
      exact consecutive_mem_link g k

/-- The actual rank-two vertex link has precisely the nearest-neighbor integer edges. -/
theorem pair_mem_link_iff_natAbs (g : IntegralGL) (k l : ℤ) (hne : k ≠ l) :
    {coordinateLine g k,coordinateLine g l} ∈ vertexLink g ↔ (k-l).natAbs = 1 := by
  rw [pair_mem_link_iff g k l hne,Int.isUnit_iff_natAbs_eq]

/-- The affine coordinates give a bijection from integers onto all actual link vertices. -/
theorem existsUnique_coordinate (g : IntegralGL) (L : RationalLine2) (hL : {L} ∈ vertexLink g) :
    ∃! k : ℤ, coordinateLine g k = L := by
  obtain ⟨k,hk⟩ := exists_coordinate g L hL
  exact ⟨k,hk,fun l hl => coordinateLine_injective g (hl.trans hk.symm)⟩

/-- Every integer-path face maps to an actual face of the fixed vertex link. -/
theorem coordinate_maps_faces (g : IntegralGL) :
    OrientedChainMap.MapsFaces (coordinateLine g) IntegerPathChains.pathComplex (vertexLink g) := by
  intro s hs
  obtain ⟨k,hk⟩ := hs.2
  apply ((vertexLink g).isRelLowerSet_faces (consecutive_mem_link g k)).2
  · intro L hL
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hL
    have hn' := hk hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn' ⊢
    exact hn'.imp (congrArg (coordinateLine g)) (congrArg (coordinateLine g))
  · exact hs.1.image _

/-- Every displayed vertex of an allowed link simplex has an integer coordinate. -/
theorem exists_coordinate_of_allowed (g : IntegralGL) {l : List RationalLine2}
    (hl : Allowed (vertexLink g) l) {L : RationalLine2} (hL : L ∈ l) :
    ∃ k : ℤ, coordinateLine g k = L := by
  apply exists_coordinate g L
  rcases hl with rfl | hl
  · simp at hL
  · apply ((vertexLink g).isRelLowerSet_faces hl).2
    · intro M hM
      have he := Finset.mem_singleton.mp hM
      subst M
      simpa only [List.mem_toFinset] using hL
    · simp

/-- Either orientation of a nearest-neighbor pair is an allowed integer-path simplex. -/
theorem path_pair_allowed (k l : ℤ) (h : IsUnit (k-l)) :
    Allowed IntegerPathChains.pathComplex [k,l] := by
  apply Or.inr
  refine ⟨by simp,?_⟩
  rcases Int.isUnit_iff.mp h with hp | hn
  · refine ⟨l,?_⟩
    have hk : k = l+1 := by omega
    intro n hn
    simpa [hk,or_comm] using hn
  · refine ⟨k,?_⟩
    have hl : l = k+1 := by omega
    intro n hn
    simpa [hl] using hn

/-- An allowed actual link edge lifts to an actual oriented integer-path edge chain. -/
theorem path_lift_simplex (g : IntegralGL) (L M : RationalLine2)
    (hl : Allowed (vertexLink g) [L,M]) :
    ∃ z : Chain ℤ, z ∈ chains IntegerPathChains.pathComplex 2 ∧
      OrientedChainMap.map (coordinateLine g) z = simplex [L,M] := by
  obtain ⟨k,rfl⟩ := exists_coordinate_of_allowed g hl (by simp : L ∈ [L,M])
  obtain ⟨l,rfl⟩ := exists_coordinate_of_allowed g hl
    (by simp : M ∈ [coordinateLine g k,M])
  by_cases hkl : k = l
  · subst l
    exact ⟨0,(chains IntegerPathChains.pathComplex 2).zero_mem,
      by rw [map_zero,simplex_repeat_adjacent]⟩
  · have hp : {coordinateLine g k,coordinateLine g l} ∈ vertexLink g := by
      have hf := hl.resolve_left (by simp)
      apply ((vertexLink g).isRelLowerSet_faces hf).2
      · intro A hA
        simpa only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,
          Finset.mem_insert,Finset.mem_singleton] using hA
      · simp
    have hu := (pair_mem_link_iff g k l hkl).mp hp
    refine ⟨simplex [k,l],simplex_mem_chains IntegerPathChains.pathComplex [k,l]
      (path_pair_allowed k l hu),?_⟩
    simp only [OrientedChainMap.map_simplex,List.map_cons,List.map_nil]

/-- Every actual oriented link one-chain has a finite actual integer-path lift. -/
theorem exists_path_lift (g : IntegralGL) {c : Chain RationalLine2}
    (hc : c ∈ chains (vertexLink g) 2) :
    ∃ z : Chain ℤ, z ∈ chains IntegerPathChains.pathComplex 2 ∧
      OrientedChainMap.map (coordinateLine g) z = c := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    exact path_lift_simplex g L M hl
  | zero => exact ⟨0,(chains IntegerPathChains.pathComplex 2).zero_mem,map_zero _⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨x,hx,hex⟩ := ihc
    obtain ⟨y,hy,hey⟩ := ihd
    exact ⟨x+y,(chains IntegerPathChains.pathComplex 2).add_mem hx hy,
      by rw [map_add,hex,hey]⟩
  | smul q c hc ih =>
    obtain ⟨x,hx,hex⟩ := ih
    exact ⟨q • x,(chains IntegerPathChains.pathComplex 2).smul_mem q hx,
      by rw [map_smul,hex]⟩

/-- There are no actual finite one-cycles in the rank-two augmented-frame vertex link. -/
theorem vertexLink_cycle_eq_zero (g : IntegralGL) {c : Chain RationalLine2}
    (hc : c ∈ chains (vertexLink g) 2) (hd : boundary c = 0) : c = 0 := by
  obtain ⟨z,hz,he⟩ := exists_path_lift g hc
  have hzBoundary : boundary z = 0 := by
    apply OrientedChainMap.map_injective (coordinateLine g) (coordinateLine_injective g)
    rw [← OrientedChainMap.boundary_map,he,hd,map_zero]
  have hzDiff : differential IntegerPathChains.pathComplex 1 ⟨z,hz⟩ = 0 :=
    Subtype.ext hzBoundary
  have hzZero : (⟨z,hz⟩ : IntegerPathChains.Edges) = 0 :=
    IntegerPathChains.differential_injective (hzDiff.trans (map_zero _).symm)
  have hv : z = 0 := congrArg Subtype.val hzZero
  rw [← he,hv,map_zero]

/-- Every rational line has an actual first-column representative, so all actual vertex links have no one-cycles. -/
theorem all_vertex_links_cycle_eq_zero (L : RationalLine2) {c : Chain RationalLine2}
    (hc : c ∈ chains (goodLink ambient (fun M => M ≠ L) {L}) 2)
    (hd : boundary c = 0) : c = 0 := by
  obtain ⟨g,hg⟩ := rationalLine_eq_augmentedLine L
  apply vertexLink_cycle_eq_zero g (c := c) _ hd
  change c ∈ chains (goodLink ambient (fun M => M ≠ augmentedLine g 0) {augmentedLine g 0}) 2
  simpa only [hg] using hc

/-- The actual rank-two augmented-frame complex has no top-dimensional cycles. -/
theorem top_cycle_eq_zero {c : Chain RationalLine2}
    (hc : c ∈ chains ambient 3) (hd : boundary c = 0) : c = 0 := by
  exact PositiveChainSeparation.cycle_eq_zero_of_vertex_links ambient 2
    (fun L z hz hd => all_vertex_links_cycle_eq_zero L hz hd) hc hd

/-- The actual boundary on rank-two augmented triangles is injective. -/
theorem top_boundary_injective {c d : Chain RationalLine2}
    (hc : c ∈ chains ambient 3) (hd : d ∈ chains ambient 3)
    (he : boundary c = boundary d) : c = d := by
  apply sub_eq_zero.mp
  apply top_cycle_eq_zero ((chains ambient 3).sub_mem hc hd)
  rw [map_sub,he,sub_self]

/-- Every actual subcomplex, including any arithmetic Good subcomplex, inherits top-cycle vanishing. -/
theorem subcomplex_top_cycle_eq_zero (C : PreAbstractSimplicialComplex RationalLine2)
    (hC : C ≤ ambient) {c : Chain RationalLine2} (hc : c ∈ chains C 3)
    (hd : boundary c = 0) : c = 0 :=
  top_cycle_eq_zero (chains_mono hC 3 hc) hd

/-- Top boundary is injective on every actual subcomplex of the rank-two augmented-frame complex. -/
theorem subcomplex_top_boundary_injective (C : PreAbstractSimplicialComplex RationalLine2)
    (hC : C ≤ ambient) {c d : Chain RationalLine2}
    (hc : c ∈ chains C 3) (hd : d ∈ chains C 3) (he : boundary c = boundary d) : c = d :=
  top_boundary_injective (chains_mono hC 3 hc) (chains_mono hC 3 hd) he

/-- An actual rank-two ambient face has at most three vertices. -/
theorem ambient_card_le_three {s : Finset RationalLine2} (hs : s ∈ ambient) : s.card ≤ 3 := by
  obtain ⟨_,g,hg⟩ := hs
  exact (Finset.card_le_card hg).trans_eq (augmentedFrame_card g)

/-- An actual vertex-link face has at most two vertices, so the coordinate graph describes every face. -/
theorem link_card_le_two (g : IntegralGL) {s : Finset RationalLine2} (hs : s ∈ vertexLink g) :
    s.card ≤ 2 := by
  have hm := (mem_goodLink ambient (fun L => L ≠ augmentedLine g 0) {augmentedLine g 0} s).mp hs
  have hnot : augmentedLine g 0 ∉ s := fun h => hm.2.2 _ h rfl
  have hf : insert (augmentedLine g 0) s ∈ ambient := by
    apply (ambient.isRelLowerSet_faces hm.2.1).2
    · intro L hL
      simpa only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert] using hL
    · simp
  have hc := ambient_card_le_three hf
  rw [Finset.card_insert_of_notMem hnot] at hc
  omega

/-- The affine coordinate image is an actual link face exactly for the integer-path faces. -/
theorem coordinate_face_iff (g : IntegralGL) (s : Finset ℤ) :
    s.image (coordinateLine g) ∈ vertexLink g ↔ s ∈ IntegerPathChains.pathComplex := by
  constructor
  · intro hs
    have hnonempty : s.Nonempty := Finset.image_nonempty.mp
      (((vertexLink g).isRelLowerSet_faces hs).1)
    have hcard : s.card ≤ 2 := by
      rw [← Finset.card_image_of_injective s (coordinateLine_injective g)]
      exact link_card_le_two g hs
    by_cases h1 : s.card = 1
    · obtain ⟨k,rfl⟩ := Finset.card_eq_one.mp h1
      exact ⟨by simp,k,by simp⟩
    · have h2 : s.card = 2 := by
        have hp := Finset.card_pos.mpr hnonempty
        omega
      obtain ⟨k,l,hkl,rfl⟩ := Finset.card_eq_two.mp h2
      have hp : {coordinateLine g k,coordinateLine g l} ∈ vertexLink g := by
        simpa only [Finset.image_insert,Finset.image_singleton] using hs
      have hu := (pair_mem_link_iff g k l hkl).mp hp
      have ha := (path_pair_allowed k l hu).resolve_left (by simp)
      apply (IntegerPathChains.pathComplex.isRelLowerSet_faces ha).2
      · intro n hn
        simpa only [Finset.mem_insert,Finset.mem_singleton,List.mem_toFinset,List.mem_cons,
          List.not_mem_nil,or_false] using hn
      · simp
  · exact coordinate_maps_faces g s

end TernaryPoly.RankTwoVertexLinks
