module

public import TernaryPeriodPolynomials.Building.Ambient.IndependentTriple
public import TernaryPeriodPolynomials.Building.AugmentedFrame.ChainAction
public import TernaryPeriodPolynomials.Building.Good.OrbitRelations

@[expose] public section


/-! Actual relative degree-two good chains, with tetrahedron boundaries killed.
Only generation and the forward reference relations are established here. -/

noncomputable section
namespace TernaryPoly.GoodRelativeChains
open ModThreeGoodAction AugmentedFrameComplex AugmentedBadFaces
open GoodAugmentedNormalForm OrientedListChains AugmentedChainAction
open ReferenceCoefficientMatrices

local instance : DecidableEq RationalLine := Classical.decEq _

abbrev GoodTwo := chains good 3
abbrev ProperTwo := chains properGood 3

def properInclusion : ProperTwo →ₗ[ℚ] GoodTwo :=
  Submodule.inclusion (chains_mono properGood_le_good 3)

/-- The embedded actual proper-good degree-two chains. -/
def properSubmodule : Submodule ℚ GoodTwo := properInclusion.range

abbrev RelativeTwo := GoodTwo ⧸ properSubmodule

/-- Kill the actual proper chains and actual good tetrahedron boundaries. -/
def nullSubmodule : Submodule ℚ GoodTwo :=
  properSubmodule ⊔ (differential good 3).range

abbrev RelativeBoundaryTwo := GoodTwo ⧸ nullSubmodule

def quotientMap : GoodTwo →ₗ[ℚ] RelativeBoundaryTwo := nullSubmodule.mkQ

theorem quotientMap_proper (x : ProperTwo) : quotientMap (properInclusion x) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (show properSubmodule ≤ nullSubmodule from le_sup_left) (LinearMap.mem_range_self _ x)

theorem quotientMap_boundary (x : chains good 4) :
    quotientMap (differential good 3 x) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (show (differential good 3).range ≤ nullSubmodule from le_sup_right)
    (LinearMap.mem_range_self _ x)

def triangleList (g : ModThreeGoodAction.IntegralGL) : List RationalLine :=
  [augmentedLine g 0, augmentedLine g 1, augmentedLine g 2]

theorem columnResidue_K (g : K) (j : Fin 3) : columnResidue g.val j = 1 := by
  have h := congrFun ((mem_K g.val).mp g.property) j
  change (∑ i, (1 : ZMod 3) * (g.val i j : ZMod 3)) = 1 at h
  simpa only [one_mul,columnResidue] using h

theorem good_K_augmentedLine (g : K) (i : Fin 4) : Good (augmentedLine g.val i).val := by
  apply good_augmentedLine_of_residue
  fin_cases i <;> simp only [templateResidue, columnResidue_K] <;> decide

theorem allowed_K_list (g : K) (l : List RationalLine)
    (hl : l ≠ []) (hsub : ∀ L ∈ l, ∃ i : Fin 4, augmentedLine g.val i = L) :
    Allowed good l := by
  refine Or.inr ⟨⟨(List.toFinset_nonempty_iff l).mpr hl, g.val, ?_⟩, ?_⟩
  · intro L hL
    exact (mem_augmentedFrame_iff _ _).mpr (hsub L (List.mem_toFinset.mp hL))
  · intro L hL
    obtain ⟨i, rfl⟩ := hsub L (List.mem_toFinset.mp hL)
    exact good_K_augmentedLine g i

theorem triangleList_allowed (g : K) : Allowed good (triangleList g.val) := by
  apply allowed_K_list g _ (by simp [triangleList])
  intro L hL
  simp only [triangleList, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

def triangle (g : K) : GoodTwo :=
  ⟨simplex (triangleList g.val), by
    have h := simplex_mem_chains good _ (triangleList_allowed g)
    change simplex (triangleList g.val) ∈ chains good 3 at h
    exact h⟩

abbrev FreeOrbit := GoodOrbitRelations.FreeOrbit

def orbitMap : FreeOrbit →ₗ[ℚ] RelativeBoundaryTwo :=
  Finsupp.lsum ℚ fun g => LinearMap.toSpanSingleton ℚ _ (quotientMap (triangle g))

@[simp] theorem orbitMap_delta (g : K) :
    orbitMap (GoodOrbitRelations.delta g) = quotientMap (triangle g) := by
  simp only [orbitMap, GoodOrbitRelations.delta, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply, one_smul]

/-- Changing each column by its normalization sign leaves its line vertex unchanged. -/
theorem normalize_columnLine (g : ModThreeGoodAction.IntegralGL) (j : Fin 3) :
    augmentedLine (normalize g) j.castSucc = augmentedLine g j.castSucc := by
  apply Subtype.ext
  rw [augmentedLine_castSucc_val, augmentedLine_castSucc_val, normalize_basis]
  apply Submodule.span_singleton_smul_eq
  apply isUnit_iff_ne_zero.mpr
  exact_mod_cast normalizingSign_ne_zero (columnResidue g j)

/-- Every full-span ordered good triangle is literally an ordered K-frame triangle. -/
theorem exists_K_triangle (L : Fin 3 → RationalLine)
    (hg : Finset.univ.image L ∈ good)
    (hd : Module.finrank ℚ (faceSpan (Finset.univ.image L)) = 3) :
    ∃ g : K, ∀ j : Fin 3, augmentedLine g.val j.castSucc = L j := by
  have himage : @Finset.image (Fin 3) RationalLine
      (fun a b => Subtype.instDecidableEq a b) L Finset.univ = Finset.univ.image L := by
    ext x
    simp only [Finset.mem_image]
  obtain ⟨g,hgL⟩ := AmbientIndependentTriple.exists_integralGL_of_finrank_eq_three L
    (by rw [himage]; exact good_le_ambient hg) (by rw [himage]; exact hd)
  have hc (j : Fin 3) : columnResidue g j ≠ 0 := by
    have h := (good_augmentedLine_iff_residue g j.castSucc).mp
      (hgL j ▸ hg.2 (L j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    fin_cases j <;> exact h
  exact ⟨⟨normalize g,normalize_mem_K g hc⟩,
    fun j => (normalize_columnLine g j).trans (hgL j)⟩

private theorem image_triple (x y z : RationalLine) :
    Finset.univ.image (![x,y,z] : Fin 3 → RationalLine) = [x,y,z].toFinset := by
  ext L
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨j,rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem simplex_class_mem_range (l : List RationalLine) (hlen : l.length = 3)
    (hl : Allowed good l) (hc : simplex l ∈ GoodTwo) :
    quotientMap ⟨simplex l,hc⟩ ∈ orbitMap.range := by
  obtain ⟨x,y,z,rfl⟩ := List.length_eq_three.mp hlen
  have hg : [x,y,z].toFinset ∈ good := hl.resolve_left (by simp)
  by_cases hd : Module.finrank ℚ (faceSpan [x,y,z].toFinset) ≤ 2
  · have hp : simplex [x,y,z] ∈ ProperTwo :=
      by
        have h := simplex_mem_chains properGood [x,y,z] (Or.inr ⟨hg,hd⟩)
        change simplex [x,y,z] ∈ chains properGood 3 at h
        exact h
    have he : (⟨simplex [x,y,z],hc⟩ : GoodTwo) = properInclusion ⟨_,hp⟩ := rfl
    rw [he,quotientMap_proper]
    exact orbitMap.range.zero_mem
  · have hle : Module.finrank ℚ (faceSpan [x,y,z].toFinset) ≤ 3 := by
      simpa only [Space,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using
        Submodule.finrank_le (faceSpan [x,y,z].toFinset)
    have he : Module.finrank ℚ (faceSpan [x,y,z].toFinset) = 3 := by omega
    obtain ⟨g,hgL⟩ := exists_K_triangle ![x,y,z]
      (by rwa [image_triple]) (by rwa [image_triple])
    have ht : triangle g = ⟨simplex [x,y,z],hc⟩ := by
      apply Subtype.ext
      change simplex [augmentedLine g.val 0,augmentedLine g.val 1,
        augmentedLine g.val 2] = simplex [x,y,z]
      have h0 : augmentedLine g.val 0 = x := hgL 0
      have h1 : augmentedLine g.val 1 = y := hgL 1
      have h2 : augmentedLine g.val 2 = z := hgL 2
      rw [h0,h1,h2]
    exact ⟨GoodOrbitRelations.delta g,(orbitMap_delta g).trans (congrArg quotientMap ht)⟩

/-- Actual good simplices generate the quotient, with proper-span generators zero. -/
theorem orbitMap_surjective : Function.Surjective orbitMap := by
  intro q
  obtain ⟨x,rfl⟩ := nullSubmodule.mkQ_surjective q
  suffices h : quotientMap x ∈ orbitMap.range from h
  obtain ⟨x,hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l,hlen,hl,rfl⟩ := hx
    exact simplex_class_mem_range l hlen hl _
  | zero => exact orbitMap.range.zero_mem
  | add x y hx hy ihx ihy =>
    exact orbitMap.range.add_mem ihx ihy
  | smul r x hx ih =>
    exact orbitMap.range.smul_mem r ih

private theorem reference_column_lines (g : ModThreeGoodAction.IntegralGL)
    (idx : Fin 3 → Fin 4) (sign : Fin 3 → ℚ) (hs : ∀ j, sign j ≠ 0)
    (hv : ∀ j, rationalRepresentation g (Pi.single j 1) = sign j • template (idx j))
    (j : Fin 3) : augmentedLine g j.castSucc = augmentedLine 1 (idx j) := by
  apply Subtype.ext
  rw [augmentedLine_castSucc_val, hv]
  change Submodule.span ℚ {sign j • template (idx j)} =
    Submodule.span ℚ {rationalRepresentation 1 (template (idx j))}
  rw [map_one]
  change Submodule.span ℚ {sign j • template (idx j)} = Submodule.span ℚ {template (idx j)}
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (hs j)) _

private theorem c_column (j : Fin 3) :
    augmentedLine c j.castSucc = augmentedLine 1 ((![1,2,0] : Fin 3 → Fin 4) j) := by
  apply reference_column_lines c _ (fun _ => 1) (fun _ => one_ne_zero) _ j
  intro j
  rw [rationalRepresentation_basis]
  fin_cases j <;> ext i <;> fin_cases i <;> decide +kernel

private theorem s_column (j : Fin 3) :
    augmentedLine s j.castSucc = augmentedLine 1 ((![1,0,2] : Fin 3 → Fin 4) j) := by
  apply reference_column_lines s _ (fun _ => 1) (fun _ => one_ne_zero) _ j
  intro j
  rw [rationalRepresentation_basis]
  fin_cases j <;> ext i <;> fin_cases i <;> decide +kernel

private theorem a_column (j : Fin 3) :
    augmentedLine a j.castSucc = augmentedLine 1 ((![1,3,2] : Fin 3 → Fin 4) j) := by
  apply reference_column_lines a _ (![1,-1,1]) (by intro j; fin_cases j <;> norm_num) _ j
  intro j
  rw [rationalRepresentation_basis]
  fin_cases j <;> ext i <;> fin_cases i <;> decide +kernel

private theorem a_sq_column (j : Fin 3) :
    augmentedLine (a^2) j.castSucc = augmentedLine 1 ((![3,0,2] : Fin 3 → Fin 4) j) := by
  rw [← a_inv_eq_sq]
  apply reference_column_lines a⁻¹ _ (![-1,1,1]) (by intro j; fin_cases j <;> norm_num) _ j
  intro j
  rw [rationalRepresentation_basis]
  fin_cases j <;> ext i <;> fin_cases i <;> decide +kernel

private theorem simplex_cyclic (x y z : RationalLine) :
    simplex [y,z,x] = simplex [x,y,z] := by
  have h := congrArg (cons y) (simplex_swap_eq_neg z x ([] : List RationalLine))
  simp only [cons_simplex,map_neg] at h
  rw [h,simplex_swap_eq_neg y x [z],neg_neg]

theorem triangle_mul (g h : K) :
    (triangle (g*h)).val = chainAction g.val (triangle h).val := by
  simp only [triangle,chainAction_simplex,triangleList,List.map_cons,List.map_nil,
    lineAction_augmentedLine,Subgroup.coe_mul]

theorem triangle_cyclic (g : K) : triangle (g*cK) = triangle g := by
  apply Subtype.ext
  rw [triangle_mul]
  have hc : (triangle cK).val = (triangle (1 : K)).val := by
    change simplex [augmentedLine c 0,augmentedLine c 1,augmentedLine c 2] = _
    have h0 : augmentedLine c 0 = augmentedLine 1 1 := c_column 0
    have h1 : augmentedLine c 1 = augmentedLine 1 2 := c_column 1
    have h2 : augmentedLine c 2 = augmentedLine 1 0 := c_column 2
    rw [h0,h1,h2]
    exact simplex_cyclic _ _ _
  rw [hc,← triangle_mul,mul_one]

theorem triangle_swap (g : K) : triangle (g*sK) = -triangle g := by
  apply Subtype.ext
  rw [triangle_mul]
  have hs : (triangle sK).val = -(triangle (1 : K)).val := by
    change simplex [augmentedLine s 0,augmentedLine s 1,augmentedLine s 2] = _
    have h0 : augmentedLine s 0 = augmentedLine 1 1 := s_column 0
    have h1 : augmentedLine s 1 = augmentedLine 1 0 := s_column 1
    have h2 : augmentedLine s 2 = augmentedLine 1 2 := s_column 2
    rw [h0,h1,h2]
    exact simplex_swap_eq_neg _ _ _
  rw [hs,map_neg,← triangle_mul,mul_one]
  rfl

def tetrahedronList (g : ModThreeGoodAction.IntegralGL) : List RationalLine :=
  [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3,augmentedLine g 2]

def coreList (g : ModThreeGoodAction.IntegralGL) : List RationalLine :=
  [augmentedLine g 0,augmentedLine g 1,augmentedLine g 3]

theorem tetrahedronList_allowed (g : K) : Allowed good (tetrahedronList g.val) := by
  apply allowed_K_list g _ (by simp [tetrahedronList])
  intro L hL
  simp only [tetrahedronList,List.mem_cons,List.not_mem_nil,or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨2,rfl⟩

theorem coreList_allowed (g : K) : Allowed properGood (coreList g.val) := by
  have hg : Allowed good (coreList g.val) := by
    apply allowed_K_list g _ (by simp [coreList])
    intro L hL
    simp only [coreList,List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨3,rfl⟩
  refine Or.inr ⟨hg.resolve_left (by simp [coreList]),?_⟩
  let P := (augmentedLine g.val 0).val ⊔ (augmentedLine g.val 1).val
  have hsum : (augmentedLine g.val 3).val ≤ P := by
    apply Submodule.span_le.mpr
    rintro v (rfl : v = _)
    change rationalRepresentation g.val (Pi.single 0 1 + Pi.single 1 1) ∈ P
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hspan : faceSpan (coreList g.val).toFinset ≤ P := by
    simp only [coreList,List.toFinset_cons,List.toFinset_nil,faceSpan,
      Finset.sup_insert,Finset.sup_empty,sup_bot_eq]
    exact sup_le le_sup_left (sup_le le_sup_right hsum)
  have hd := Submodule.finrank_add_le_finrank_add_finrank
    (augmentedLine g.val 0).val (augmentedLine g.val 1).val
  rw [(augmentedLine g.val 0).property,(augmentedLine g.val 1).property] at hd
  exact (Submodule.finrank_mono hspan).trans hd

def tetrahedron (g : K) : chains good 4 :=
  ⟨simplex (tetrahedronList g.val), by
    have h := simplex_mem_chains good _ (tetrahedronList_allowed g)
    change simplex (tetrahedronList g.val) ∈ chains good 4 at h
    exact h⟩

def core (g : K) : ProperTwo :=
  ⟨simplex (coreList g.val), by
    have h := simplex_mem_chains properGood _ (coreList_allowed g)
    change simplex (coreList g.val) ∈ chains properGood 3 at h
    exact h⟩

/-- The norm triangles are the actual tetrahedron boundary plus its proper core. -/
theorem triangle_norm_boundary (g : K) :
    triangle g + triangle (g*aK) + triangle (g*aK^2) =
      differential good 3 (tetrahedron g) + properInclusion (core g) := by
  apply Subtype.ext
  have hreference : (triangle (1 : K)).val + (triangle aK).val +
      (triangle (aK^2)).val = boundary (simplex (tetrahedronList 1)) +
        simplex (coreList 1) := by
    change simplex [augmentedLine 1 0,augmentedLine 1 1,augmentedLine 1 2] +
      simplex [augmentedLine a 0,augmentedLine a 1,augmentedLine a 2] +
      simplex [augmentedLine (a^2) 0,augmentedLine (a^2) 1,augmentedLine (a^2) 2] = _
    have h0 : augmentedLine a 0 = augmentedLine 1 1 := a_column 0
    have h1 : augmentedLine a 1 = augmentedLine 1 3 := a_column 1
    have h2 : augmentedLine a 2 = augmentedLine 1 2 := a_column 2
    have k0 : augmentedLine (a^2) 0 = augmentedLine 1 3 := a_sq_column 0
    have k1 : augmentedLine (a^2) 1 = augmentedLine 1 0 := a_sq_column 1
    have k2 : augmentedLine (a^2) 2 = augmentedLine 1 2 := a_sq_column 2
    rw [h0,h1,h2,k0,k1,k2]
    simp only [tetrahedronList,coreList,boundary_cons,boundary_nil,map_sub,map_zero,
      cons_simplex,sub_zero]
    rw [simplex_swap_eq_neg (augmentedLine 1 3) (augmentedLine 1 0)]
    abel
  have h := congrArg (chainAction g.val) hreference
  simp only [map_add,← triangle_mul,mul_one,← boundary_chainAction,
    chainAction_simplex,tetrahedronList,coreList,List.map_cons,List.map_nil,
    lineAction_augmentedLine,mul_one] at h
  exact h

theorem cyclicRelation_mem_ker (g : K) :
    GoodOrbitRelations.cyclicRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,GoodOrbitRelations.cyclicRelation,map_sub,
    orbitMap_delta,orbitMap_delta,triangle_cyclic,sub_self]

theorem swapRelation_mem_ker (g : K) :
    GoodOrbitRelations.swapRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,GoodOrbitRelations.swapRelation,map_add,
    orbitMap_delta,orbitMap_delta,triangle_swap,map_neg,neg_add_cancel]

theorem normRelation_mem_ker (g : K) :
    GoodOrbitRelations.normRelation g ∈ LinearMap.ker orbitMap := by
  rw [LinearMap.mem_ker,GoodOrbitRelations.normRelation,map_add,map_add,
    orbitMap_delta,orbitMap_delta,orbitMap_delta,← map_add,← map_add,
    triangle_norm_boundary,map_add,quotientMap_boundary,quotientMap_proper,add_zero]

/-- Only the forward inclusion: no claim of relation completeness or injectivity. -/
theorem relations_le_ker : GoodOrbitRelations.relations ≤ LinearMap.ker orbitMap := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with (⟨g,rfl⟩ | ⟨g,rfl⟩) | ⟨g,rfl⟩
  · exact normRelation_mem_ker g
  · exact cyclicRelation_mem_ker g
  · exact swapRelation_mem_ker g

end TernaryPoly.GoodRelativeChains
