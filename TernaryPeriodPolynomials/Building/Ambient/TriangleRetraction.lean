module

public import TernaryPeriodPolynomials.Building.Ambient.TriangleLocalGeometry

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientTriangleRetraction
open ModThreeGoodAction GoodIntegralNormalization PrimitiveLineUniqueness
open GoodAugmentedNormalForm AugmentedFrameComplex AugmentedBadFaces
open PrimitiveLineHeight IntegralFrameHeightReduction AmbientEdgeRetraction
open AmbientTriangleLocalGeometry AmbientDependentTriangles OrientedListChains

/-- Nonnegative primitive signs turn a signed relation into a positive sum after reordering,
except that the all-zero case may require changing two generator signs. -/
theorem nonnegative_additive_cases (F : IntegralVector →ₗ[ℤ] ℤ) (x y z : IntegralVector)
    (hx : 0 ≤ F x) (hy : 0 ≤ F y) (hz : 0 ≤ F z)
    (s t : ℤ) (hs : s*s=1) (ht : t*t=1) (he : x = s • y + t • z) :
    x = y+z ∨ y = x+z ∨ z = x+y ∨
      (F x = 0 ∧ F y = 0 ∧ F z = 0 ∧ x = -y + -z) := by
  rcases Int.isUnit_eq_one_or (IsUnit.of_mul_eq_one s hs) with rfl | rfl <;>
    rcases Int.isUnit_eq_one_or (IsUnit.of_mul_eq_one t ht) with rfl | rfl
  · exact Or.inl (by simpa using he)
  · right; left
    simp only [one_smul,neg_one_smul] at he
    rw [he]
    abel
  · right; right; left
    simp only [one_smul,neg_one_smul] at he
    rw [he]
    abel
  · simp only [neg_one_smul] at he
    have hval : F x = -F y + -F z := by rw [he,map_add,map_neg,map_neg]
    exact Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,he⟩))

/-- The complement and any distinct core pair can be aligned with specified primitive generators. -/
theorem aligned_core_pair_basis (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j)
    (W v u : IntegralVector) (hW : Primitive W) (hv : Primitive v) (hu : Primitive u)
    (hsW : Submodule.span ℚ {rationalVector W} = (augmentedLine g 2).val)
    (hsv : Submodule.span ℚ {rationalVector v} = (augmentedLine g (coreIndex i)).val)
    (hsu : Submodule.span ℚ {rationalVector u} = (augmentedLine g (coreIndex j)).val) :
    ∃ h : IntegralGL, h.val.col 0 = W ∧ h.val.col 1 = v ∧ h.val.col 2 = u := by
  have hinj : Function.Injective (![2,coreIndex i,coreIndex j] : Fin 3 → Fin 4) :=
    (by decide +kernel : ∀ i j : Fin 3, i ≠ j →
      Function.Injective (![2,coreIndex i,coreIndex j] : Fin 3 → Fin 4)) i j hij
  obtain ⟨a,ha⟩ := ordered_template_basis g ![2,coreIndex i,coreIndex j] hinj ⟨0,rfl⟩
  let v' : Fin 3 → IntegralVector := ![W,v,u]
  have hp : ∀ k, Primitive (v' k) := by
    intro k
    fin_cases k
    · exact hW
    · exact hv
    · exact hu
  have hsp : ∀ k, Submodule.span ℚ {rationalVector (v' k)} =
      (augmentedLine a k.castSucc).val := by
    intro k
    fin_cases k
    · exact hsW.trans (congrArg Subtype.val (ha 0)).symm
    · exact hsv.trans (congrArg Subtype.val (ha 1)).symm
    · exact hsu.trans (congrArg Subtype.val (ha 2)).symm
  obtain ⟨h,hh⟩ := exists_basis_columns a v' hp hsp
  exact ⟨h,hh 0,hh 1,hh 2⟩

/-- An actual additive core opposite the fixed complementary vertex has a low boundary lift. -/
theorem internal_core_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (g : IntegralGL) (hw : augmentedLine g 2 = w)
    (hf : (coreList g).toFinset ∈ link w) : Liftable F W w (simplex (coreList g)) := by
  classical
  let A := augmentedLine g 0
  let B := augmentedLine g 1
  let C := augmentedLine g 3
  let x := nonnegativeRepresentative F A
  let y := nonnegativeRepresentative F B
  let z := nonnegativeRepresentative F C
  have hA : {A} ∈ link w := singleton_of_link_list w _ hf A (by simp [coreList,A])
  have hB : {B} ∈ link w := singleton_of_link_list w _ hf B (by simp [coreList,B])
  have hC : {C} ∈ link w := singleton_of_link_list w _ hf C (by simp [coreList,C])
  have hpx : Primitive x := nonnegativeRepresentative_primitive F A
  have hpy : Primitive y := nonnegativeRepresentative_primitive F B
  have hpz : Primitive z := nonnegativeRepresentative_primitive F C
  have hsx : Submodule.span ℚ {rationalVector x} = A.val := nonnegativeRepresentative_span F A
  have hsy : Submodule.span ℚ {rationalVector y} = B.val := nonnegativeRepresentative_span F B
  have hsz : Submodule.span ℚ {rationalVector z} = C.val := nonnegativeRepresentative_span F C
  have hx : 0 ≤ F x := nonnegativeRepresentative_nonneg F A
  have hy : 0 ≤ F y := nonnegativeRepresentative_nonneg F B
  have hz : 0 ≤ F z := nonnegativeRepresentative_nonneg F C
  have hsW : Submodule.span ℚ {rationalVector W} = (augmentedLine g 2).val := by
    rw [hw]
    exact hspan
  have hn : [A,B,C].Nodup := by
    have hi : ([0,1,3] : List (Fin 4)).Nodup := by decide
    exact hi.map (augmentedLine_injective g)
  obtain ⟨s,t,hs,ht,he⟩ := primitive_core_relation g A B C (List.Perm.refl _) hn x y z
    hpx hpy hpz hsx hsy hsz
  change Liftable F W w (simplex [A,B,C])
  rcases nonnegative_additive_cases F x y z hx hy hz s t hs ht he with he | he | he | he
  · obtain ⟨h,hh0,hh1,hh2⟩ := aligned_core_pair_basis g 1 2 (by decide) W y z
      hW hpy hpz hsW hsy hsz
    exact internal_sum_lift F W w A B C hW hspan hN hA hB hC x y z
      hpx hpy hpz hsx hsy hsz he hy hz h hh0 hh1 hh2
  · obtain ⟨h,hh0,hh1,hh2⟩ := aligned_core_pair_basis g 0 2 (by decide) W x z
      hW hpx hpz hsW hsx hsz
    apply liftable_perm F W w (show [A,B,C].Perm [B,A,C] from List.Perm.swap _ _ _)
    exact internal_sum_lift F W w B A C hW hspan hN hB hA hC y x z
      hpy hpx hpz hsy hsx hsz he hx hz h hh0 hh1 hh2
  · obtain ⟨h,hh0,hh1,hh2⟩ := aligned_core_pair_basis g 0 1 (by decide) W x y
      hW hpx hpy hsW hsx hsy
    have hp : [A,B,C].Perm [C,A,B] := by
      have hp' : ([0,1,2] : List (Fin 3)).Perm [2,0,1] := by decide
      simpa using hp'.map (![A,B,C] : Fin 3 → RationalLine)
    apply liftable_perm F W w hp
    exact internal_sum_lift F W w C A B hW hspan hN hC hA hB z x y
      hpz hpx hpy hsz hsx hsy he hx hy h hh0 hh1 hh2
  · have hsy' : Submodule.span ℚ {rationalVector (-y)} = B.val := (span_neg y).trans hsy
    have hsz' : Submodule.span ℚ {rationalVector (-z)} = C.val := (span_neg z).trans hsz
    have hy' : 0 ≤ F (-y) := by rw [map_neg,he.2.1]; omega
    have hz' : 0 ≤ F (-z) := by rw [map_neg,he.2.2.1]; omega
    obtain ⟨h,hh0,hh1,hh2⟩ := aligned_core_pair_basis g 1 2 (by decide) W (-y) (-z)
      hW hpy.neg hpz.neg hsW hsy' hsz'
    exact internal_sum_lift F W w A B C hW hspan hN hA hB hC x (-y) (-z)
      hpx hpy.neg hpz.neg hsx hsy' hsz' he.2.2.2 hy' hz' h hh0 hh1 hh2

/-- The four literal template vertices exhaust both possible kinds of vertex-link triangles. -/
theorem template_vertex_link_cases : ∀ i j k m : Fin 4,
    ([i,j,k,m] : List (Fin 4)).Nodup →
      (i = 2 ∧ ([j,k,m] : List (Fin 4)).Perm [0,1,3]) ∨
      ∃ a b c : Fin 3, i = coreIndex a ∧
        ([i,coreIndex b,coreIndex c] : List (Fin 4)).Perm [0,1,3] ∧
        ([j,k,m] : List (Fin 4)).Perm [coreIndex b,coreIndex c,2] := by
  decide +kernel

/-- A list permutation preserves the actual finite face, independently of its order. -/
theorem face_list_perm (D : PreAbstractSimplicialComplex RationalLine)
    {l m : List RationalLine} (hp : l.Perm m) (hl : l.toFinset ∈ D) : m.toFinset ∈ D := by
  classical
  convert hl using 1
  ext x
  simp only [List.mem_toFinset]
  exact hp.mem_iff.symm

/-- Every nondegenerate actual link triangle has the low boundary lifting property. -/
theorem nondegenerate_triangle_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hf : l.toFinset ∈ link w) : Liftable F W w (simplex l) := by
  classical
  obtain ⟨A,B,C,rfl⟩ := List.length_eq_three.mp hlen
  have hw : w ∉ [A,B,C] := by
    intro hw
    exact hf.2 w (List.mem_toFinset.mpr hw) rfl
  have hn4 : [w,A,B,C].Nodup := List.nodup_cons.mpr ⟨hw,hn⟩
  have ht : [w,A,B,C].toFinset ∈ ambient := by
    convert hf.1.2 using 1
    ext x
    simp
  obtain ⟨_,g,hg⟩ := ht
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hg (by simp : w ∈ [w,A,B,C].toFinset))
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (hg (by simp : A ∈ [w,A,B,C].toFinset))
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp (hg (by simp : B ∈ [w,A,B,C].toFinset))
  obtain ⟨m,_,hm⟩ := Finset.mem_image.mp (hg (by simp : C ∈ [w,A,B,C].toFinset))
  have hidx : ([i,j,k,m] : List (Fin 4)).Nodup := by
    apply List.Nodup.of_map (f := augmentedLine g)
    simpa only [List.map_cons,List.map_nil,hi,hj,hk,hm] using hn4
  rcases template_vertex_link_cases i j k m hidx with ⟨hi2,hp⟩ | ⟨a,b,c,hia,hpc,hpr⟩
  · have hp' : [A,B,C].Perm (coreList g) := by
      simpa only [List.map_cons,List.map_nil,hj,hk,hm,coreList] using hp.map (augmentedLine g)
    apply liftable_perm F W w hp'
    apply internal_core_lift F W w hW hspan hN g
    · rw [← hi2]
      exact hi
    · exact face_list_perm (link w) hp' hf
  · have hw' : augmentedLine g (coreIndex a) = w := by rw [← hia]; exact hi
    have hpc' : [w,augmentedLine g (coreIndex b),augmentedLine g (coreIndex c)].Perm
        (coreList g) := by
      simpa only [List.map_cons,List.map_nil,hi,coreList] using hpc.map (augmentedLine g)
    have hpr' : [A,B,C].Perm
        [augmentedLine g (coreIndex b),augmentedLine g (coreIndex c),augmentedLine g 2] := by
      simpa only [List.map_cons,List.map_nil,hj,hk,hm] using hpr.map (augmentedLine g)
    have hcore : (coreList g).Nodup := by
      have h0 : ([0,1,3] : List (Fin 4)).Nodup := by decide
      exact h0.map (augmentedLine_injective g)
    apply liftable_perm F W w hpr'
    exact external_triangle_lift F W w hW hspan hN g a b c hw' hpc'
      (hpc'.nodup_iff.mpr hcore) (face_list_perm (link w) hpr' hf)

/-- Degenerate and nondegenerate actual link triangles both have the exact low boundary lift. -/
theorem simplex_boundary_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (l : List RationalLine) (hlen : l.length = 3) (hl : Allowed (link w) l) :
    Liftable F W w (simplex l) := by
  classical
  by_cases hn : l.Nodup
  · rcases hl with rfl | hl
    · simp at hlen
    · apply nondegenerate_triangle_lift F W w hW hspan hN l hlen hn
      convert hl using 1
      ext x
      simp only [List.mem_toFinset]
  · rw [simplex_eq_zero_of_not_nodup l hn]
    exact liftable_zero F W w

/-- Finite linear combinations extend the literal triangle lifts without choosing a global orientation. -/
theorem chain_boundary_lift (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (c : Chain RationalLine) (hc : c ∈ chains (link w) 3) :
    ∃ b : Chain RationalLine, b ∈ chains (lowLink F W w) 3 ∧
      boundary b = OrientedChainMap.map (retract F W) (boundary c) := by
  change Liftable F W w c
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    exact simplex_boundary_lift F W w hW hspan hN l hlen hl
  | zero => exact liftable_zero F W w
  | add c d hc hd ihc ihd => exact liftable_add F W w ihc ihd
  | smul q c hc ih => exact liftable_smul F W w q ih

/-- Every unrestricted link filler whose boundary is already low can be replaced by a low filler. -/
theorem boundary_lift_of_low (F : IntegralVector →ₗ[ℤ] ℤ) (W : IntegralVector)
    (w : RationalLine) (hW : Primitive W)
    (hspan : Submodule.span ℚ {rationalVector W} = w.val) (hN : 0 < F W)
    (c a : Chain RationalLine) (hc : c ∈ chains (link w) 3)
    (ha : a ∈ chains (lowLink F W w) 2) (he : boundary c = a) :
    ∃ b : Chain RationalLine, b ∈ chains (lowLink F W w) 3 ∧ boundary b = a := by
  obtain ⟨b,hb,hbd⟩ := chain_boundary_lift F W w hW hspan hN c hc
  refine ⟨b,hb,?_⟩
  rw [he,retract_eq_self_on_low_chains F W w 2 ha] at hbd
  exact hbd

end TernaryPoly.AmbientTriangleRetraction
