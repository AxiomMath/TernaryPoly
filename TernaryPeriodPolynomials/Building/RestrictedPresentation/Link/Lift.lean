module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Charts

@[expose] public section


/-!
# Lemma A.1: faces of `L_b` over block charts, lifts from `Z`, and the generator facts

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.2.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection

theorem exists_index_list (q : RankTwoAugmentedFrames.IntegralGL)
    (l : List RankTwoAugmentedFrames.RationalLine2)
    (hl : ∀ x ∈ l, x ∈ RankTwoAugmentedFrames.augmentedFrame q) :
    ∃ I : List (Fin 3), l = I.map (RankTwoAugmentedFrames.augmentedLine q) := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons x l ih =>
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (hl x (List.mem_cons_self))
    obtain ⟨I,hI⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    exact ⟨i :: I,by simp [hI,hi]⟩

local instance instDecRLL : DecidableEq RationalLine := Classical.decEq _
local instance instDecRLTwoL : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "res" => AugmentedPrismCaps.columnResidue

theorem mem_of_subset {V : Type*} (C : PreAbstractSimplicialComplex V) {s t : Finset V}
    (hs : s ∈ C) (hts : t ⊆ s) (ht : t.Nonempty) : t ∈ C :=
  (C.isRelLowerSet_faces hs).2 hts ht

theorem res_zero_of_bad (h : IntegralGL) (hbad : ¬Good (augmentedLine h 0).val) :
    res h 0 = 0 := AugmentedBadFaces.bad_augmentedLine_residue h 0 hbad

theorem good_fiber_shift (h : IntegralGL) (hb : res h 0 = 0) (i : Fin 3) (k l : ℤ) :
    Good (fiberLine h i k).val ↔ Good (fiberLine h i l).val := by
  rw [BadVertexSimplexNormalForm.fiberLine_good_iff h hb i k,
    BadVertexSimplexNormalForm.fiberLine_good_iff h hb i l]

theorem singleton_fiber_mem (h : IntegralGL) (i : Fin 3) (k : ℤ)
    (hg : Good (fiberLine h i k).val) :
    ({fiberLine h i k} : Finset RationalLine) ∈ badLink (augmentedLine h 0) := by
  refine ⟨⟨by simp,?_⟩,?_⟩
  · rw [Finset.singleton_union]
    exact fiber_edge_ambient h i k
  · intro L hL
    rw [Finset.mem_singleton] at hL
    exact hL ▸ hg

/-- A literal mixed triangle over two (possibly non-adjacent in the quotient frame) fibres. -/
theorem mixed_triple_mem (h : IntegralGL) (hb : res h 0 = 0) (i j : Fin 3) (hij : i ≠ j)
    (k l : ℤ) (hi : Good (fiberLine h i 0).val) (hj : Good (fiberLine h j 0).val) :
    ({fiberLine h i k,fiberLine h i (k+1),fiberLine h j l} : Finset RationalLine) ∈
      badLink (augmentedLine h 0) := by
  refine ⟨⟨by simp,?_⟩,?_⟩
  · rw [Finset.singleton_union,← BadVertexPrismSupport.mixedGL_frame h i j hij k l]
    exact augmentedFrame_mem _
  · intro L hL
    simp only [Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact (good_fiber_shift h hb i 0 _).mp hi
    · exact (good_fiber_shift h hb i 0 _).mp hi
    · exact (good_fiber_shift h hb j 0 _).mp hj

theorem coherent_triple_mem (h : IntegralGL) (hb : res h 0 = 0)
    (h0 : Good (fiberLine h 0 0).val) (h1 : Good (fiberLine h 1 0).val)
    (h2 : Good (fiberLine h 2 0).val) :
    ({fiberLine h 0 0,fiberLine h 1 0,fiberLine h 2 0} : Finset RationalLine) ∈
      badLink (augmentedLine h 0) := by
  have hX := (BadVertexSimplexNormalForm.fiberLine_good_iff h hb 0 0).mp h0
  have hY := (BadVertexSimplexNormalForm.fiberLine_good_iff h hb 1 0).mp h1
  have hZ := (BadVertexSimplexNormalForm.fiberLine_good_iff h hb 2 0).mp h2
  exact BadVertexPrismSupport.coherent_face_link h hb hX hY hZ (0,0)

theorem lift_finset_mem (h : IntegralGL) (hb : res h 0 = 0) (S : Finset (Fin 3)) (hS : S.Nonempty)
    (hgood : ∀ i ∈ S, Good (fiberLine h i 0).val) :
    S.image (fun i => fiberLine h i 0) ∈ badLink (augmentedLine h 0) := by
  classical
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  have hle : S.card ≤ 3 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ S
      _ = 3 := by simp
  have hcases : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hcases with hc | hc | hc
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hc
    rw [Finset.image_singleton]
    exact singleton_fiber_mem h a 0 (hgood a (by simp))
  · obtain ⟨a,c,hac,rfl⟩ := Finset.card_eq_two.mp hc
    have hm := mixed_triple_mem h hb a c hac 0 0 (hgood a (by simp)) (hgood c (by simp))
    refine mem_of_subset _ hm ?_ (by simp)
    intro x hx
    simp only [Finset.image_insert,Finset.image_singleton,Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  · obtain ⟨a,c,d,hac,had,hcd,rfl⟩ := Finset.card_eq_three.mp hc
    have hm := coherent_triple_mem h hb (hgood 0 (by fin_cases a <;> fin_cases c <;> fin_cases d <;> simp_all))
      (hgood 1 (by fin_cases a <;> fin_cases c <;> fin_cases d <;> simp_all))
      (hgood 2 (by fin_cases a <;> fin_cases c <;> fin_cases d <;> simp_all))
    refine mem_of_subset _ hm ?_ (by simp)
    intro x hx
    simp only [Finset.image_insert,Finset.image_singleton,Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢
    have key : ∀ t : Fin 3, fiberLine h t 0 = fiberLine h 0 0 ∨ fiberLine h t 0 = fiberLine h 1 0 ∨
        fiberLine h t 0 = fiberLine h 2 0 := by
      intro t; fin_cases t <;> simp
    rcases hx with rfl | rfl | rfl <;> exact key _

/-! ### Lifting chains of `Z` to chains of `L_b` -/

/-- Every simplex chain of the good quotient complex lifts to the link. -/
theorem lift_chain (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val) (n : ℕ)
    (hn : 1 ≤ n) {w : Chain RankTwoAugmentedFrames.RationalLine2}
    (hw : w ∈ chains (RankTwoGoodComplex.good (phi g)) n) :
    ∃ w' : Chain RationalLine, w' ∈ chains (badLink (augmentedLine g 0)) n ∧
      OrientedChainMap.map (vertex g) w' = w := by
  classical
  induction hw using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hnd : l.Nodup
    · have hl' : l.toFinset ∈ RankTwoGoodComplex.good (phi g) :=
        hl.resolve_left (fun he => by subst he; simp at hlen; omega)
      obtain ⟨_,q,hq⟩ := hl'.1
      obtain ⟨I,hI⟩ := exists_index_list q l (fun x hx => hq (List.mem_toFinset.mpr hx))
      subst hI
      have hInd : I.Nodup := hnd.of_map _
      have hIne : I ≠ [] := by
        rintro rfl
        simp at hlen; omega
      set h := g * blockGL q with hhd
      have hh : augmentedLine h 0 = augmentedLine g 0 := blockGL_line_zero g q
      have hgood : ∀ i ∈ I, Good (fiberLine h i 0).val := by
        intro i hi
        rw [good_block_iff g hbad q i 0]
        exact hl'.2 _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hi,rfl⟩))
      have hbad_h : ¬Good (augmentedLine h 0).val := by rw [hh]; exact hbad
      have hmem : (I.map (fun i => fiberLine h i 0)).toFinset ∈ badLink (augmentedLine h 0) := by
        have := lift_finset_mem h (res_zero_of_bad h hbad_h) I.toFinset
          (List.toFinset_nonempty_iff _ |>.mpr hIne) (fun i hi => hgood i (List.mem_toFinset.mp hi))
        convert this using 1
        ext x
        simp
      refine ⟨simplex (I.map (fun i => fiberLine h i 0)),?_,?_⟩
      · have := simplex_mem_chains (badLink (augmentedLine h 0)) (I.map (fun i => fiberLine h i 0))
          (Or.inr hmem)
        rw [hh] at this
        simpa only [List.length_map,← hlen] using this
      · rw [OrientedChainMap.map_simplex,List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact vertex_block g q i 0
    · refine ⟨0,(chains _ _).zero_mem,?_⟩
      rw [simplex_eq_zero_of_not_nodup l hnd,map_zero]
  | zero => exact ⟨0,(chains _ _).zero_mem,map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x',hx',hxe⟩ := hx
    obtain ⟨y',hy',hye⟩ := hy
    exact ⟨x'+y',(chains _ _).add_mem hx' hy',by rw [map_add,hxe,hye]⟩
  | smul q x _ hx =>
    obtain ⟨x',hx',hxe⟩ := hx
    exact ⟨q • x',(chains _ _).smul_mem q hx',by rw [map_smul,hxe]⟩

/-! ### The generator facts -/

theorem shearGL_zero : shearGL (0,0) = 1 := by
  apply Units.ext
  change shearMatrix (0,0) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearMatrix]

theorem affineBasis_zero (g : IntegralGL) : affineBasis g (0,0) = g := by
  simp [affineBasis,shearGL_zero]

theorem prismSphere_eq (g : IntegralGL) :
    AugmentedPrismCaps.prismSphere g =
      coherent g (0+1,0) - coherent g (0,0) - horizontalResidual g (0,0) := by
  have h := horizontal_identity g (0,0)
  rw [horizontalCap,affineBasis_zero,AugmentedPrismCaps.boundary_prismCap] at h
  rw [h]
  abel

theorem prismSphere_mem_chains (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hX : Good (xFiber g 0).val) (hY : Good (yFiber g 0).val) (hZ : Good (zFiber g 0).val) :
    AugmentedPrismCaps.prismSphere g ∈ chains (badLink (augmentedLine g 0)) 3 := by
  have hb := res_zero_of_bad g hbad
  have hX' := (BadVertexSimplexNormalForm.fiberLine_good_iff g hb 0 0).mp hX
  have hY' := (BadVertexSimplexNormalForm.fiberLine_good_iff g hb 1 0).mp hY
  have hZ' := (BadVertexSimplexNormalForm.fiberLine_good_iff g hb 2 0).mp hZ
  rw [prismSphere_eq]
  refine (chains _ _).sub_mem ((chains _ _).sub_mem ?_ ?_) ?_
  · exact BadVertexPrismSupport.coherent_mem_link g hb hX' hY' hZ' _
  · exact BadVertexPrismSupport.coherent_mem_link g hb hX' hY' hZ' _
  · exact BadVertexPrismSupport.MixedSpan_le_link g hb hX' hY' hZ' (horizontalResidual_mem g _)

theorem simplex_mem_chains_of_mem {V : Type*} (C : PreAbstractSimplicialComplex V)
    (xs : List V) (n : ℕ) (hlen : xs.length = n) (T : Finset V) (hT : T ∈ C)
    (he : ∀ x, x ∈ xs ↔ x ∈ T) : simplex xs ∈ chains C n := by
  classical
  have hf : xs.toFinset ∈ C := by
    have : xs.toFinset = T := by
      ext x
      simp [he x]
    rw [this]
    exact hT
  have := simplex_mem_chains C xs (Or.inr hf)
  rwa [hlen] at this

theorem tetraSphere_mem_chains (g : IntegralGL) (hbad : ¬Good (augmentedLine g 0).val)
    (hX : Good (xFiber g 0).val) (hY : Good (yFiber g 0).val) (k l : ℤ) :
    tetraSphere g k l ∈ chains (badLink (augmentedLine g 0)) 3 := by
  have hb := res_zero_of_bad g hbad
  have e1 : tetraSphere g k l =
      simplex [xFiber g (k+1),yFiber g l,yFiber g (l+1)] -
      simplex [xFiber g k,yFiber g l,yFiber g (l+1)] +
      simplex [xFiber g k,xFiber g (k+1),yFiber g (l+1)] -
      simplex [xFiber g k,xFiber g (k+1),yFiber g l] := by
    simp only [tetraSphere,boundary_cons,boundary_nil,map_sub,map_zero,cons_simplex,sub_zero]
    abel
  rw [e1]
  have m1 := mixed_triple_mem g hb 0 1 (by decide) k l hX hY
  have m2 := mixed_triple_mem g hb 0 1 (by decide) k (l+1) hX hY
  have m3 := mixed_triple_mem g hb 1 0 (by decide) l k hY hX
  have m4 := mixed_triple_mem g hb 1 0 (by decide) l (k+1) hY hX
  refine (chains _ _).sub_mem ((chains _ _).add_mem ((chains _ _).sub_mem ?_ ?_) ?_) ?_
  · exact simplex_mem_chains_of_mem _ _ 3 rfl _ m4 (fun x => by simp; tauto)
  · exact simplex_mem_chains_of_mem _ _ 3 rfl _ m3 (fun x => by simp; tauto)
  · exact simplex_mem_chains_of_mem _ _ 3 rfl _ m2 (fun x => by simp)
  · exact simplex_mem_chains_of_mem _ _ 3 rfl _ m1 (fun x => by simp)

/-- Every generator is a cycle of `chains L_b 3`. -/
theorem generator_mem (b : RationalLine) (hb : ¬Good b.val) {c : Chain RationalLine}
    (hc : c ∈ tetraSpheres b ∪ prismSpheres b) :
    c ∈ chains (badLink b) 3 ∧ boundary c = 0 := by
  rcases hc with ⟨g,k,l,rfl,hX,hY,rfl⟩ | ⟨g,rfl,hX,hY,hZ,rfl⟩
  · exact ⟨tetraSphere_mem_chains g hb hX hY k l,boundary_squared _⟩
  · exact ⟨prismSphere_mem_chains g hb hX hY hZ,AugmentedPrismCaps.boundary_prismSphere g⟩

theorem chains_four_eq_bot (b : RationalLine) (hb : ¬Good b.val) : chains (badLink b) 4 = ⊥ := by
  classical
  rw [eq_bot_iff]
  apply Submodule.span_le.mpr
  rintro _ ⟨l,hlen,hl,rfl⟩
  rw [SetLike.mem_coe,Submodule.mem_bot]
  by_contra hne
  have hnd : l.Nodup := by
    by_contra h
    exact hne (simplex_eq_zero_of_not_nodup l h)
  have hf : l.toFinset ∈ badLink b := hl.resolve_left (fun he => by subst he; simp at hlen)
  have hs := (mem_goodLink ambient _ _ _).mp hf
  have hcard : ({b} ∪ l.toFinset).card ≤ 4 := AugmentedBadFaces.ambient_card_le_four hs.2.1
  have hbl : b ∉ l.toFinset := fun hm => hb (hs.2.2 b hm)
  rw [Finset.singleton_union,Finset.card_insert_of_notMem hbl,List.toFinset_card_of_nodup hnd,
    hlen] at hcard
  omega

theorem exists_vertex (b : RationalLine) (hb : ¬Good b.val) :
    ∃ a : RationalLine, ({a} : Finset RationalLine) ∈ badLink b := by
  obtain ⟨g,rfl⟩ := RationalLineBasis.rationalLine_eq_augmentedLine b
  have hb0 := res_zero_of_bad g hb
  obtain ⟨j,hj⟩ := AugmentedBadFaces.exists_columnResidue_ne_zero g
  fin_cases j
  · exact absurd hb0 hj
  · exact ⟨_,singleton_fiber_mem g 0 0
      ((BadVertexSimplexNormalForm.fiberLine_good_iff g hb0 0 0).mpr hj)⟩
  · exact ⟨_,singleton_fiber_mem g 1 0
      ((BadVertexSimplexNormalForm.fiberLine_good_iff g hb0 1 0).mpr hj)⟩

end TernaryPeriodPolynomials.Argument.AppendixALink
