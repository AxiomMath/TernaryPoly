module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Link.Lift
public import TernaryPeriodPolynomials.Building.Integer.PathChains
public import TernaryPeriodPolynomials.Building.BadVertex.MixedBlocks
public import TernaryPeriodPolynomials.Building.OrientedChain.SimplexCoefficient

@[expose] public section


/-!
# Lemma A.1: the fibre paths `P_u`

Formalized by Claude Sonnet 5.5.
Paper: Appendix A.2: over `u ∈ Z` the lifts `u_k = u_0 + k b` form a bi-infinite path
`P_u` with edges `[u_k,u_{k+1}]`, which is contractible.

In the chart `h` (an integral basis with first line `b`) the fibre over the standard quotient
vertex `augmentedLine 1 0` is `k ↦ xFiber h k`.  The chains of `L_b` lying over that vertex are
exactly the images of path chains (`project_x_mem`), and the path complex is acyclic.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixALink

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.AugmentedFrameComplex
  TernaryPoly.OrientedListChains TernaryPoly.GoodLinkExtraction TernaryPoly.CoherentPrismReduction
  TernaryPoly.BadVertexProjection TernaryPoly.OrientedImageFaceProjection
  TernaryPoly.OrientedImageFaceBoundary TernaryPoly.OrientedImageFaceDecomposition

theorem exists_index_of_mem_frame (f : IntegralGL) {x : RationalLine}
    (hx : x ∈ augmentedFrame f) : ∃ i : Fin 4, augmentedLine f i = x := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
  exact ⟨i,hi⟩

local instance instDecRLF : DecidableEq RationalLine := Classical.decEq _
local instance instDecRLTwoF : DecidableEq RankTwoAugmentedFrames.RationalLine2 := Classical.decEq _
local notation "res" => AugmentedPrismCaps.columnResidue

/-- The standard first quotient vertex. -/
abbrev A0 : RankTwoAugmentedFrames.RationalLine2 := RankTwoAugmentedFrames.augmentedLine 1 0

/-! ### Consecutive fibre points -/

theorem fiber_pair_mem (h : IntegralGL) (hb : res h 0 = 0) (i : Fin 3)
    (hi : Good (fiberLine h i 0).val) (n : ℤ) :
    ({fiberLine h i n,fiberLine h i (n+1)} : Finset RationalLine) ∈
      badLink (augmentedLine h 0) := by
  obtain ⟨j,hij⟩ : ∃ j : Fin 3, i ≠ j := ⟨i+1,by fin_cases i <;> decide⟩
  refine ⟨⟨by simp,?_⟩,?_⟩
  · apply subset_augmentedFrame_mem (h * mixedGL i j hij n 0) (by simp)
    rw [BadVertexPrismSupport.mixedGL_frame]
    intro x hx
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert] at hx ⊢
    tauto
  · intro L hL
    simp only [Finset.mem_insert,Finset.mem_singleton] at hL
    rcases hL with rfl | rfl <;> exact (good_fiber_shift h hb i 0 _).mp hi

/-- Linear independence of the first two columns of an integral basis. -/
theorem col_combination_zero (h : IntegralGL) (c d : ℤ)
    (hz : c • h.val.col 0 + d • h.val.col 1 = 0) : c = 0 ∧ d = 0 := by
  have hm : h.val.mulVec (![c,d,0] : Fin 3 → ℤ) = 0 := by
    rw [← hz]
    funext r
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,Matrix.col]
    ring
  have hu : (![c,d,0] : Fin 3 → ℤ) = 0 := by
    have := congrArg (fun v => h⁻¹.val.mulVec v) hm
    simpa only [Matrix.mulVec_mulVec,← Units.val_mul,inv_mul_cancel,Units.val_one,
      Matrix.one_mulVec,Matrix.mulVec_zero] using this
  exact ⟨congrFun hu 0,congrFun hu 1⟩

theorem fiberCoefficient_zero_col (h : IntegralGL) :
    h.val.mulVec (fiberCoefficient 0 0) = h.val.col 1 := by
  funext r
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,fiberCoefficient,Matrix.col]

/-- Two charts with the same first line: consecutive points of a fibre of one chart are
consecutive points of the `x`-fibre of the other. -/
theorem fiber_step_compare (g' h : IntegralGL)
    (hb : augmentedLine g' 0 = augmentedLine h 0) (a : Fin 3) (n k k' : ℤ)
    (h1 : fiberLine g' a n = xFiber h k) (h2 : fiberLine g' a (n+1) = xFiber h k') :
    k' = k+1 ∨ k = k'+1 := by
  have hs1 : Submodule.span ℚ {rationalVector (g'.val.mulVec (fiberCoefficient a n))} =
      Submodule.span ℚ {rationalVector (h.val.mulVec (fiberCoefficient 0 k))} := by
    rw [← fiberLine_val,← fiberLine_val]
    exact congrArg Subtype.val h1
  have hs2 : Submodule.span ℚ {rationalVector (g'.val.mulVec (fiberCoefficient a (n+1)))} =
      Submodule.span ℚ {rationalVector (h.val.mulVec (fiberCoefficient 0 k'))} := by
    rw [← fiberLine_val,← fiberLine_val]
    exact congrArg Subtype.val h2
  obtain ⟨ε,hε,he1⟩ := BadVertexMixedCharts.primitive_span_sign
    (BadVertexMixedCharts.fiberVector_primitive g' a n)
    (BadVertexMixedCharts.fiberVector_primitive h 0 k) hs1
  obtain ⟨ε',hε',he2⟩ := BadVertexMixedCharts.primitive_span_sign
    (BadVertexMixedCharts.fiberVector_primitive g' a (n+1))
    (BadVertexMixedCharts.fiberVector_primitive h 0 k') hs2
  obtain ⟨ε0,hε0,hcol⟩ := BadVertexMixedCharts.first_column_sign h g' hb
  have hstep : g'.val.mulVec (fiberCoefficient a (n+1)) =
      g'.val.mulVec (fiberCoefficient a n) + g'.val.col 0 := by
    rw [BadVertexMixedCharts.fiberVector_affine g' a (n+1),
      BadVertexMixedCharts.fiberVector_affine g' a n,add_smul,one_smul]
    abel
  have hk : h.val.mulVec (fiberCoefficient 0 k) =
      h.val.col 1 + k • h.val.col 0 := by
    rw [BadVertexMixedCharts.fiberVector_affine h 0 k,fiberCoefficient_zero_col]
  have hk' : h.val.mulVec (fiberCoefficient 0 k') =
      h.val.col 1 + k' • h.val.col 0 := by
    rw [BadVertexMixedCharts.fiberVector_affine h 0 k',fiberCoefficient_zero_col]
  rw [he2,he1,hcol,hk,hk'] at hstep
  have hz : (ε' * k' - ε * k - ε0) • h.val.col 0 + (ε' - ε) • h.val.col 1 = 0 := by
    funext r
    have := congrFun hstep r
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at this ⊢
    linear_combination this
  obtain ⟨c0,c1⟩ := col_combination_zero h _ _ hz
  have hee : ε' = ε := by linarith
  subst hee
  rcases hε' with rfl | rfl <;> rcases hε0 with rfl | rfl <;> omega

theorem nf_table : ∀ (i : Fin 4) (j m : Fin 3), j ≠ m →
    BadVertexSimplexNormalForm.normalFiber i j = BadVertexSimplexNormalForm.normalFiber i m →
    BadVertexSimplexNormalForm.normalHeight i m = BadVertexSimplexNormalForm.normalHeight i j + 1 ∨
    BadVertexSimplexNormalForm.normalHeight i j = BadVertexSimplexNormalForm.normalHeight i m + 1 := by
  decide +kernel

/-- Two distinct Good neighbours of `b` in the same fibre which are adjacent are consecutive. -/
theorem fiber_edge_consecutive (h : IntegralGL) (k k' : ℤ) (hne : k ≠ k')
    (hf : ({xFiber h k,xFiber h k'} : Finset RationalLine) ∈ badLink (augmentedLine h 0)) :
    k' = k+1 ∨ k = k'+1 := by
  obtain ⟨_,f,hsub⟩ := hf.1.2
  have hmem (x : RationalLine) (hx : x ∈ ({augmentedLine h 0} ∪ {xFiber h k,xFiber h k'} :
      Finset RationalLine)) : ∃ i : Fin 4, augmentedLine f i = x :=
    exists_index_of_mem_frame f (hsub hx)
  obtain ⟨i0,hi0⟩ := hmem (augmentedLine h 0) (by simp)
  obtain ⟨j,hj⟩ := hmem (xFiber h k) (by simp)
  obtain ⟨m,hm⟩ := hmem (xFiber h k') (by simp)
  have hne_k : xFiber h k ≠ augmentedLine h 0 := fiber_ne_base h 0 k
  have hne_k' : xFiber h k' ≠ augmentedLine h 0 := fiber_ne_base h 0 k'
  have hji : j ≠ i0 := by
    intro e; apply hne_k; rw [← hj,← hi0,e]
  have hmi : m ≠ i0 := by
    intro e; apply hne_k'; rw [← hm,← hi0,e]
  have hjm : j ≠ m := by
    intro e
    apply hne
    have : xFiber h k = xFiber h k' := by rw [← hj,← hm,e]
    exact BadVertexFibers.prism_fiber_injective h 0 this
  obtain ⟨jj,hjj⟩ := (BadVertexSimplexNormalForm.remainingIndex_range i0 j).mpr hji
  obtain ⟨mm,hmm⟩ := (BadVertexSimplexNormalForm.remainingIndex_range i0 m).mpr hmi
  let g' := f * templateChange i0
  have hb' : augmentedLine g' 0 = augmentedLine h 0 :=
    (templateChange_line f i0).trans hi0
  have eq1 : xFiber h k = fiberLine g' (BadVertexSimplexNormalForm.normalFiber i0 jj)
      (BadVertexSimplexNormalForm.normalHeight i0 jj) := by
    rw [BadVertexSimplexNormalForm.normal_line,hjj,hj]
  have eq2 : xFiber h k' = fiberLine g' (BadVertexSimplexNormalForm.normalFiber i0 mm)
      (BadVertexSimplexNormalForm.normalHeight i0 mm) := by
    rw [BadVertexSimplexNormalForm.normal_line,hmm,hm]
  have hjm' : jj ≠ mm := by
    intro e
    apply hjm
    rw [← hjj,← hmm,e]
  -- the quotient vertices agree
  have hv1 := BadVertexProjectionChange.vertex_change h g' hb' (xFiber h k) hne_k
  have hv2 := BadVertexProjectionChange.vertex_change h g' hb' (xFiber h k') hne_k'
  have hq : BadVertexProjectionChange.quotientChange h g' hb'
        (RankTwoAugmentedFrames.augmentedLine 1 (BadVertexSimplexNormalForm.normalFiber i0 jj)) =
      BadVertexProjectionChange.quotientChange h g' hb'
        (RankTwoAugmentedFrames.augmentedLine 1 (BadVertexSimplexNormalForm.normalFiber i0 mm)) := by
    rw [← BadVertexFibers.prism_fiber_vertex g' _ (BadVertexSimplexNormalForm.normalHeight i0 jj),
      ← BadVertexFibers.prism_fiber_vertex g' _ (BadVertexSimplexNormalForm.normalHeight i0 mm),
      ← eq1,← eq2,← hv1,← hv2]
    simp only [xFiber,BadVertexFibers.prism_fiber_vertex]
  have hnf := RankTwoAugmentedFrames.augmentedLine_injective 1
    ((BadVertexProjectionChange.quotientChange h g' hb').injective hq)
  rcases nf_table i0 jj mm hjm' hnf with ht | ht
  · -- height of mm is height of jj plus one
    have h2 : fiberLine g' (BadVertexSimplexNormalForm.normalFiber i0 jj)
        (BadVertexSimplexNormalForm.normalHeight i0 jj + 1) = xFiber h k' := by
      rw [← ht,hnf,← eq2]
    exact fiber_step_compare g' h hb' _ _ k k' eq1.symm h2
  · have h2 : fiberLine g' (BadVertexSimplexNormalForm.normalFiber i0 mm)
        (BadVertexSimplexNormalForm.normalHeight i0 mm + 1) = xFiber h k := by
      rw [← ht,← hnf,← eq1]
    exact (fiber_step_compare g' h hb' _ _ k' k eq2.symm h2).symm

/-! ### Chains over the first quotient vertex -/

/-- Relabel path chains into the fibre over the first quotient vertex. -/
abbrev xmap (h : IntegralGL) : Chain ℤ →ₗ[ℚ] Chain RationalLine :=
  OrientedChainMap.map (xFiber h)

theorem mapsFaces_x (h : IntegralGL) (hb : res h 0 = 0) (hx : Good (xFiber h 0).val) :
    OrientedChainMap.MapsFaces (xFiber h) IntegerPathChains.pathComplex
      (badLink (augmentedLine h 0)) := by
  classical
  intro s hs
  obtain ⟨hne,n,hn⟩ := hs
  have hm := fiber_pair_mem h hb 0 hx n
  refine mem_of_subset _ hm ?_ (hne.image _)
  intro y hy
  obtain ⟨m,hm',rfl⟩ := Finset.mem_image.mp hy
  have := hn hm'
  simp only [Finset.mem_insert,Finset.mem_singleton] at this ⊢
  rcases this with rfl | rfl <;> simp

theorem exists_fiber (h : IntegralGL) (hbad_h : ¬Good (augmentedLine h 0).val) (i : Fin 3)
    (Q : RationalLine) (hQ : ({Q} : Finset RationalLine) ∈ badLink (augmentedLine h 0))
    (hv : vertex h Q = RankTwoAugmentedFrames.augmentedLine 1 i) :
    ∃ k, fiberLine h i k = Q := by
  have hne : Q ≠ augmentedLine h 0 :=
    BadVertexProjectionChange.good_ne_base h hbad_h Q (hQ.2 Q (by simp))
  have he : ({augmentedLine h 0,Q} : Finset RationalLine) ∈ ambient := by
    have := hQ.1.2
    rwa [Finset.singleton_union] at this
  obtain ⟨k,hk,_⟩ := BadVertexFibers.prism_fiber_existsUnique h i Q hne (by convert he) hv
  exact ⟨k,hk⟩

theorem singleton_mem_of_mem {C : PreAbstractSimplicialComplex RationalLine}
    {s : Finset RationalLine} (hs : s ∈ C) {Q : RationalLine} (hQ : Q ∈ s) :
    ({Q} : Finset RationalLine) ∈ C :=
  mem_of_subset C hs (by simpa using hQ) (by simp)

theorem pathAllowed_one (k : ℤ) : Allowed IntegerPathChains.pathComplex [k] := by
  classical
  refine Or.inr ⟨by simp,k,?_⟩
  intro x hx
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  simp_all

theorem pathAllowed_two (k k' : ℤ) (hk : k' = k+1 ∨ k = k'+1) :
    Allowed IntegerPathChains.pathComplex [k,k'] := by
  classical
  rcases hk with rfl | rfl
  · refine Or.inr ⟨by simp,k,?_⟩
    intro x hx
    simp at hx ⊢
    omega
  · refine Or.inr ⟨by simp,k',?_⟩
    intro x hx
    simp at hx ⊢
    omega

theorem project_x_mem (h : IntegralGL) (hbad_h : ¬Good (augmentedLine h 0).val) (n : ℕ)
    (hn : n = 1 ∨ n = 2) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink (augmentedLine h 0)) n) :
    project (vertex h) {A0} c ∈
      (chains IntegerPathChains.pathComplex n).map (xmap h) := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    rw [project_simplex]
    by_cases he : imageFace (vertex h) l = {A0}
    · rw [ite_eq_left he]
      by_cases hnd : l.Nodup
      · have hlf : l.toFinset ∈ badLink (augmentedLine h 0) :=
          hl.resolve_left (fun e => by subst e; simp at hlen; omega)
        have hover : ∀ Q ∈ l, vertex h Q = A0 := by
          intro Q hQ
          have : vertex h Q ∈ imageFace (vertex h) l :=
            List.mem_toFinset.mpr (List.mem_map.mpr ⟨Q,hQ,rfl⟩)
          rw [he] at this
          exact Finset.mem_singleton.mp this
        have hex : ∀ Q ∈ l, ∃ k, xFiber h k = Q := fun Q hQ =>
          exists_fiber h hbad_h 0 Q (singleton_mem_of_mem hlf (List.mem_toFinset.mpr hQ))
            (hover Q hQ)
        rcases hn with rfl | rfl
        · obtain ⟨Q,rfl⟩ := List.length_eq_one_iff.mp hlen
          obtain ⟨k,rfl⟩ := hex Q (by simp)
          refine ⟨simplex [k],?_,?_⟩
          · have := simplex_mem_chains IntegerPathChains.pathComplex [k] (pathAllowed_one k)
            simpa using this
          · simp
        · obtain ⟨Q,R,rfl⟩ := List.length_eq_two.mp hlen
          obtain ⟨k,rfl⟩ := hex Q (by simp)
          obtain ⟨k',rfl⟩ := hex R (by simp)
          have hkk : k ≠ k' := by
            rintro rfl
            simp at hnd
          have hpair : ({xFiber h k,xFiber h k'} : Finset RationalLine) ∈
              badLink (augmentedLine h 0) := by
            convert hlf using 1
            ext x
            simp
          have hc2 := fiber_edge_consecutive h k k' hkk hpair
          refine ⟨simplex [k,k'],?_,?_⟩
          · have := simplex_mem_chains IntegerPathChains.pathComplex [k,k'] (pathAllowed_two k k' hc2)
            simpa using this
          · simp
      · rw [simplex_eq_zero_of_not_nodup l hnd]
        exact Submodule.zero_mem _
    · rw [ite_eq_right he]
      exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [map_smul]; exact Submodule.smul_mem _ q hx

/-- `∂` of a chain over a single quotient vertex stays over that vertex. -/
theorem boundary_simplex_project_single {V W : Type*} (f : V → W) (w : W) (l : List V)
    (hl : imageFace f l = {w}) (hlen : 2 ≤ l.length) :
    project f {w} (boundary (simplex l)) = boundary (simplex l) := by
  classical
  have hmem := boundary_simplex_mem (LinearMap.eqLocus (project f {w}) LinearMap.id) l (by
    intro m hm hmlen
    rw [LinearMap.mem_eqLocus]
    have hsub : imageFace f m ⊆ {w} := by
      have := imageFace_sublist f hm
      rwa [hl] at this
    have hne : (imageFace f m).Nonempty := by
      cases m with
      | nil => simp at hmlen; omega
      | cons x m' =>
        exact ⟨f x,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,List.mem_cons_self,rfl⟩)⟩
    have : imageFace f m = {w} := (hne.subset_singleton_iff).mp hsub
    simp [project_simplex,this])
  exact hmem

theorem boundary_project_single {V W : Type*} (f : V → W) (w : W)
    (C : PreAbstractSimplicialComplex V) (n : ℕ) (hn : 2 ≤ n) {c : Chain V}
    (hc : c ∈ chains C n) :
    boundary (project f {w} c) = project f {w} (boundary (project f {w} c)) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    rw [project_simplex]
    by_cases he : imageFace f l = {w}
    · rw [ite_eq_left he]
      exact (boundary_simplex_project_single f w l he (by omega)).symm
    · rw [ite_eq_right he]; simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact congrArg₂ _ hx hy
  | smul q x _ hx =>
    simp only [map_smul]
    exact congrArg _ hx

/-- Path chains over one vertex: the augmentation is read off the projected chain. -/
theorem map_const_vertices {W : Type*} (A : W) (V : IntegerPathChains.Vertices) :
    OrientedChainMap.map (fun _ : ℤ => A) V.val =
      IntegerPathChains.augmentation V • simplex [A] := by
  obtain ⟨z,rfl⟩ := IntegerPathChains.vertexEquiv.surjective V
  change OrientedChainMap.map (fun _ : ℤ => A) (IntegerPathChains.vertexTransport z).val =
    IntegerPathChains.augmentation (IntegerPathChains.vertexTransport z) • simplex [A]
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add,Submodule.coe_add,add_smul,hx,hy]
  | single n q =>
    rw [IntegerPathChains.vertexTransport_single]
    simp only [Submodule.coe_smul,map_smul]
    have h1 : (IntegerPathChains.vertexChain n).val = simplex [n] := rfl
    have h2 : IntegerPathChains.augmentation (IntegerPathChains.vertexChain n) = 1 := by
      simp [IntegerPathChains.augmentation]
    rw [h1,OrientedChainMap.map_simplex,h2]
    simp

theorem xmap_vertex_projection (h : IntegralGL) (V : IntegerPathChains.Vertices) :
    OrientedChainMap.map (vertex h) (xmap h V.val) =
      IntegerPathChains.augmentation V • simplex [A0] := by
  rw [OrientedChainMap.map_comp_apply]
  have : (vertex h ∘ xFiber h) = fun _ : ℤ => A0 := by
    funext k
    exact BadVertexFibers.prism_fiber_vertex h 0 k
  rw [this]
  exact map_const_vertices A0 V

/-- Reduced degree-zero exactness above one quotient vertex. -/
theorem vertex_component_fill (h : IntegralGL) (hbad_h : ¬Good (augmentedLine h 0).val)
    (hx : Good (xFiber h 0).val) {c : Chain RationalLine}
    (hc : c ∈ chains (badLink (augmentedLine h 0)) 1)
    (hz : OrientedChainMap.map (vertex h) c = 0) :
    ∃ t ∈ chains (badLink (augmentedLine h 0)) 2,
      boundary t = project (vertex h) {A0} c := by
  have hb := res_zero_of_bad h hbad_h
  obtain ⟨V,hV,hVe⟩ := Submodule.mem_map.mp (project_x_mem h hbad_h 1 (Or.inl rfl) hc)
  have hzero : OrientedChainMap.map (vertex h) (project (vertex h) {A0} c) = 0 :=
    map_project_eq_zero _ _ hz
  rw [← hVe] at hzero
  have hz2 := xmap_vertex_projection h ⟨V,hV⟩
  change OrientedChainMap.map (vertex h) (xmap h V) =
    IntegerPathChains.augmentation ⟨V,hV⟩ • simplex [A0] at hz2
  rw [hzero] at hz2
  have haug : IntegerPathChains.augmentation ⟨V,hV⟩ = 0 := by
    have := (OrientedSimplexCoefficient.scalar_simplex_eq_zero_iff [A0] (by simp) _).mp hz2.symm
    exact this
  have hker : (⟨V,hV⟩ : IntegerPathChains.Vertices) ∈
      LinearMap.ker IntegerPathChains.augmentation := LinearMap.mem_ker.mpr haug
  rw [IntegerPathChains.ker_augmentation_eq_range_differential] at hker
  obtain ⟨E,hE⟩ := hker
  refine ⟨xmap h E.val,?_,?_⟩
  · exact OrientedChainMap.map_mem_chains _ _ _ (mapsFaces_x h hb hx) 2 E.property
  · rw [← hVe,OrientedChainMap.boundary_map]
    congr 1
    exact congrArg Subtype.val hE

/-- Above one quotient vertex a one-cycle of fibre edges vanishes: the path has no cycles. -/
theorem fiber_cycle_zero (h : IntegralGL) (hbad_h : ¬Good (augmentedLine h 0).val)
    {c : Chain RationalLine}
    (hc : c ∈ chains (badLink (augmentedLine h 0)) 2)
    (him : c ∈ imageBounded (vertex h) 1) (hd : boundary c = 0) :
    project (vertex h) {A0} c = 0 := by
  have hb := res_zero_of_bad h hbad_h
  have hcard : ({A0} : Finset RankTwoAugmentedFrames.RationalLine2).card = 1 := rfl
  have h1 : project (vertex h) {A0} (boundary (project (vertex h) {A0} c)) = 0 := by
    have := project_boundary_project_eq_zero (vertex h) {A0} (by rw [hcard]; exact him) hd
    exact this
  have h2 := boundary_project_single (vertex h) A0 (badLink (augmentedLine h 0)) 2 le_rfl hc
  rw [h1] at h2
  obtain ⟨E,hE,hEe⟩ := Submodule.mem_map.mp (project_x_mem h hbad_h 2 (Or.inr rfl) hc)
  rw [← hEe] at h2
  rw [OrientedChainMap.boundary_map] at h2
  have hinj := OrientedChainMap.map_injective (xFiber h) (BadVertexFibers.prism_fiber_injective h 0)
  have hbd : boundary E = 0 := by
    apply hinj
    rw [h2, map_zero]
  have hE0 : (⟨E,hE⟩ : IntegerPathChains.Edges) = 0 := by
    apply IntegerPathChains.differential_injective
    rw [map_zero]
    exact Subtype.ext hbd
  rw [← hEe]
  have : E = 0 := congrArg Subtype.val hE0
  rw [this, map_zero]

end TernaryPeriodPolynomials.Argument.AppendixALink
