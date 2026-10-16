module

public import TernaryPeriodPolynomials.Building.Ambient.HeightFiltration
public import TernaryPeriodPolynomials.Building.Ambient.DependentTriangles
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainJoin

@[expose] public section


noncomputable section
namespace TernaryPoly.AmbientHighAdditiveElimination
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
open OrientedListChains OrientedChainJoin AmbientHeightFiltration AmbientDependentTriangles

local instance : DecidableEq RationalLine := fun _ _ => Classical.propDecidable _

/-- Every cone over a distinct pair of core lines has full rational rank. -/
theorem core_pair_cone_full_rank (g : IntegralGL) (i j : Fin 3) (hij : i ≠ j) :
    Module.finrank ℚ (faceSpan
      [augmentedLine g 2,augmentedLine g (coreIndex i),augmentedLine g (coreIndex j)].toFinset) = 3 := by
  classical
  obtain ⟨h,h0,h1,h2⟩ := core_pair_complement_basis g i j hij
  apply le_antisymm (faceSpan_finrank_le_three _)
  have he : [augmentedLine g 2,augmentedLine g (coreIndex i),augmentedLine g (coreIndex j)].toFinset =
      [augmentedLine h 0,augmentedLine h 1,augmentedLine h 2].toFinset := by
    ext L
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false,h0,h1,h2]
    tauto
  rw [he]
  have hfe : [augmentedLine h 0,augmentedLine h 1,augmentedLine h 2].toFinset =
      @List.toFinset RationalLine (fun a b => Subtype.instDecidableEq a b)
        [augmentedLine h 0,augmentedLine h 1,augmentedLine h 2] := by
    ext L
    simp only [List.mem_toFinset]
  rw [hfe]
  exact basis_face_finrank_ge h

/-- Cone boundaries over core edges consist of actual independent triangles. -/
theorem core_boundary_cone_reduced (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (g : IntegralGL) (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hcore : l.Perm (coreList g))
    (hallowed : Allowed (bounded F N) (augmentedLine g 2 :: l)) :
    cons (augmentedLine g 2) (boundary (simplex l)) ∈ reducedTriangles F N := by
  classical
  apply boundary_simplex_mem ((reducedTriangles F N).comap (cons (augmentedLine g 2))) l
  intro m hm hmlen
  have hm2 : m.length = 2 := by omega
  obtain ⟨u,v,rfl⟩ := List.length_eq_two.mp hm2
  have huv : u ≠ v := by simpa using hm.nodup hn
  have hu : u ∈ coreList g := hcore.mem_iff.mp (hm.subset (by simp))
  have hv : v ∈ coreList g := hcore.mem_iff.mp (hm.subset (by simp))
  have core_mem (L : RationalLine) (hL : L ∈ coreList g) :
      ∃ i : Fin 3, L = augmentedLine g (coreIndex i) := by
    simp only [coreList,List.mem_cons,List.not_mem_nil,or_false] at hL
    rcases hL with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i,rfl⟩ := core_mem u hu
  obtain ⟨j,rfl⟩ := core_mem v hv
  have hij : i ≠ j := fun he => huv (congrArg (fun k => augmentedLine g (coreIndex k)) he)
  change cons (augmentedLine g 2)
    (simplex [augmentedLine g (coreIndex i),augmentedLine g (coreIndex j)]) ∈ reducedTriangles F N
  rw [cons_simplex]
  exact simplex_mem_reducedTriangles F N _ rfl
    (allowed_sublist (bounded F N) hallowed (hm.cons_cons _))
    (Or.inl (core_pair_cone_full_rank g i j hij))

/-- A single high dependent triangle is its cone boundary plus independent faces. -/
theorem dependent_simplex_elimination (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ)
    (hN : 0 < N) (l : List RationalLine) (hlen : l.length = 3) (hn : l.Nodup)
    (hl : Allowed (bounded F N) l) (hdep : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2)
    (hhigh : ¬ ∀ L ∈ l, height F L < N) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ simplex l = boundary t + r := by
  classical
  obtain ⟨ha,hb⟩ := (allowed_bounded_iff F N l).mp hl
  have hf : l.toFinset ∈ ambient := ha.resolve_left (fun he => by subst l; simp at hlen)
  have ht := dependent_triangle_core l hlen hn
  have hfe : l.toFinset = @List.toFinset RationalLine
      (fun a b => Subtype.instDecidableEq a b) l := by
    ext L
    simp only [List.mem_toFinset]
  obtain ⟨g,hg⟩ := ht (by rwa [← hfe]) (by rwa [← hfe])
  push Not at hhigh
  obtain ⟨L,hL,hLN⟩ := hhigh
  have hLcore : L ∈ coreList g := hg.mem_iff.mp hL
  have hidx : ∃ i : Fin 3, L = augmentedLine g (coreIndex i) := by
    simp only [coreList,List.mem_cons,List.not_mem_nil,or_false] at hLcore
    rcases hLcore with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨i,rfl⟩ := hidx
  obtain ⟨g',hfix,hlow,htet⟩ := exists_low_complement F g i (hN.trans_le hLN)
  have hlowN : height F (augmentedLine g' 2) < N := hlow.trans_le (hb _ hL)
  have hcore : l.Perm (coreList g') := by
    have he : coreList g' = coreList g := by
      have h0 : augmentedLine g' 0 = augmentedLine g 0 := hfix 0
      have h1 : augmentedLine g' 1 = augmentedLine g 1 := hfix 1
      have h3 : augmentedLine g' 3 = augmentedLine g 3 := hfix 2
      simp only [coreList,h0,h1,h3]
    rwa [he]
  have hal : Allowed (bounded F N) (augmentedLine g' 2 :: l) := by
    apply (allowed_bounded_iff F N _).mpr
    constructor
    · apply Or.inr
      convert htet using 1
      ext M
      simp only [List.mem_toFinset,List.mem_cons,Finset.mem_insert,Finset.mem_singleton]
      rw [hg.mem_iff]
      simp only [List.mem_cons,List.not_mem_nil,false_or,or_comm,or_left_comm]
    · intro M hM
      rcases List.mem_cons.mp hM with rfl | hM
      · exact hlowN.le
      · exact hb M hM
  refine ⟨cons (augmentedLine g' 2) (simplex l),
    cons (augmentedLine g' 2) (boundary (simplex l)),?_,
    core_boundary_cone_reduced F N g' l hlen hn hcore hal,?_⟩
  · rw [cons_simplex]
    simpa only [List.length_cons,hlen] using simplex_mem_chains (bounded F N) _ hal
  · rw [boundary_cons_chain]
    abel

/-- Finite span induction removes every high additive triangle without any cycle premise. -/
theorem eliminate_high_additive (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    {c : Chain RationalLine} (hc : c ∈ chains (bounded F N) 3) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ c = boundary t + r := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases hn : l.Nodup
    · by_cases hr : ReducedTriangle F N l
      · exact ⟨0,simplex l,(chains (bounded F N) 4).zero_mem,
          simplex_mem_reducedTriangles F N l hlen hl hr,by simp⟩
      · have hd : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2 := by
          have hupper := faceSpan_finrank_le_three l.toFinset
          have hne : Module.finrank ℚ (faceSpan l.toFinset) ≠ 3 := fun he => hr (Or.inl he)
          omega
        exact dependent_simplex_elimination F N hN l hlen hn hl hd (fun he => hr (Or.inr he))
    · rw [simplex_eq_zero_of_not_nodup l hn]
      exact ⟨0,0,(chains (bounded F N) 4).zero_mem,(reducedTriangles F N).zero_mem,by simp⟩
  | zero => exact ⟨0,0,(chains (bounded F N) 4).zero_mem,(reducedTriangles F N).zero_mem,by simp⟩
  | add c d hc hd ihc ihd =>
    obtain ⟨t,r,ht,hr,he⟩ := ihc
    obtain ⟨t',r',ht',hr',he'⟩ := ihd
    refine ⟨t+t',r+r',(chains (bounded F N) 4).add_mem ht ht',
      (reducedTriangles F N).add_mem hr hr',?_⟩
    rw [map_add,he,he']
    abel
  | smul q c hc ih =>
    obtain ⟨t,r,ht,hr,he⟩ := ih
    refine ⟨q • t,q • r,(chains (bounded F N) 4).smul_mem q ht,
      (reducedTriangles F N).smul_mem q hr,?_⟩
    rw [map_smul,he,smul_add]

/-- The reduced chain has exactly the original boundary, in particular preserving cycles. -/
theorem eliminate_high_additive_preserves_boundary
    (F : IntegralVector →ₗ[ℤ] ℤ) (N : ℕ) (hN : 0 < N)
    {c : Chain RationalLine} (hc : c ∈ chains (bounded F N) 3) :
    ∃ t r : Chain RationalLine, t ∈ chains (bounded F N) 4 ∧
      r ∈ reducedTriangles F N ∧ c = boundary t + r ∧ boundary r = boundary c := by
  obtain ⟨t,r,ht,hr,he⟩ := eliminate_high_additive F N hN hc
  refine ⟨t,r,ht,hr,he,?_⟩
  rw [he,map_add,boundary_squared,zero_add]

end TernaryPoly.AmbientHighAdditiveElimination
