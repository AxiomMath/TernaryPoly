module

public import TernaryPeriodPolynomials.Building.Proper.PlaneComplex
public import TernaryPeriodPolynomials.Building.Span.ChainComparison
public import TernaryPeriodPolynomials.Building.OrientedChain.ChainProjection
public import TernaryPeriodPolynomials.Building.OrientedChain.BadFaceDecomposition

@[expose] public section


noncomputable section
namespace TernaryPoly.ProperSpanProjection
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains OrientedChainJoin
open OrientedChainProjection OrientedBadFaceDecomposition SpanChainComparison ProperPlaneComplex
local instance : DecidableEq RationalLine := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The exact rational span of an ordered simplex is invariant under permutation. -/
theorem faceSpan_perm {l m : List RationalLine} (h : l.Perm m) :
    faceSpan l.toFinset = faceSpan m.toFinset := by
  have he : l.toFinset = m.toFinset := by ext L; simp only [List.mem_toFinset,h.mem_iff]
  rw [he]

/-- Literal projection onto the edges whose exact rational span is the specified subspace. -/
def planeProjection (P : RationalSubspace) : Chain RationalLine →ₗ[ℚ] Chain RationalLine :=
  filter (fun l => faceSpan l.toFinset = P) (fun h => by dsimp only; rw [faceSpan_perm h])

theorem planeProjection_simplex (P : RationalSubspace) (l : List RationalLine) :
    planeProjection P (simplex l) = if faceSpan l.toFinset = P then simplex l else 0 := by
  classical
  have he := filter_simplex (fun m => faceSpan m.toFinset = P)
    (fun h => by dsimp only; rw [faceSpan_perm h]) l
  convert he using 1
  · rfl
  · split_ifs <;> rfl

/-- Each exact-span component retains actual Good support in the specified plane. -/
theorem planeProjection_mem (P : RationalSubspace) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains good n) :
    planeProjection P c ∈ chains (planeComplex P) n := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    by_cases he : faceSpan l.toFinset = P
    · rw [planeProjection_simplex,ite_eq_left he]
      have ha : Allowed (planeComplex P) l := by
        rcases hl with rfl | hl
        · exact Or.inl rfl
        · refine Or.inr ⟨hl,?_⟩
          intro L hL
          rw [← he]
          exact Finset.le_sup hL
      simpa only [hlen] using simplex_mem_chains (planeComplex P) l ha
    · rw [planeProjection_simplex,ite_eq_right he]
      exact (chains (planeComplex P) n).zero_mem
  | zero => simpa only [map_zero] using (chains (planeComplex P) n).zero_mem
  | add c d hc hd ihc ihd => simpa only [map_add] using (chains (planeComplex P) n).add_mem ihc ihd
  | smul q c hc ih => simpa only [map_smul] using (chains (planeComplex P) n).smul_mem q ih

/-- Every actual finite chain admits a finite decomposition by its exact rational spans. -/
theorem exists_plane_decomposition (c : Chain RationalLine) :
    ∃ S : Finset RationalSubspace, (∑ P ∈ S, planeProjection P c) = c := by
  classical
  refine Quotient.inductionOn' c (fun r => ?_)
  let S := r.support.image (fun l : List RationalLine => faceSpan l.toFinset)
  refine ⟨S,?_⟩
  change (∑ P ∈ S, planeProjection P ((relations RationalLine).mkQ r)) =
    (relations RationalLine).mkQ r
  rw [mkQ_expansion]
  simp only [map_sum,map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.smul_sum]
  congr 1
  have hs : faceSpan l.toFinset ∈ S := Finset.mem_image.mpr ⟨l,hl,rfl⟩
  simp [planeProjection_simplex,hs]

/-- The exact span of a two-vertex simplex is the supremum of its literal line subspaces. -/
theorem edge_faceSpan (L M : RationalLine) : faceSpan [L,M].toFinset = L.val ⊔ M.val := by
  simp [faceSpan]

/-- Degenerate edges vanish, so a nonzero exact edge component has plane dimension two. -/
theorem planeProjection_zero_of_not_two (P : RationalSubspace)
    (hP : Module.finrank ℚ P ≠ 2) {c : Chain RationalLine} (hc : c ∈ chains good 2) :
    planeProjection P c = 0 := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    by_cases he : L = M
    · subst M
      rw [simplex_repeat_adjacent,map_zero]
    · have hd : Module.finrank ℚ (faceSpan [L,M].toFinset) = 2 := by
        rw [edge_faceSpan]
        exact GoodIncidenceConnected.finrank_sup_of_distinct_lines L.val M.val L.property M.property
          (fun heq => he (Subtype.ext heq))
      have hne : faceSpan [L,M].toFinset ≠ P := fun hh => hP (hh ▸ hd)
      rw [planeProjection_simplex,ite_eq_right hne]
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => rw [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => rw [map_smul,ih,smul_zero]

/-- Forget only the additional Good proof on an actual rational incidence line. -/
def forgetLine (L : GoodBuilding.GoodLine) : RationalLine := ⟨L.val,L.property.1⟩

@[simp] theorem forget_goodLine (L : RationalLine) (hL : Good L.val) :
    forgetLine (goodLine L hL) = L := rfl

/-- Extract exactly the actual incidence flags with plane `P`, and read their signed line endpoints.
This is a literal Finsupp coefficient map, not a plane-independence hypothesis. -/
def planeFlagBoundary (P : RationalSubspace) :
    GoodChainComplex.EdgeChains →ₗ[ℚ] Chain RationalLine := by
  classical
  exact Finsupp.linearCombination ℚ (fun e : GoodChainComplex.GoodEdge =>
    if e.val.2.val = P then -simplex [forgetLine e.val.1] else 0)

/-- The extraction map reads one displayed flag with its actual coefficient and plane equality. -/
theorem planeFlagBoundary_single (P : RationalSubspace) (e : GoodChainComplex.GoodEdge) (q : ℚ) :
    planeFlagBoundary P (Finsupp.single e q) =
      q • (if e.val.2.val = P then -simplex [forgetLine e.val.1] else 0) := by
  classical
  exact Finsupp.linearCombination_single ℚ q e

theorem planeFlagBoundary_flag (P : RationalSubspace) (L : GoodBuilding.GoodLine)
    (Q : GoodBuilding.GoodPlane) (hL : L.val ≤ Q.val) :
    planeFlagBoundary P (GoodApartmentCycles.flagChain Good L Q hL) =
      if Q.val = P then -simplex [forgetLine L] else 0 := by
  erw [GoodApartmentCycles.flagChain,planeFlagBoundary_single,one_smul]

/-- On a literal Good edge, the flag coefficients at one plane are exactly its projected boundary. -/
theorem boundary_planeProjection_edge (P : RationalSubspace) (L M : RationalLine)
    (hL : Good L.val) (hM : Good M.val) :
    boundary (planeProjection P (simplex [L,M])) = planeFlagBoundary P (edgeMap (simplex [L,M])) := by
  classical
  by_cases he : L = M
  · subst M
    rw [simplex_repeat_adjacent,map_zero,map_zero,map_zero,map_zero]
  · have hne : goodLine L hL ≠ goodLine M hM := fun hh => he
      (Subtype.ext (congrArg (fun A : GoodBuilding.GoodLine => A.val) hh))
    rw [edgeMap_simplex L M hL hM,GoodApartmentCycles.lineChain_of_ne Good _ _ hne]
    conv_rhs => erw [map_sub]
    rw [planeFlagBoundary_flag,planeFlagBoundary_flag,forget_goodLine,forget_goodLine,
      planeProjection_simplex]
    have hs : (GoodIncidenceConnected.spanPlane Good (goodLine L hL) (goodLine M hM) hne).val =
        faceSpan [L,M].toFinset := (edge_faceSpan L M).symm
    rw [hs]
    by_cases hp : faceSpan [L,M].toFinset = P
    · rw [ite_eq_left hp,ite_eq_left hp,ite_eq_left hp]
      simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
      abel
    · rw [ite_eq_right hp,ite_eq_right hp,ite_eq_right hp,map_zero,sub_self]

/-- Actual Finsupp flag extraction computes the boundary of every exact-plane edge component. -/
theorem boundary_planeProjection (P : RationalSubspace) {c : Chain RationalLine}
    (hc : c ∈ chains good 2) :
    boundary (planeProjection P c) = planeFlagBoundary P (edgeMap c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    have hf := hl.resolve_left (by simp)
    exact boundary_planeProjection_edge P L M (hf.2 L (by simp)) (hf.2 M (by simp))
  | zero => rw [map_zero,map_zero,map_zero,map_zero]
  | add c d hc hd ihc ihd => rw [map_add,map_add,map_add,map_add,ihc,ihd]
  | smul q c hc ih => rw [map_smul,map_smul,map_smul,map_smul,ih]

/-- Zero incidence image forces each literal plane component to be a cycle separately. -/
theorem planeProjection_cycle (P : RationalSubspace) {c : Chain RationalLine}
    (hc : c ∈ chains good 2) (he : edgeMap c = 0) : boundary (planeProjection P c) = 0 := by
  rw [boundary_planeProjection P hc,he,map_zero]

end TernaryPoly.ProperSpanProjection
