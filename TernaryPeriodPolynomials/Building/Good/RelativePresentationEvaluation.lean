module

public import TernaryPeriodPolynomials.Building.Good.RelativePresentationFrames
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.GoodRelativePresentationEvaluation
open ModThreeGoodAction AugmentedFrameComplex GoodRelativeChains
open GoodRelativePresentationFrames ReferenceCoefficientMatrices OrientedListChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Only the cyclic and transposition orientation relations. -/
def orientations : Submodule ℚ GoodOrbitRelations.FreeOrbit :=
  Submodule.span ℚ (Set.range GoodOrbitRelations.cyclicRelation ∪ Set.range GoodOrbitRelations.swapRelation)

abbrev OrientationQuotient := GoodOrbitRelations.FreeOrbit ⧸ orientations

def deltaClass (g : K) : OrientationQuotient := orientations.mkQ (GoodOrbitRelations.delta g)

theorem orientations_le_relations : orientations ≤ GoodOrbitRelations.relations := by
  apply Submodule.span_le.mpr
  intro x hx
  apply Submodule.subset_span
  rcases hx with hx | hx
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

theorem deltaClass_cyclic (g : K) : deltaClass (g*cK) = deltaClass g := by
  have h : GoodOrbitRelations.cyclicRelation g ∈ orientations :=
    Submodule.subset_span (Or.inl ⟨g,rfl⟩)
  have he := (Submodule.Quotient.mk_eq_zero orientations).mpr h
  change orientations.mkQ (GoodOrbitRelations.cyclicRelation g) = 0 at he
  simpa only [GoodOrbitRelations.cyclicRelation,map_sub,deltaClass,sub_eq_zero] using he

theorem deltaClass_swap (g : K) : deltaClass (g*sK) = -deltaClass g := by
  have h : GoodOrbitRelations.swapRelation g ∈ orientations :=
    Submodule.subset_span (Or.inr ⟨g,rfl⟩)
  have he := (Submodule.Quotient.mk_eq_zero orientations).mpr h
  change orientations.mkQ (GoodOrbitRelations.swapRelation g) = 0 at he
  have he' : deltaClass (g*sK) + deltaClass g = 0 := by
    simpa only [GoodOrbitRelations.swapRelation,map_add,deltaClass] using he
  exact eq_neg_of_add_eq_zero_left he'

/-- A list receives its unique normalized frame class, and every other list receives zero. -/
def value (l : List RationalLine) : OrientationQuotient := by
  classical
  exact if h : ∃ g : K, triangleList g.val = l then deltaClass h.choose else 0

@[simp] theorem value_triangle (g : K) : value (triangleList g.val) = deltaClass g := by
  have h : ∃ h : K, triangleList h.val = triangleList g.val := ⟨g,rfl⟩
  rw [value,dite_eq_left h]
  congr 1
  exact triangleList_injective h.choose_spec

theorem value_of_frame (g : K) (l : List RationalLine) (hg : triangleList g.val = l) :
    value l = deltaClass g := by rw [← hg,value_triangle]

theorem value_eq_zero_of_no_frame (l : List RationalLine)
    (h : ¬∃ g : K, triangleList g.val = l) : value l = 0 := by rw [value,dite_eq_right h]

theorem value_swap_first (L M N : RationalLine) : value [M,L,N] = -value [L,M,N] := by
  by_cases h : ∃ g : K, triangleList g.val = [L,M,N]
  · obtain ⟨g,hg⟩ := h
    rw [value_of_frame g _ hg,value_of_frame (g*sK) _ (triangleList_swap_of_eq g L M N hg)]
    exact deltaClass_swap g
  · have h' : ¬∃ g : K, triangleList g.val = [M,L,N] := by
      rintro ⟨g,hg⟩
      exact h ⟨g*sK,triangleList_swap_of_eq g M L N hg⟩
    rw [value_eq_zero_of_no_frame _ h,value_eq_zero_of_no_frame _ h',neg_zero]

theorem value_cyclic (L M N : RationalLine) : value [M,N,L] = value [L,M,N] := by
  by_cases h : ∃ g : K, triangleList g.val = [L,M,N]
  · obtain ⟨g,hg⟩ := h
    rw [value_of_frame g _ hg,value_of_frame (g*cK) _ (triangleList_cycle_of_eq g L M N hg)]
    exact deltaClass_cyclic g
  · have h' : ¬∃ g : K, triangleList g.val = [M,N,L] := by
      rintro ⟨g,hg⟩
      exact h ⟨(g*cK)*cK,triangleList_cycle_of_eq (g*cK) N L M
        (triangleList_cycle_of_eq g M N L hg)⟩
    rw [value_eq_zero_of_no_frame _ h,value_eq_zero_of_no_frame _ h']

theorem value_swap_last (L M N : RationalLine) : value [L,N,M] = -value [L,M,N] := by
  calc
    value [L,N,M] = value [N,M,L] := (value_cyclic L N M).symm
    _ = -value [M,N,L] := value_swap_first M N L
    _ = -value [L,M,N] := congrArg Neg.neg (value_cyclic L M N)

theorem value_eq_zero_of_length (l : List RationalLine) (hl : l.length ≠ 3) : value l = 0 := by
  apply value_eq_zero_of_no_frame
  rintro ⟨g,hg⟩
  apply hl
  rw [← hg]
  rfl

/-- The actual finite-list evaluator satisfies every orientation relation, at every prefix. -/
theorem value_alternating : SpanChainComparison.AlternatingLists value := by
  intro p L M s
  by_cases hlen : (p ++ L :: M :: s).length = 3
  · have hlen' : p.length + s.length = 1 := by
      simp only [List.length_append,List.length_cons] at hlen
      omega
    cases p with
    | nil =>
      have hs : s.length = 1 := by simpa using hlen'
      obtain ⟨N,rfl⟩ := List.length_eq_one_iff.mp hs
      change value [L,M,N] + value [M,L,N] = 0
      rw [value_swap_first L M N,add_neg_cancel]
    | cons N p =>
      have hp : p = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen'; omega)
      have hs : s = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen'; omega)
      subst p
      subst s
      change value [N,L,M] + value [N,M,L] = 0
      rw [value_swap_last N L M,add_neg_cancel]
  · have hlen' : (p ++ M :: L :: s).length ≠ 3 := by
      simpa only [List.length_append,List.length_cons] using hlen
    rw [value_eq_zero_of_length _ hlen,value_eq_zero_of_length _ hlen',add_zero]

/-- The evaluator on the genuine oriented-list quotient. -/
def evaluator : Chain RationalLine →ₗ[ℚ] OrientationQuotient :=
  SpanChainComparison.evaluate value value_alternating

@[simp] theorem evaluator_simplex (l : List RationalLine) : evaluator (simplex l) = value l :=
  SpanChainComparison.evaluate_simplex value value_alternating l

@[simp] theorem evaluator_triangle (g : K) : evaluator (triangle g).val = deltaClass g := by
  change evaluator (simplex (triangleList g.val)) = _
  rw [evaluator_simplex,value_triangle]

/-- Proper-span triangles have no independent K-frame representative and evaluate to zero. -/
theorem evaluator_proper_simplex (l : List RationalLine)
    (hd : Module.finrank ℚ (faceSpan l.toFinset) ≤ 2) : evaluator (simplex l) = 0 := by
  rw [evaluator_simplex]
  exact value_eq_zero_of_no_frame l (not_triangleList_of_proper l hd)

/-- Every finite proper Good triangle chain evaluates to zero. -/
theorem evaluator_proper_chain {c : Chain RationalLine} (hc : c ∈ chains properGood 3) :
    evaluator c = 0 := by
  classical
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    rcases hl with rfl | hl
    · simp at hlen
    · exact evaluator_proper_simplex l hl.2
  | zero => exact map_zero _
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- Restriction to actual Good triangles. -/
def goodEvaluator : GoodTwo →ₗ[ℚ] OrientationQuotient := evaluator.comp GoodTwo.subtype

theorem properSubmodule_le_ker : properSubmodule ≤ LinearMap.ker goodEvaluator := by
  rintro c ⟨p,rfl⟩
  exact evaluator_proper_chain p.property

/-- The exact evaluator on proper-relative Good triangles. -/
def relativeEvaluator : RelativeTwo →ₗ[ℚ] OrientationQuotient :=
  properSubmodule.liftQ goodEvaluator properSubmodule_le_ker

@[simp] theorem relativeEvaluator_mk (x : GoodTwo) :
    relativeEvaluator (properSubmodule.mkQ x) = evaluator x.val := rfl

/-- The free K-frame map before quotienting by actual tetrahedron boundaries. -/
def properOrbitMap : GoodOrbitRelations.FreeOrbit →ₗ[ℚ] RelativeTwo :=
  Finsupp.lsum ℚ fun g => LinearMap.toSpanSingleton ℚ _ (properSubmodule.mkQ (triangle g))

@[simp] theorem properOrbitMap_delta (g : K) :
    properOrbitMap (GoodOrbitRelations.delta g) = properSubmodule.mkQ (triangle g) := by
  simp only [properOrbitMap,GoodOrbitRelations.delta,Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,one_smul]

/-- The proper-relative evaluator recovers the literal orientation quotient map. -/
theorem relativeEvaluator_properOrbitMap :
    relativeEvaluator.comp properOrbitMap = orientations.mkQ := by
  apply Finsupp.lhom_ext
  intro g q
  have h : Finsupp.single g q = q • GoodOrbitRelations.delta g := by simp [GoodOrbitRelations.delta]
  rw [h,map_smul,map_smul]
  change q • relativeEvaluator (properOrbitMap (GoodOrbitRelations.delta g)) = _
  rw [properOrbitMap_delta,relativeEvaluator_mk,evaluator_triangle]
  rfl

/-- Cyclic and swap orientation relations are exactly all relations before tetrahedron boundaries. -/
theorem properOrbitMap_ker : LinearMap.ker properOrbitMap = orientations := by
  apply le_antisymm
  · intro x hx
    have he := LinearMap.congr_fun relativeEvaluator_properOrbitMap x
    have hx' : properOrbitMap x = 0 := hx
    change relativeEvaluator (properOrbitMap x) = orientations.mkQ x at he
    rw [hx',map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero orientations).mp he.symm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨g,rfl⟩ | ⟨g,rfl⟩
    · change properOrbitMap (GoodOrbitRelations.cyclicRelation g) = 0
      rw [GoodOrbitRelations.cyclicRelation,map_sub,properOrbitMap_delta,properOrbitMap_delta,
        triangle_cyclic,sub_self]
    · change properOrbitMap (GoodOrbitRelations.swapRelation g) = 0
      rw [GoodOrbitRelations.swapRelation,map_add,properOrbitMap_delta,properOrbitMap_delta,
        triangle_swap,map_neg,neg_add_cancel]

/-- Every proper-relative actual Good triangle chain is generated by the normalized K frames. -/
theorem properOrbitMap_surjective : Function.Surjective properOrbitMap := by
  intro x
  obtain ⟨c,rfl⟩ := properSubmodule.mkQ_surjective x
  suffices h : properSubmodule.mkQ c ∈ properOrbitMap.range from h
  obtain ⟨c,hc⟩ := c
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    have hgood : simplex l ∈ GoodTwo := by simpa only [hlen] using simplex_mem_chains good l hl
    rcases good_triangle_cases l hlen hl with hp | ⟨g,hg⟩
    · have hpc : simplex l ∈ chains properGood 3 := by
        have h := simplex_mem_chains properGood l (Or.inr hp)
        simpa only [hlen] using h
      have he : properSubmodule.mkQ (⟨simplex l,hgood⟩ : GoodTwo) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact ⟨⟨simplex l,hpc⟩,rfl⟩
      rw [he]
      exact properOrbitMap.range.zero_mem
    · have ht : triangle g = (⟨simplex l,hgood⟩ : GoodTwo) := by
        apply Subtype.ext
        change simplex (triangleList g.val) = simplex l
        rw [hg]
      exact ⟨GoodOrbitRelations.delta g,
        (properOrbitMap_delta g).trans (congrArg properSubmodule.mkQ ht)⟩
  | zero => exact properOrbitMap.range.zero_mem
  | add c d hc hd ihc ihd => exact properOrbitMap.range.add_mem ihc ihd
  | smul q c hc ih => exact properOrbitMap.range.smul_mem q ih

end TernaryPoly.GoodRelativePresentationEvaluation
