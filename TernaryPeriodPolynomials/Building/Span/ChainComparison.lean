module

public import TernaryPeriodPolynomials.Building.Good.RelativeChains

@[expose] public section


/-! The actual proper-span comparison to the good line-plane incidence graph.
This constructs a surjection of quotients; it makes no assertion about its kernel. -/

noncomputable section
namespace TernaryPoly.SpanChainComparison
open OrientedListChains ModThreeGoodAction AugmentedFrameComplex

local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : DecidableEq RationalLine := Classical.decEq _

section AlternatingLift
variable {V E : Type*} [AddCommGroup E] [Module ℚ E]

/-- Finite linear evaluation of actual vertex lists. -/
def rawEvaluate (f : List V → E) : Raw V →ₗ[ℚ] E :=
  Finsupp.lsum ℚ fun l => LinearMap.toSpanSingleton ℚ _ (f l)

@[simp] theorem rawEvaluate_simplex (f : List V → E) (l : List V) :
    rawEvaluate f (rawSimplex l) = f l := by
  simp only [rawEvaluate,rawSimplex,Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,one_smul]

theorem rawEvaluate_cons (f : List V → E) (a : V) (c : Raw V) :
    rawEvaluate f (rawCons a c) = rawEvaluate (fun l => f (a::l)) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add,hc,hd]
  | single l q =>
    have h : Finsupp.single l q = q • rawSimplex l := by simp [rawSimplex]
    simp only [h,map_smul,rawCons_simplex,rawEvaluate_simplex]

/-- Adjacent swaps at every prefix generate precisely the relations needed for evaluation. -/
def AlternatingLists (f : List V → E) : Prop :=
  ∀ (p : List V) (a b : V) (s : List V),
    f (p ++ a::b::s) + f (p ++ b::a::s) = 0

theorem rawEvaluate_relation {c : Raw V} (hc : c ∈ relations V) :
    ∀ f : List V → E, AlternatingLists f → rawEvaluate f c = 0 := by
  induction hc with
  | swap a b l =>
    intro f hf
    simpa only [map_add,rawEvaluate_simplex,List.nil_append] using hf [] a b l
  | cons a hc ih =>
    intro f hf
    rw [rawEvaluate_cons]
    apply ih
    intro p x y s
    simpa only [List.cons_append] using hf (a::p) x y s
  | zero => intro f hf; exact map_zero _
  | add hc hd ihc ihd => intro f hf; rw [map_add,ihc f hf,ihd f hf,add_zero]
  | smul q hc ih => intro f hf; rw [map_smul,ih f hf,smul_zero]

/-- Evaluation descends through the actual oriented-list relation submodule. -/
def evaluate (f : List V → E) (hf : AlternatingLists f) : Chain V →ₗ[ℚ] E :=
  (relations V).liftQ (rawEvaluate f) (fun _ hc => rawEvaluate_relation hc f hf)

@[simp] theorem evaluate_simplex (f : List V → E) (hf : AlternatingLists f) (l : List V) :
    evaluate f hf (simplex l) = f l := rawEvaluate_simplex f l

end AlternatingLift

/-- The same rational line, with its proved goodness retained. -/
def goodLine (L : RationalLine) (hL : Good L.val) : GoodBuilding.GoodLine :=
  ⟨L.val,L.property,hL⟩

def vertexValue : List RationalLine → GoodChainComplex.VertexChains
  | [L] => if hL : Good L.val then Finsupp.single (.inl (goodLine L hL)) 1 else 0
  | _ => 0

def edgeValue : List RationalLine → GoodChainComplex.EdgeChains
  | [L,M] => if hL : Good L.val then
      if hM : Good M.val then GoodApartmentCycles.lineChain Good (goodLine L hL) (goodLine M hM)
      else 0
    else 0
  | _ => 0

theorem vertexValue_alternating : AlternatingLists vertexValue := by
  intro p a b s
  cases p with
  | nil => simp [vertexValue]
  | cons x p => cases p <;> simp [vertexValue]

theorem edgeValue_alternating : AlternatingLists edgeValue := by
  intro p a b s
  cases p with
  | nil =>
    cases s with
    | nil =>
      by_cases ha : Good a.val <;> by_cases hb : Good b.val <;>
        simp [edgeValue,ha,hb]
      rw [GoodApartmentCycles.lineChain_reverse Good (goodLine a ha) (goodLine b hb)]
      exact add_neg_cancel _
    | cons x s => simp [edgeValue]
  | cons x p => cases p <;> simp [edgeValue]

def vertexMap : Chain RationalLine →ₗ[ℚ] GoodChainComplex.VertexChains :=
  evaluate vertexValue vertexValue_alternating

def edgeMap : Chain RationalLine →ₗ[ℚ] GoodChainComplex.EdgeChains :=
  evaluate edgeValue edgeValue_alternating

@[simp] theorem vertexMap_simplex (L : RationalLine) (hL : Good L.val) :
    vertexMap (simplex [L]) = Finsupp.single (.inl (goodLine L hL)) 1 := by
  simp only [vertexMap,evaluate_simplex,vertexValue,dite_eq_left hL]

@[simp] theorem edgeMap_simplex (L M : RationalLine) (hL : Good L.val) (hM : Good M.val) :
    edgeMap (simplex [L,M]) =
      GoodApartmentCycles.lineChain Good (goodLine L hL) (goodLine M hM) := by
  simp only [edgeMap,evaluate_simplex,edgeValue,dite_eq_left hL]
  exact dite_eq_left hM

/-- The actual oriented edge boundary agrees with its incidence path endpoints. -/
theorem boundary_edge_simplex (L M : RationalLine) (hL : Good L.val) (hM : Good M.val) :
    GoodChainComplex.boundary (edgeMap (simplex [L,M])) =
      vertexMap (OrientedListChains.boundary (simplex [L,M])) := by
  rw [edgeMap_simplex L M hL hM]
  change GoodApartmentCycles.boundary Good
    (GoodApartmentCycles.lineChain Good (goodLine L hL) (goodLine M hM)) = _
  rw [GoodApartmentCycles.boundary_lineChain]
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,
    vertexMap_simplex L hL,vertexMap_simplex M hM]

private theorem good_of_mem_allowed {l : List RationalLine} (hl : Allowed good l)
    {L : RationalLine} (hL : L ∈ l) : Good L.val := by
  classical
  rcases hl with rfl | hl
  · simp at hL
  · exact hl.2 L (List.mem_toFinset.mpr hL)

/-- Boundary compatibility on every actual good edge chain. -/
theorem boundary_edgeMap {c : Chain RationalLine} (hc : c ∈ chains good 2) :
    GoodChainComplex.boundary (edgeMap c) = vertexMap (OrientedListChains.boundary c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    exact boundary_edge_simplex L M (good_of_mem_allowed hl (by simp))
      (good_of_mem_allowed hl (by simp))
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

/-- The boundary of a triangle gives its literal oriented graph apartment. -/
theorem edgeMap_triangle_boundary (L M N : RationalLine)
    (hL : Good L.val) (hM : Good M.val) (hN : Good N.val) :
    edgeMap (OrientedListChains.boundary (simplex [L,M,N])) =
      GoodApartmentCycles.apartmentChain Good (goodLine L hL) (goodLine M hM) (goodLine N hN) := by
  have hb : OrientedListChains.boundary (simplex [L,M,N]) =
      simplex [M,N] - simplex [L,N] + simplex [L,M] := by
    simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub]
    abel
  rw [hb,map_add,map_sub,edgeMap_simplex L M hL hM,edgeMap_simplex L N hL hN,
    edgeMap_simplex M N hM hN,GoodApartmentCycles.apartmentChain,
    GoodApartmentCycles.lineChain_reverse Good (goodLine L hL) (goodLine N hN)]
  change (GoodApartmentCycles.lineChain Good (goodLine M hM) (goodLine N hN) -
    GoodApartmentCycles.lineChain Good (goodLine L hL) (goodLine N hN) +
    GoodApartmentCycles.lineChain Good (goodLine L hL) (goodLine M hM) :
    GoodApartmentCycles.Chains Good) = _
  abel

/-- A proper good triangle has zero incidence apartment because its span is at most a plane. -/
theorem edgeMap_proper_triangle (L M N : RationalLine)
    (hL : Good L.val) (hM : Good M.val) (hN : Good N.val)
    (hd : Module.finrank ℚ (faceSpan [L,M,N].toFinset) ≤ 2) :
    edgeMap (OrientedListChains.boundary (simplex [L,M,N])) = 0 := by
  classical
  by_cases he : L = M
  · subst M
    rw [simplex_repeat_adjacent,map_zero,map_zero]
  · rw [edgeMap_triangle_boundary L M N hL hM hN]
    let P := GoodIncidenceConnected.spanPlane Good (goodLine L hL) (goodLine M hM)
      (fun h => he (Subtype.ext (show L.val = M.val from
        congrArg (fun x : GoodBuilding.GoodLine => x.val) h)))
    have hLs : L.val ≤ faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hMs : M.val ≤ faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hNs : N.val ≤ faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hPs : P.val ≤ faceSpan [L,M,N].toFinset := sup_le hLs hMs
    have hdim : Module.finrank ℚ (faceSpan [L,M,N].toFinset) = 2 :=
      le_antisymm hd (P.property.1 ▸ Submodule.finrank_mono hPs)
    have hPeq : P.val = faceSpan [L,M,N].toFinset :=
      Submodule.eq_of_le_of_finrank_eq hPs (P.property.1.trans hdim.symm)
    exact GoodApartmentCycles.apartmentChain_collinear Good _ _ _ P
      (hPeq ▸ hLs) (hPeq ▸ hMs) (hPeq ▸ hNs)

/-- Every actual proper-good degree-two chain has zero apartment image. -/
theorem edgeMap_boundary_proper {c : Chain RationalLine} (hc : c ∈ chains properGood 3) :
    edgeMap (OrientedListChains.boundary c) = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,N,rfl⟩ := List.length_eq_three.mp hlen
    have hf : [L,M,N].toFinset ∈ properGood := hl.resolve_left (by simp)
    have hg : Allowed good [L,M,N] := Or.inr hf.1
    exact edgeMap_proper_triangle L M N
      (good_of_mem_allowed hg (by simp)) (good_of_mem_allowed hg (by simp))
      (good_of_mem_allowed hg (by simp)) hf.2
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- The boundary of every actual good degree-two chain is an incidence graph cycle. -/
def spanCycleMap : GoodRelativeChains.GoodTwo →ₗ[ℚ] GoodChainComplex.Cycles :=
  ((edgeMap.comp OrientedListChains.boundary).comp (chains good 3).subtype).codRestrict _ (by
    intro c
    change GoodChainComplex.boundary (edgeMap (OrientedListChains.boundary c.val)) = 0
    rw [boundary_edgeMap (boundary_mem_chains good 2 c.property),boundary_squared,map_zero])

theorem spanCycleMap_proper (c : GoodRelativeChains.ProperTwo) :
    spanCycleMap (GoodRelativeChains.properInclusion c) = 0 := by
  apply Subtype.ext
  exact edgeMap_boundary_proper c.property

theorem spanCycleMap_boundary (c : chains good 4) :
    spanCycleMap (differential good 3 c) = 0 := by
  apply Subtype.ext
  change edgeMap (OrientedListChains.boundary (OrientedListChains.boundary c.val)) = 0
  rw [boundary_squared,map_zero]

theorem nullSubmodule_le_ker : GoodRelativeChains.nullSubmodule ≤ LinearMap.ker spanCycleMap := by
  apply sup_le
  · rintro x ⟨c,rfl⟩
    exact spanCycleMap_proper c
  · rintro x ⟨c,rfl⟩
    exact spanCycleMap_boundary c

/-- The genuine comparison from the relative boundary quotient to actual incidence cycles. -/
def comparison : GoodRelativeChains.RelativeBoundaryTwo →ₗ[ℚ] GoodChainComplex.Cycles :=
  GoodRelativeChains.nullSubmodule.liftQ spanCycleMap nullSubmodule_le_ker

@[simp] theorem comparison_quotientMap (c : GoodRelativeChains.GoodTwo) :
    comparison (GoodRelativeChains.quotientMap c) = spanCycleMap c := rfl

/-- The column lines on both sides are the same actual rational subspaces. -/
theorem goodLine_column (g : K) (j : Fin 3) :
    goodLine (augmentedLine g.val j.castSucc)
      (GoodRelativeChains.good_K_augmentedLine g j.castSucc) =
      GoodIntegralFrames.columnLine g.val.val (GoodUnimodularOrbit.element_normalized g) j := by
  apply Subtype.ext
  change (augmentedLine g.val j.castSucc).val = _
  rw [AugmentedBadFaces.augmentedLine_castSucc_val,AugmentedBadFaces.rationalRepresentation_basis]
  rfl

/-- The comparison sends an actual ordered K-frame to its actual graph apartment translate. -/
theorem comparison_triangle (g : K) :
    comparison (GoodRelativeChains.quotientMap (GoodRelativeChains.triangle g)) =
      GoodChainComplex.complex.cyclesAction g GoodUnimodularOrbit.referenceApartment := by
  rw [comparison_quotientMap,← GoodUnimodularOrbit.frameApartment_val_eq_translate]
  apply Subtype.ext
  change edgeMap (OrientedListChains.boundary
    (simplex [augmentedLine g.val 0,augmentedLine g.val 1,augmentedLine g.val 2])) = _
  rw [edgeMap_triangle_boundary _ _ _ (GoodRelativeChains.good_K_augmentedLine g 0)
    (GoodRelativeChains.good_K_augmentedLine g 1) (GoodRelativeChains.good_K_augmentedLine g 2)]
  have h0 := goodLine_column g 0
  have h1 := goodLine_column g 1
  have h2 := goodLine_column g 2
  change goodLine (augmentedLine g.val 0) _ = _ at h0
  change goodLine (augmentedLine g.val 1) _ = _ at h1
  change goodLine (augmentedLine g.val 2) _ = _ at h2
  rw [h0,h1,h2]
  rfl

/-- Exact compatibility of the two existing free K-orbit maps. -/
theorem comparison_orbitMap :
    comparison.comp GoodRelativeChains.orbitMap = GoodOrbitRelations.orbitMap := by
  apply Finsupp.lhom_ext
  intro g q
  have h : Finsupp.single g q = q • GoodOrbitRelations.delta g := by
    simp [GoodOrbitRelations.delta]
  rw [h,map_smul,map_smul]
  change q • comparison (GoodRelativeChains.orbitMap (GoodOrbitRelations.delta g)) = _
  rw [GoodRelativeChains.orbitMap_delta,comparison_triangle,GoodOrbitRelations.orbitMap_delta]

/-- Existing orbit spanning makes the actual comparison surjective. -/
theorem comparison_surjective : Function.Surjective comparison := by
  intro c
  obtain ⟨x,hx⟩ := GoodOrbitRelations.orbitMap_surjective c
  refine ⟨GoodRelativeChains.orbitMap x,?_⟩
  exact (LinearMap.congr_fun comparison_orbitMap x).trans hx

end TernaryPoly.SpanChainComparison
