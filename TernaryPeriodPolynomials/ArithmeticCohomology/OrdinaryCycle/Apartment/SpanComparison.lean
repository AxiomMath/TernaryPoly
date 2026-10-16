module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.Chains
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains
public import TernaryPeriodPolynomials.Building.Span.ChainComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryApartmentSpanComparison
open OrientedListChains ModThreeGoodAction AugmentedFrameComplex OrdinaryRelativeChains
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Retain the same line subspace in the ordinary incidence model. -/
def line (L : RationalLine) : OrdinaryIncidence.Line := ⟨L.val,L.property,trivial⟩

def vertexValue : List RationalLine → OrdinaryIncidenceChains.VertexChains
  | [L] => Finsupp.single (.inl (line L)) 1
  | _ => 0

def edgeValue : List RationalLine → OrdinaryIncidenceChains.EdgeChains
  | [L,M] => GoodApartmentCycles.lineChain (fun _ => True) (line L) (line M)
  | _ => 0

theorem vertexValue_alternating : SpanChainComparison.AlternatingLists vertexValue := by
  intro p a b s
  cases p with
  | nil => simp [vertexValue]
  | cons x p => cases p <;> simp [vertexValue]

theorem edgeValue_alternating : SpanChainComparison.AlternatingLists edgeValue := by
  intro p a b s
  cases p with
  | nil =>
    cases s with
    | nil =>
      change GoodApartmentCycles.lineChain (fun _ => True) (line a) (line b)+
        GoodApartmentCycles.lineChain (fun _ => True) (line b) (line a)=0
      rw [GoodApartmentCycles.lineChain_reverse (fun _ => True) (line a) (line b)]
      exact add_neg_cancel (GoodApartmentCycles.lineChain (fun _ => True) (line a) (line b))
    | cons x s => simp [edgeValue]
  | cons x p => cases p <;> simp [edgeValue]

def vertexMap : Chain RationalLine →ₗ[ℚ] OrdinaryIncidenceChains.VertexChains :=
  SpanChainComparison.evaluate vertexValue vertexValue_alternating

def edgeMap : Chain RationalLine →ₗ[ℚ] OrdinaryIncidenceChains.EdgeChains :=
  SpanChainComparison.evaluate edgeValue edgeValue_alternating

@[simp] theorem vertexMap_simplex (L : RationalLine) :
    vertexMap (simplex [L])=Finsupp.single (.inl (line L)) 1 :=
  SpanChainComparison.evaluate_simplex _ _ _

@[simp] theorem edgeMap_simplex (L M : RationalLine) :
    edgeMap (simplex [L,M])=GoodApartmentCycles.lineChain (fun _ => True) (line L) (line M) :=
  SpanChainComparison.evaluate_simplex _ _ _

/-- The oriented edge boundary is exactly the incidence-path endpoint boundary. -/
theorem boundary_edge_simplex (L M : RationalLine) :
    OrdinaryIncidenceChains.boundary (edgeMap (simplex [L,M]))=
      vertexMap (OrientedListChains.boundary (simplex [L,M])) := by
  rw [edgeMap_simplex]
  change GoodApartmentCycles.boundary (fun _ => True)
    (GoodApartmentCycles.lineChain (fun _ => True) (line L) (line M))=_
  rw [GoodApartmentCycles.boundary_lineChain]
  simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub,vertexMap_simplex]

theorem boundary_edgeMap {c : Chain RationalLine} (hc : c∈chains ambient 2) :
    OrdinaryIncidenceChains.boundary (edgeMap c)=vertexMap (OrientedListChains.boundary c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    exact boundary_edge_simplex L M
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd]
  | smul q c hc ih => simp only [map_smul,ih]

theorem edgeMap_triangle_boundary (L M N : RationalLine) :
    edgeMap (OrientedListChains.boundary (simplex [L,M,N]))=
      GoodApartmentCycles.apartmentChain (fun _ => True) (line L) (line M) (line N) := by
  have hb : OrientedListChains.boundary (simplex [L,M,N])=
      simplex [M,N]-simplex [L,N]+simplex [L,M] := by
    simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex,map_sub]
    abel
  rw [hb,map_add,map_sub,edgeMap_simplex,edgeMap_simplex,edgeMap_simplex,
    GoodApartmentCycles.apartmentChain,GoodApartmentCycles.lineChain_reverse (fun _ => True) (line L) (line N)]
  change (GoodApartmentCycles.lineChain (fun _ => True) (line M) (line N)-
    GoodApartmentCycles.lineChain (fun _ => True) (line L) (line N)+
    GoodApartmentCycles.lineChain (fun _ => True) (line L) (line M) :
    GoodApartmentCycles.Chains (fun _ => True))=_
  abel

/-- The boundary apartment of a proper-span ambient triangle vanishes literally. -/
theorem edgeMap_proper_triangle (L M N : RationalLine)
    (hd : Module.finrank ℚ (faceSpan [L,M,N].toFinset)≤2) :
    edgeMap (OrientedListChains.boundary (simplex [L,M,N]))=0 := by
  by_cases he : L=M
  · subst M
    rw [simplex_repeat_adjacent,map_zero,map_zero]
  · rw [edgeMap_triangle_boundary]
    let P := GoodIncidenceConnected.spanPlane (fun _ => True) (line L) (line M)
      (fun h => he (Subtype.ext (show L.val=M.val from congrArg (fun x : OrdinaryIncidence.Line => x.val) h)))
    have hLs : L.val≤faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hMs : M.val≤faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hNs : N.val≤faceSpan [L,M,N].toFinset := Finset.le_sup (by simp)
    have hPs : P.val≤faceSpan [L,M,N].toFinset := sup_le hLs hMs
    have hdim : Module.finrank ℚ (faceSpan [L,M,N].toFinset)=2 :=
      le_antisymm hd (P.property.1 ▸ Submodule.finrank_mono hPs)
    have hPeq : P.val=faceSpan [L,M,N].toFinset :=
      Submodule.eq_of_le_of_finrank_eq hPs (P.property.1.trans hdim.symm)
    exact GoodApartmentCycles.apartmentChain_collinear (fun _ => True) _ _ _ P
      (hPeq ▸ hLs) (hPeq ▸ hMs) (hPeq ▸ hNs)

theorem edgeMap_boundary_proper {c : Chain RationalLine} (hc : c∈chains properAmbient 3) :
    edgeMap (OrientedListChains.boundary c)=0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    obtain ⟨L,M,N,rfl⟩ := List.length_eq_three.mp hlen
    have hf : [L,M,N].toFinset∈properAmbient := hl.resolve_left (by simp)
    exact edgeMap_proper_triangle L M N hf.2
  | zero => simp only [map_zero]
  | add c d hc hd ihc ihd => simp only [map_add,ihc,ihd,add_zero]
  | smul q c hc ih => simp only [map_smul,ih,smul_zero]

/-- Actual ambient triangle chains give actual ordinary incidence cycles. -/
def spanCycleMap : AmbientTwo →ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  ((edgeMap.comp OrientedListChains.boundary).comp AmbientTwo.subtype).codRestrict _ (by
    intro c
    change OrdinaryIncidenceChains.boundary (edgeMap (OrientedListChains.boundary c.val))=0
    rw [boundary_edgeMap (boundary_mem_chains ambient 2 c.property),boundary_squared,map_zero])

theorem spanCycleMap_proper (c : ProperTwo) : spanCycleMap (properInclusion c)=0 := by
  apply Subtype.ext
  exact edgeMap_boundary_proper c.property

theorem spanCycleMap_boundary (c : chains ambient 4) : spanCycleMap (differential ambient 3 c)=0 := by
  apply Subtype.ext
  change edgeMap (OrientedListChains.boundary (OrientedListChains.boundary c.val))=0
  rw [boundary_squared,map_zero]

theorem nullSubmodule_le_ker : nullSubmodule≤LinearMap.ker spanCycleMap := by
  apply sup_le
  · rintro x ⟨c,rfl⟩
    exact spanCycleMap_proper c
  · rintro x ⟨c,rfl⟩
    exact spanCycleMap_boundary c

/-- The actual relative ambient quotient maps to the actual ordinary incidence cycle module. -/
def comparison : RelativeBoundaryTwo →ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  nullSubmodule.liftQ spanCycleMap nullSubmodule_le_ker

@[simp] theorem comparison_quotientMap (c : AmbientTwo) : comparison (quotientMap c)=spanCycleMap c := rfl

end TernaryPoly.OrdinaryApartmentSpanComparison
