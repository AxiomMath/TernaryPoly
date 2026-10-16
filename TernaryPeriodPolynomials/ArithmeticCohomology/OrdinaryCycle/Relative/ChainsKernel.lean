module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.ChainsPlanes
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.SpanComparison
public import TernaryPeriodPolynomials.Building.Proper.SpanProjection
public import TernaryPeriodPolynomials.Building.Ambient.TwoFilling

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryRelativeChainsKernel
open ModThreeGoodAction AugmentedFrameComplex OrientedListChains OrdinaryRelativeChains
open OrdinaryRelativeChainsPlanes OrdinaryApartmentSpanComparison
open ProperSpanProjection (planeProjection planeProjection_simplex edge_faceSpan exists_plane_decomposition)
local instance : DecidableEq RationalLine := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Each exact-span component retains actual ambient support in the specified plane. -/
theorem planeProjection_mem (P : RationalSubspace) (n : ℕ)
    {c : Chain RationalLine} (hc : c ∈ chains ambient n) :
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

/-- Degenerate edges vanish, so a nonzero exact edge component has plane dimension two. -/
theorem planeProjection_zero_of_not_two (P : RationalSubspace)
    (hP : Module.finrank ℚ P ≠ 2) {c : Chain RationalLine} (hc : c ∈ chains ambient 2) :
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

/-- Forget only the redundant truth proof on an actual rational incidence line. -/
def forgetLine (L : OrdinaryIncidence.Line) : RationalLine := ⟨L.val,L.property.1⟩

@[simp] theorem forget_line (L : RationalLine)  :
    forgetLine (line L) = L := rfl

/-- Extract exactly the actual incidence flags with plane `P`, and read their signed line endpoints.
This is a literal Finsupp coefficient map, not a plane-independence hypothesis. -/
def planeFlagBoundary (P : RationalSubspace) :
    OrdinaryIncidenceChains.EdgeChains →ₗ[ℚ] Chain RationalLine := by
  classical
  exact Finsupp.linearCombination ℚ (fun e : OrdinaryIncidenceChains.Edge =>
    if e.val.2.val = P then -simplex [forgetLine e.val.1] else 0)

/-- The extraction map reads one displayed flag with its actual coefficient and plane equality. -/
theorem planeFlagBoundary_single (P : RationalSubspace) (e : OrdinaryIncidenceChains.Edge) (q : ℚ) :
    planeFlagBoundary P (Finsupp.single e q) =
      q • (if e.val.2.val = P then -simplex [forgetLine e.val.1] else 0) := by
  classical
  exact Finsupp.linearCombination_single ℚ q e

theorem planeFlagBoundary_flag (P : RationalSubspace) (L : OrdinaryIncidence.Line)
    (Q : OrdinaryIncidence.Plane) (hL : L.val ≤ Q.val) :
    planeFlagBoundary P (GoodApartmentCycles.flagChain (fun _ => True) L Q hL) =
      if Q.val = P then -simplex [forgetLine L] else 0 := by
  erw [GoodApartmentCycles.flagChain,planeFlagBoundary_single,one_smul]

/-- On a literal ordinary edge, the flag coefficients at one plane are exactly its projected boundary. -/
theorem boundary_planeProjection_edge (P : RationalSubspace) (L M : RationalLine)
      :
    boundary (planeProjection P (simplex [L,M])) = planeFlagBoundary P (edgeMap (simplex [L,M])) := by
  classical
  by_cases he : L = M
  · subst M
    rw [simplex_repeat_adjacent,map_zero,map_zero,map_zero,map_zero]
  · have hne : line L ≠ line M := fun hh => he
      (Subtype.ext (congrArg (fun A : OrdinaryIncidence.Line => A.val) hh))
    rw [edgeMap_simplex L M,GoodApartmentCycles.lineChain_of_ne (fun _ => True) _ _ hne]
    conv_rhs => erw [map_sub]
    rw [planeFlagBoundary_flag,planeFlagBoundary_flag,forget_line,forget_line,
      planeProjection_simplex]
    have hs : (GoodIncidenceConnected.spanPlane (fun _ => True) (line L) (line M) hne).val =
        faceSpan [L,M].toFinset := (edge_faceSpan L M).symm
    rw [hs]
    by_cases hp : faceSpan [L,M].toFinset = P
    · rw [ite_eq_left hp,ite_eq_left hp,ite_eq_left hp]
      simp only [boundary_cons,boundary_nil,map_zero,sub_zero,cons_simplex]
      abel
    · rw [ite_eq_right hp,ite_eq_right hp,ite_eq_right hp,map_zero,sub_self]

/-- Actual Finsupp flag extraction computes the boundary of every exact-plane edge component. -/
theorem boundary_planeProjection (P : RationalSubspace) {c : Chain RationalLine}
    (hc : c ∈ chains ambient 2) :
    boundary (planeProjection P c) = planeFlagBoundary P (edgeMap c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,_,rfl⟩ := hc
    obtain ⟨L,M,rfl⟩ := List.length_eq_two.mp hlen
    exact boundary_planeProjection_edge P L M
  | zero => rw [map_zero,map_zero,map_zero,map_zero]
  | add c d hc hd ihc ihd => rw [map_add,map_add,map_add,map_add,ihc,ihd]
  | smul q c hc ih => rw [map_smul,map_smul,map_smul,map_smul,ih]

/-- Zero incidence image forces each literal plane component to be a cycle separately. -/
theorem planeProjection_cycle (P : RationalSubspace) {c : Chain RationalLine}
    (hc : c ∈ chains ambient 2) (he : edgeMap c = 0) : boundary (planeProjection P c) = 0 := by
  rw [boundary_planeProjection P hc,he,map_zero]

/-- Each actual exact-plane component has a proper ambient triangle filling. -/
theorem component_filling (hplane : PerPlaneFilling) (P : RationalSubspace)
    {z : Chain RationalLine} (hz : z ∈ chains ambient 2) (he : edgeMap z = 0) :
    ∃ q : Chain RationalLine, q ∈ chains properAmbient 3 ∧ boundary q = planeProjection P z := by
  by_cases hP : Module.finrank ℚ P = 2
  · obtain ⟨q,hq,hdq⟩ := hplane P hP (planeProjection P z)
      (planeProjection_mem P 2 hz) (planeProjection_cycle P hz he)
    exact ⟨q,chains_mono (planeComplex_le_properAmbient P hP.le) 3 hq,hdq⟩
  · exact ⟨0,(chains properAmbient 3).zero_mem,by rw [map_zero,planeProjection_zero_of_not_two P hP hz]⟩

/-- Finite exact-plane decomposition and actual flag coefficient extraction fill the entire kernel. -/
theorem fill_edgeMap_kernel (hplane : PerPlaneFilling)
    {z : Chain RationalLine} (hz : z ∈ chains ambient 2) (he : edgeMap z = 0) :
    ∃ q : Chain RationalLine, q ∈ chains properAmbient 3 ∧ boundary q = z := by
  classical
  obtain ⟨S,hS⟩ := exists_plane_decomposition z
  choose q hq hdq using (fun P => component_filling hplane P hz he)
  refine ⟨∑ P ∈ S,q P,(chains properAmbient 3).sum_mem (fun P _ => hq P),?_⟩
  simpa only [map_sum,hdq] using hS


/-- Actual ambient H2 filling identifies the relative null module once the proper edge kernel fills. -/
theorem ker_spanCycleMap  :
    LinearMap.ker spanCycleMap = nullSubmodule := by
  apply le_antisymm ?_ nullSubmodule_le_ker
  intro c hc
  have he : edgeMap (boundary c.val) = 0 := congrArg Subtype.val hc
  obtain ⟨q,hq,hdq⟩ := fill_edgeMap_kernel perPlaneFilling
    (boundary_mem_chains ambient 2 c.property) he
  have hqgood := chains_mono properAmbient_le_ambient 3 hq
  have hcycle : boundary (c.val-q) = 0 := by rw [map_sub,hdq,sub_self]
  obtain ⟨b,hb,hdb⟩ := AmbientTwoFilling.ambient_two_filling (c.val-q)
    ((chains ambient 3).sub_mem c.property hqgood) hcycle
  have hqm : properInclusion ⟨q,hq⟩ ∈ nullSubmodule :=
    (show properSubmodule ≤ nullSubmodule from le_sup_left) ⟨⟨q,hq⟩,rfl⟩
  have hbm : differential ambient 3 ⟨b,hb⟩ ∈ nullSubmodule :=
    (show (differential ambient 3).range ≤ nullSubmodule from le_sup_right) ⟨⟨b,hb⟩,rfl⟩
  have hdecomp : c = properInclusion ⟨q,hq⟩ + differential ambient 3 ⟨b,hb⟩ := by
    apply Subtype.ext
    change c.val = q + boundary b
    rw [hdb]
    abel
  rw [hdecomp]
  exact nullSubmodule.add_mem hqm hbm

/-- The actual relative-to-incidence comparison is injective by the proved unrestricted proper kernel. -/
theorem comparison_injective  : Function.Injective comparison := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x
  refine Submodule.Quotient.induction_on nullSubmodule x ?_
  intro c hc
  apply (Submodule.Quotient.mk_eq_zero nullSubmodule).mpr
  rw [← ker_spanCycleMap]
  exact hc


end TernaryPoly.OrdinaryRelativeChainsKernel
