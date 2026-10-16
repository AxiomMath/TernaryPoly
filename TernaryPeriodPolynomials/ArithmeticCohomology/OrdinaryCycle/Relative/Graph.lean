module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.IncidenceChains

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryRelativeGraph
open OrdinaryIncidenceChains OrdinaryIncidencePaths

/-- The three literal image subspaces used in the relative graph sequence. -/
def goodEdges : Submodule ℚ EdgeChains := edgeInclusion.range
def goodVertices : Submodule ℚ VertexChains := vertexInclusion.range
def goodCycles : Submodule ℚ Cycles := cycleInclusion.range
abbrev R₁ := EdgeChains ⧸ goodEdges
abbrev R₀ := VertexChains ⧸ goodVertices
abbrev Q := Cycles ⧸ goodCycles

/-- Inclusion of ordinary cycles descends modulo the actual Good cycles and edges. -/
def cycleToEdge : Q →ₗ[ℚ] R₁ :=
  goodCycles.mapQ goodEdges Cycles.subtype (by
    rintro _ ⟨c,rfl⟩
    exact ⟨c.val,rfl⟩)

/-- The actual incidence boundary descends to the relative vertex quotient. -/
def relativeBoundary : R₁ →ₗ[ℚ] R₀ :=
  goodEdges.mapQ goodVertices boundary (by
    rintro _ ⟨c,rfl⟩
    exact ⟨GoodChainComplex.boundary c,(boundary_inclusion c).symm⟩)

@[simp] theorem cycleToEdge_mk (c : Cycles) :
    cycleToEdge (Submodule.Quotient.mk c) = Submodule.Quotient.mk c.val := rfl
@[simp] theorem relativeBoundary_mk (c : EdgeChains) :
    relativeBoundary (Submodule.Quotient.mk c) = Submodule.Quotient.mk (boundary c) := rfl

/-- No new relation among ordinary cycles is introduced by quotienting by Good edges. -/
theorem cycleToEdge_injective : Function.Injective cycleToEdge := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x
  refine Submodule.Quotient.induction_on goodCycles x ?_
  intro c hc
  have hm : c.val ∈ goodEdges := (Submodule.Quotient.mk_eq_zero goodEdges).mp hc
  obtain ⟨a,ha⟩ := hm
  have hd : GoodChainComplex.boundary a = 0 := by
    apply vertexInclusion_injective
    rw [map_zero,← boundary_inclusion,ha]
    exact c.property
  apply (Submodule.Quotient.mk_eq_zero goodCycles).mpr
  exact ⟨⟨a,hd⟩,Subtype.ext ha⟩

/-- The generic incidence chain graph of the actual Good building is connected. -/
theorem good_preconnected :
    (BipartitePathChains.graph GoodChainComplex.incidence).Preconnected := by
  intro u v
  exact ((GoodBuilding.path u v).val.map GoodChainComplex.incidenceGraphIso.toHom).reachable

/-- A Good vertex chain with zero total coefficient bounds an actual finite Good edge chain. -/
theorem good_zero_augmentation_filling (c : GoodChainComplex.VertexChains)
    (hc : augmentation c = 0) : ∃ a, GoodChainComplex.boundary a = c :=
  zero_augmentation_filling GoodChainComplex.incidence good_preconnected GoodBuilding.baseVertex c hc

/-- The image of the cycle quotient is exactly the relative boundary kernel. -/
theorem range_cycleToEdge : cycleToEdge.range = relativeBoundary.ker := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    refine Submodule.Quotient.induction_on goodCycles x ?_
    intro c
    change Submodule.Quotient.mk (boundary c.val) = (0 : R₀)
    rw [show boundary c.val = 0 from c.property]
    exact map_zero goodVertices.mkQ
  · intro x hx
    refine Submodule.Quotient.induction_on goodEdges x (fun c hc => ?_) hx
    have hm : boundary c ∈ goodVertices := (Submodule.Quotient.mk_eq_zero goodVertices).mp hc
    obtain ⟨v,hv⟩ := hm
    have haug : augmentation v = 0 := by
      rw [← augmentation_inclusion,hv]
      exact augmentation_boundary OrdinaryIncidence.incidence c
    obtain ⟨a,ha⟩ := good_zero_augmentation_filling v haug
    let z : Cycles := ⟨c-edgeInclusion a,by
      change boundary (c-edgeInclusion a) = 0
      rw [map_sub,boundary_inclusion,ha,hv,sub_self]⟩
    refine ⟨Submodule.Quotient.mk z,?_⟩
    change goodEdges.mkQ (c-edgeInclusion a) = goodEdges.mkQ c
    rw [map_sub,show goodEdges.mkQ (edgeInclusion a) = 0 from
      (Submodule.Quotient.mk_eq_zero goodEdges).mpr ⟨a,rfl⟩,sub_zero]

/-- Every relative vertex chain bounds: the ordinary path's base vertex is already Good. -/
theorem relativeBoundary_surjective : Function.Surjective relativeBoundary := by
  intro x
  refine Submodule.Quotient.induction_on goodVertices x ?_
  intro v
  let base := OrdinaryIncidence.goodVertex GoodBuilding.baseVertex
  let p := pathLift OrdinaryIncidence.incidence OrdinaryIncidence.connected.preconnected base v
  refine ⟨Submodule.Quotient.mk p,?_⟩
  change goodVertices.mkQ (boundary p) = goodVertices.mkQ v
  rw [boundary_pathLift,map_sub,map_smul]
  have hb : goodVertices.mkQ (Finsupp.single base 1) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero goodVertices).mpr
    exact ⟨Finsupp.single GoodBuilding.baseVertex 1,vertexInclusion_single _ _⟩
  rw [hb,smul_zero,sub_zero]

/-- The actual rational incidence graphs give the short exact relative graph sequence. -/
theorem short_exact : Function.Injective cycleToEdge ∧
    cycleToEdge.range = relativeBoundary.ker ∧ Function.Surjective relativeBoundary :=
  ⟨cycleToEdge_injective,range_cycleToEdge,relativeBoundary_surjective⟩

end TernaryPoly.OrdinaryRelativeGraph
